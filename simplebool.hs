-- Implementation of the simply-typed lambda calculus ("simplebool").
--
-- References:
-- * Pierce, B. C. (2002). Types and Programming Languages. The MIT Press. 

import Data.Maybe

data Type
    = TyBool
    | TyArr Type Type
    deriving Eq

instance Show Type where
    show TyBool          = "Bool"
    show (TyArr ty1 ty2) = show ty1 ++ " -> " ++ show ty2

data Term
    = TmTrue
    | TmFalse
    | TmIf Term Term Term
    | TmVar Int
    | TmAbs String Type Term
    | TmApp Term Term
    deriving Eq

instance Show Term where
    show t = aux Nothing t
      where
        aux hint t = case t of
            TmTrue ->
                "true"
            TmFalse ->
                "false"
            TmIf t1 t2 t3 ->
                "if " ++ show t1 ++ " then " ++ show t2 ++ " else " ++ show t3
            TmVar x ->
                fromJust hint
            TmAbs x ty t1 ->
                let body = (aux (Just x) t1)
                in "(\\" ++ x ++ " : " ++ show ty ++ ". " ++ body ++ ")"
            TmApp t1 t2 ->
                "(" ++ (aux hint t1) ++ " " ++ (aux hint t2) ++ ")"

data Binding
    = NameBind
    | VarBind Type

type Context = [(String, Binding)]

addBinding :: Context -> String -> Binding -> Context
addBinding ctx x bind = (x, bind):ctx

getBinding :: Context -> String -> Either String Binding
getBinding [] x          = Left $ "no binding for " ++ x
getBinding ((v, b):bs) x = if v == x then Right b else getBinding bs x

safeIndex :: [a] -> Int -> String -> Either String a
safeIndex []     i msg = Left msg
safeIndex (x:_)  0 msg = Right x
safeIndex (_:xs) i msg = safeIndex xs (i - 1) msg

termShift :: Int -> Term -> Term
termShift d t = walk 0 t
  where
    walk c t = case t of
        TmTrue        -> TmTrue
        TmFalse       -> TmTrue
        TmIf t1 t2 t3 -> TmIf t1 t2 t3
        TmVar x       -> TmVar (if x >= c then (x + d) else x)
        TmAbs x ty t1 -> TmAbs x ty (walk (c + 1) t1)
        TmApp t1 t2   -> TmApp (walk c t1) (walk c t2)

termSubst :: Int -> Term -> Term -> Term
termSubst j s t = walk 0 t
  where
    walk c t = case t of
        TmVar x       -> if x == j + c then termShift c s else TmVar x
        TmAbs x ty t1 -> TmAbs x ty (walk (c + 1) t1)
        TmApp t1 t2   -> TmApp (walk c t1) (walk c t2)

termSubstTop :: Term -> Term -> Term
termSubstTop s t = termShift (-1) (termSubst 0 (termShift 1 s) t)

isVal :: Context -> Term -> Bool
isVal _ t = case t of
    TmTrue      -> True
    TmFalse     -> True
    TmAbs _ _ _ -> True
    _           -> False

typeOf :: Context -> Term -> Either String Type
typeOf ctx t = case t of
    TmTrue ->
        Right TyBool
    TmFalse ->
        Right TyBool
    TmIf t1 t2 t3 -> do
        ty1 <- typeOf ctx t1
        if ty1 /= TyBool then
            Left $
                "conditional guard has type:\n" ++
                "  " ++ show ty1 ++ "\n" ++
                "but expected type:\n" ++
                "  " ++ show TyBool
        else do
            ty2 <- typeOf ctx t2
            ty3 <- typeOf ctx t3
            if ty2 /= ty3 then
                Left $
                    "conditional branches have different types:\n" ++
                    "  " ++ show ty2 ++ "\n" ++
                    "and\n" ++
                    "  " ++ show ty3
            else 
                Right ty2
    TmVar i -> do
        let err = "no binding for variable"
        (_, b) <- safeIndex ctx i err
        case b of
            VarBind ty -> Right ty
            _          -> Left err
    TmAbs x ty1 t2 -> do
        let ctx' = addBinding ctx x (VarBind ty1)
        ty2 <- typeOf ctx' t2
        Right $ TyArr ty1 ty2
    TmApp t1 t2 -> do
        ty1 <- typeOf ctx t1
        ty2 <- typeOf ctx t2
        case ty1 of
            TyArr ty11 ty12 ->
                if ty2 == ty11 then
                    Right ty12
                else
                    Left $
                        "parameter type mismatch:\n" ++
                        "  cannot apply term of type:\n" ++
                        "    " ++ show ty2 ++ "\n" ++
                        "  to parameter of type:\n" ++
                        "    " ++ show ty11
            _ -> Left $
                    "cannot apply to term of type:\n" ++
                    "  " ++ show ty1 ++ "\n" ++
                    "arrow type expected"

eval1 :: Context -> Term -> Maybe Term
eval1 ctx t = case t of
    TmApp (TmAbs x _ t12) v2 | isVal ctx v2 ->
        Just $ termSubstTop v2 t12
    TmApp v1 t2 | isVal ctx v1 -> do
        t2' <- eval1 ctx t2
        Just $ TmApp v1 t2'
    TmApp t1 t2 -> do
        t1' <- eval1 ctx t1
        Just $ TmApp t1' t2
    TmIf TmTrue t2 _ ->
        Just t2
    TmIf TmFalse _ t3 ->
        Just t3
    TmIf t1 t2 t3 -> do
        t1' <- eval1 ctx t1
        Just $ TmIf t1' t2 t3
    _ ->
        Nothing

eval :: Term -> IO ()
eval t = do
    putStrLn $ show t
    aux [] t
    where
      aux ctx t =
          let t' = fromMaybe t $ eval1 ctx t
          in if t' == t then
                 return ()
             else do
                 putStrLn $ "=> " ++ show t'
                 aux ctx t'
                 return ()

typeCheckAndEval :: Term -> IO ()
typeCheckAndEval t = do
    separator
    putStrLn $ show t
    case typeOf [] t of
        Left err ->
            putStrLn err
        Right ty -> do
            putStrLn $ show t ++ " : " ++ show ty
            eval t
    separator
    putStrLn "\n"
      where
        separator = putStrLn $ replicate 72 '-'

main :: IO ()
main = do
    -- true
    -- true : Bool
    -- true
    let simple_bool = TmTrue
    typeCheckAndEval simple_bool

    -- (\x : Bool. x)
    -- (\x : Bool. x) : Bool -> Bool
    -- (\x : Bool. x)
    let id = TmAbs "x" TyBool (TmVar 0)
    typeCheckAndEval id

    -- ((\x : Bool. x) true)
    -- ((\x : Bool. x) true) : Bool
    -- ((\x : Bool. x) true)
    -- => true
    let app_id = TmApp id TmTrue
    typeCheckAndEval app_id

    -- (\x : Bool -> Bool. (x true))
    -- (\x : Bool -> Bool. (x true)) : Bool -> Bool -> Bool
    -- (\x : Bool -> Bool. (x true))
    let arrow = TmAbs "x" (TyArr TyBool TyBool) (TmApp (TmVar 0) (TmTrue))
    typeCheckAndEval arrow

    -- (\x : Bool -> Bool. (x x))
    -- parameter type mismatch:
    --   cannot apply term of type:
    --     Bool -> Bool
    --   to parameter of type:
    --     Bool
    let bad_operand = TmAbs "x"
                            (TyArr TyBool TyBool)
                            (TmApp (TmVar 0) (TmVar 0))
    typeCheckAndEval bad_operand

    -- (true false)
    -- cannot apply to term of type:
    --   Bool
    -- arrow type expected
    let bad_operator = TmApp TmTrue TmFalse
    typeCheckAndEval bad_operator

    -- if true then true else false
    -- if true then true else false : Bool
    -- if true then true else false
    -- => true
    let simple_if = TmIf TmTrue TmTrue TmFalse
    typeCheckAndEval simple_if

    -- if (\x : Bool. x) then true else false
    -- conditional guard has type:
    --   Bool -> Bool
    -- but expected type:
    --   Bool
    let id = TmAbs "x" TyBool (TmVar 0)
    let bad_guard = TmIf id TmTrue TmFalse
    typeCheckAndEval bad_guard

    -- if true then (\x : Bool. x) else false
    -- conditional branches have different types:
    --   Bool -> Bool
    -- and
    --   Bool
    let id = TmAbs "x" TyBool (TmVar 0)
    let bad_branches = TmIf TmTrue id TmFalse
    typeCheckAndEval bad_branches

    -- if ((\x : Bool. x) true) then ((\x : Bool. x) false) else true
    -- if ((\x : Bool. x) true) then ((\x : Bool. x) false) else true : Bool
    -- if ((\x : Bool. x) true) then ((\x : Bool. x) false) else true
    -- => if true then ((\x : Bool. x) false) else true
    -- => ((\x : Bool. x) false)
    -- => true
    let complex_if = TmIf (TmApp id TmTrue) (TmApp id TmFalse) TmTrue
    typeCheckAndEval complex_if
