-- Single-step evaluator for the untyped lambda calculus ("untyped").
--
-- References:
-- * Pierce, B. C. (2002). Types and Programming Languages. The MIT Press. 

import Data.Maybe

data Term
    = TmVar Int
    | TmAbs String Term
    | TmApp Term Term
    deriving Eq

instance Show Term where
    show t = aux Nothing t
      where
        aux hint t = case t of
            TmVar x     -> fromJust hint
            TmAbs x t1  -> "(\\" ++ x ++ ". " ++ (aux (Just x) t1) ++ ")"
            TmApp t1 t2 -> "(" ++ (aux hint t1) ++ " " ++ (aux hint t2) ++ ")"

data Binding = NameBind
type Context = [(String, Binding)]

-- Example naming context:
-- Γ = x -> 4
--     y -> 3
--     z -> 2
--     a -> 1
--     b -> 0

-- Suppose: s = z (\w. w) => 2 (\. 0). Then,
--          [x -> s][\y. x]
-- c = 0 => [1 -> 2 (\. 0)][\. 1]
-- c = 1 => \. 3 (\. 0)
--       => \y. z (\w. w)

termShift :: Int -> Term -> Term
termShift d t = walk 0 t
  where
    walk c t = case t of
        TmVar x     -> TmVar (if x >= c then (x + d) else x)
        TmAbs x t1  -> TmAbs x (walk (c + 1) t1)
        TmApp t1 t2 -> TmApp (walk c t1) (walk c t2)

termSubst :: Int -> Term -> Term -> Term
termSubst j s t = walk 0 t
  where
    walk c t = case t of
        TmVar x     -> if x == j + c then termShift c s else TmVar x
        TmAbs x t1  -> TmAbs x (walk (c + 1) t1)
        TmApp t1 t2 -> TmApp (walk c t1) (walk c t2)

termSubstTop :: Term -> Term -> Term
termSubstTop s t = termShift (-1) (termSubst 0 (termShift 1 s) t)

isVal :: Context -> Term -> Bool
isVal _ t = case t of
    TmAbs _ _ -> True
    _         -> False

eval1 :: Context -> Term -> Maybe Term
eval1 ctx t = case t of
    TmApp (TmAbs x t12) v2 | isVal ctx v2 ->
        Just $ termSubstTop v2 t12
    TmApp v1 t2 | isVal ctx v1 -> do
        t2' <- eval1 ctx t2
        Just $ TmApp v1 t2'
    TmApp t1 t2 -> do
        t1' <- eval1 ctx t1
        Just $ TmApp t1' t2
    _ ->
        Nothing

eval :: Context -> Term -> IO ()
eval ctx t =
    let t' = fromMaybe t $ eval1 ctx t
    in if t' == t then
           return ()
       else do
           putStrLn $ "=> " ++ show t'
           eval ctx t'
           return ()

-- Given t = (id id) (id (id (\z. id z))), where id = \x. x,
-- following the call-by-value strategy:
--
--    (id id) (id (id (\z. id z)))
--    ~~~~~~~
-- => id (id (id (\z. id z)))
--       ~~~~~~~~~~~~~~~~~~~~
-- => id (id (\z. id z))
--       ~~~~~~~~~~~~~~~
-- => id (\z. id z)
--    ~~~~~~~~~~~~~
-- => (\z. id z)
--
-- Output:
-- (((\x. x) (\x. x)) ((\y. y) ((\y. y) (\z. ((\y. y) z)))))
-- => ((\x. x) ((\y. y) ((\y. y) (\z. ((\y. y) z)))))
-- => ((\x. x) ((\y. y) (\z. ((\y. y) z))))
-- => ((\x. x) (\z. ((\y. y) z)))
-- => (\z. ((\y. y) z))
main :: IO ()
main = do
    let idx  = TmAbs "x" (TmVar 0)
    let idy  = TmAbs "y" (TmVar 0)  -- Bind different names for some ids
    let idy1 = TmAbs "y" (TmVar 1)  -- de Bruijn index 1 for the nested id
    let z    = TmVar 0
    let t    = TmApp (TmApp idx idx)
                     (TmApp idy (TmApp idy (TmAbs "z" (TmApp idy1 z))))
    putStrLn $ show t
    let ignore_ctx = []  -- No context used in this implementation.
    eval ignore_ctx t
