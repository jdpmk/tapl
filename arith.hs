-- Single-step evaluator based on small-step semantics for untyped arithmetic
-- expressions ("arith").
--
-- References:
-- * Pierce, B. C. (2002). Types and Programming Languages. The MIT Press. 

import Data.Maybe

data Term
    = TmTrue
    | TmFalse
    | TmIf Term Term Term
    | TmZero
    | TmSucc Term
    | TmPred Term
    | TmIsZero Term
    deriving (Show, Eq)

isNumericVal :: Term -> Bool
isNumericVal TmZero     = True
isNumericVal (TmSucc t) = isNumericVal t
isNumericVal _          = False

eval1 :: Term -> Maybe Term
eval1 (TmIf TmTrue t2 _) = Just t2
eval1 (TmIf TmFalse _ t3) = Just t3
eval1 (TmIf t1 t2 t3) = do
    t1' <- eval1 t1
    Just $ TmIf t1' t2 t3
eval1 (TmSucc t) = do
    t' <- eval1 t
    Just $ TmSucc t'
eval1 (TmPred TmZero) = Just TmZero
eval1 (TmPred (TmSucc v)) | isNumericVal v = Just v
eval1 (TmPred t) = do
    t' <- eval1 t
    Just $ TmPred t'
eval1 (TmIsZero TmZero) = Just TmTrue
eval1 (TmIsZero (TmSucc v)) | isNumericVal v = Just TmFalse
eval1 (TmIsZero t) = do
    t' <- eval1 t
    Just $ TmIsZero t'
eval1 _ = Nothing

eval :: Term -> IO ()
eval t =
    let t' = fromMaybe t $ eval1 t
    in if t' == t then
           return ()
       else do
           putStrLn $ "=> " ++ show t'
           eval t'
           return ()

-- Output:
-- TmIf (TmIf TmTrue TmFalse TmTrue) TmZero (TmSucc TmZero)
-- => TmIf TmFalse TmZero (TmSucc TmZero)
-- => TmSucc TmZero
main :: IO ()
main = do
    let t = TmIf (TmIf TmTrue TmFalse TmTrue) TmZero (TmSucc TmZero)
    putStrLn $ show t
    eval t
