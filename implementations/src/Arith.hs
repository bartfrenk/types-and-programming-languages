{-| Implementation of the language of untyped arithmetic expressions as presented
in chapter 3 of Types and Programming Languages. This is mostly a translation of
the OCaml implementation in chapter 4 of the same book, except for the 'eval2'
function, which is a solution to Exercise 4.2.2.
-}
module Arith where

import Data.Maybe (isJust, fromJust)

-- |Terms in the language of untyped arithmetic expressions.
data Term
  = TmTrue
  | TmFalse
  | TmIf Term Term Term
  | TmZero
  | TmSucc Term
  | TmPred Term
  | TmIsZero Term deriving (Show, Eq)

-- |An example term ~ (if (zero? (dec (inc 0))) (inc 0) false)
term :: Term
term = TmIf (TmIsZero (TmPred (TmSucc TmZero))) (TmSucc TmZero) TmFalse

-- |True when term is a numeric value, False otherwise.
isNumericVal :: Term -> Bool
isNumericVal TmZero = True
isNumericVal (TmSucc t) = isNumericVal t
isNumericVal _ = False

-- |True when term is a value, False otherwise.
isVal :: Term -> Bool
isVal TmTrue = True
isVal TmFalse = True
isVal t = isNumericVal t

-- |Small step semantics of the language of untyped arithmetic expressions.
eval1 :: Term -> Maybe Term
eval1 (TmIf TmTrue t _) = Just t
eval1 (TmIf TmFalse _ t) = Just t
eval1 (TmIf t1 t2 t3) = (\t -> TmIf t t2 t3) <$> eval1 t1
eval1 (TmSucc t) = TmSucc <$> eval1 t
eval1 (TmPred TmZero) = Just TmZero
eval1 (TmPred (TmSucc t)) | isNumericVal t = Just t
eval1 (TmPred t) = TmPred <$> eval1 t
eval1 (TmIsZero TmZero) = Just TmTrue
eval1 (TmIsZero (TmSucc t)) | isNumericVal t = Just TmFalse
eval1 (TmIsZero t) = TmIsZero <$> eval1 t
eval1 _ = Nothing

toNormalForm :: Term -> Term
toNormalForm t = lastJust (iterate (>>= eval1) (Just t))
  where lastJust (Just x:xs) = takeLast' xs x
        lastJust _ = error ""
        takeLast' (Just z:zs) _ = takeLast' zs z
        takeLast' _ acc = acc

-- |Prints single steps of a reduction to normal form.
printReductions :: Term -> IO ()
printReductions t =
  (print . fromJust) `mapM_` takeWhile isJust (iterate (>>= eval1) (Just t))

-- |Big step semantics of the language of untyped arithmetic expressions.
eval2 :: Term -> Maybe Term
eval2 (TmIf t1 t2 _) | eval2 t1 == Just TmTrue
  = eval2 t2
eval2 (TmIf t1 _ t3) | eval2 t1 == Just TmFalse
  = eval2 t3
eval2 (TmSucc t) | (isNumericVal <$> eval2 t) == Just True
  = TmSucc <$> eval2 t
eval2 (TmPred t) | eval2 t == Just TmZero
  = Just TmZero
eval2 (TmPred t) =
  case eval2 t of
    Just (TmSucc t') -> if isNumericVal t' then Just t' else Nothing
    _ -> Nothing
eval2 (TmIsZero t) | eval2 t == Just TmZero = Just TmTrue
eval2 (TmIsZero t) =
  case eval2 t of
    Just (TmSucc t') -> if isNumericVal t' then Just TmFalse else Nothing
    _ -> Nothing
eval2 t = Just t
