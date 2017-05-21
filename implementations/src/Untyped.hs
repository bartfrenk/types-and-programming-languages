{-|Implementation of the pure untyped lambda calculus, as presented in Chapter 7
 of Types and Programming Languages. This is somewhat of a simplication of the
 ML implementation presented in Chapter 7, as no information for debugging or
 printing is tracked.
-}
module Untyped where

import Data.Maybe

type Index = Int

-- |Representation of terms in the pure untyped lambda calculus.
data Term
  -- first index is the De Bruijn index of the variable
  = TmVar Index
  | TmAbs Term
  | TmApp Term Term deriving Show

-- |Shifts the De Bruijn indices of all free variables up by `d`.
termShift :: Index -> Term -> Term
termShift d = walk 0
  where walk c (TmVar x) =
          if x >= c then TmVar (x + d)
          else TmVar x
        walk c (TmAbs t) = TmAbs $ walk (c + 1) t
        walk c (TmApp t1 t2) = TmApp (walk c t1) (walk c t2)

-- |Substitutes `s` for `j` in `t`.
termSubst :: Index -> Term -> Term -> Term
termSubst j s t@(TmVar k) = if k == j then s else t
termSubst j s (TmAbs t) = TmAbs (termSubst (j + 1) (termShift 1 s) t)
termSubst j s (TmApp t1 t2) = TmApp (termSubst j s t1) (termSubst j s t2)

-- |Substitution operation used to define evaluation of application.
termSubstTop :: Term -> Term -> Term
termSubstTop s t =
  termShift (-1) (termSubst 0 (termShift 1 s) t)

-- |Predicate for values.
isVal :: Term -> Bool
isVal (TmAbs _) = True
isVal (TmVar _) = True
isVal _ = False

isNormal :: Term -> Bool
isNormal (TmApp (TmAbs _) _) = False
isNormal _ = True

-- |Strict small step evaluation of terms in the pure untyped lambda calculus.
eval1 :: Term -> Term
eval1 (TmApp (TmAbs t) v)
  | isVal v = termSubstTop v t
eval1 (TmApp v t)
  | isVal v = TmApp v (eval1 t)
eval1 (TmApp t1 t2) = TmApp (eval1 t1) t2
eval1 _ = error "NoRuleApplies"

-- |Strict small step evaluation; evaluate abstraction body.
evalMaybe :: Term -> Maybe Term
evalMaybe (TmApp (TmAbs t) v)
  | isNormal v = Just $ termSubstTop v t
evalMaybe (TmApp v t)
  | isNormal v = TmApp v <$> evalMaybe t
evalMaybe (TmApp t1 t2) = flip TmApp t2 <$> evalMaybe t1
evalMaybe (TmAbs t) = TmAbs <$> evalMaybe t
evalMaybe _ = Nothing

-- |Prints single steps of a reduction to normal form.
printReductions :: Term -> IO ()
printReductions t =
  (print . fromJust) `mapM_` takeWhile isJust (iterate (>>= evalMaybe) (Just t))

-- |Small step reduction to normal form.
toNormalForm :: Term -> Term
toNormalForm t = lastJust (iterate (>>= evalMaybe) (Just t))
  where lastJust (Just x:xs) = takeLast' xs x
        lastJust _ = error ""
        takeLast' (Just z:zs) _ = takeLast' zs z
        takeLast' _ acc = acc

-- |Church numeral: 0
c0 :: Term
c0 = TmAbs $ TmAbs $ TmVar 0

-- |Church numerals (using a Haskell list is cheating of course)
churchNumerals :: [Term]
churchNumerals = iterate (TmApp scc) c0

-- |Church boolean: True
tru :: Term
tru = TmAbs $ TmAbs $ TmVar 1

-- |Church boolean: False
fls :: Term
fls = TmAbs $ TmAbs $ TmVar 0

-- |Logical conjunction on Church booleans
tmAnd :: Term
tmAnd = TmAbs $ TmAbs $ TmApp (TmApp (TmVar 1) (TmVar 0)) fls

-- |Successor function on Church numerals
scc :: Term
scc = TmAbs $ TmAbs $ TmAbs $ TmApp (TmVar 1)
  (TmApp (TmApp (TmVar 2) (TmVar 1)) (TmVar 0))

-- |Addition of Church numerals
plus :: Term
plus = TmAbs $ TmAbs $ TmAbs $ TmAbs $
  TmApp (TmApp (TmVar 3) (TmVar 1))
        (TmApp (TmApp (TmVar 2) (TmVar 1)) (TmVar 0))

-- |Multiplication of Church numerals
times :: Term
times = TmAbs $ TmAbs $ TmAbs $
  TmApp (TmVar 2) (TmApp (TmVar 1) (TmVar 0))

-- |Evaluates to `tru` if applied to `c0`, to `fls` on any other Church numeral.
iszro :: Term
iszro = TmAbs (TmApp (TmApp (TmVar 0) (TmAbs fls)) tru)

-- |Encode a pair of terms by applying pair to them.
pair :: Term
pair = TmAbs $ TmAbs $ TmAbs $ TmApp (TmApp (TmVar 0) (TmVar 2)) (TmVar 1)

-- |Evaluates to the first element when applied to a pair.
tmFst :: Term
tmFst = TmAbs (TmApp tru (TmVar 0))

-- |Evaluates to the second element when applied to a pair.
tmSnd :: Term
tmSnd = TmAbs (TmApp fls (TmVar 0))

-- Would expect this to evaluate to `tru`, but doesn't
testCase :: Term
testCase = toNormalForm $ TmApp tmFst (TmApp (TmApp pair tru) fls)
