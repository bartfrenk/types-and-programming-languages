{-|Implementation of the pure untyped lambda calculus, as presented in Chapter 7
 of Types and Programming Languages. This is somewhat of a simplication of the
 ML implementation presented in Chapter 7, as no information for debugging or
 printing is tracked.
-}
module Untyped where

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
isVal _ = False

-- |Small step evaluation of terms in the pure untyped lambda calculus.
-- Call-by-value semantics?
eval1 :: Term -> Term
eval1 (TmApp (TmAbs t) v)
  | isVal v = termSubstTop v t
eval1 (TmApp v t)
  | isVal v = TmApp v (eval1 t)
eval1 (TmApp t1 t2) = TmApp (eval1 t1) t2
--eval1 (TmAbs t) = TmAbs (eval1 t)
eval1 _ = error "NoRuleApplies"


c0 :: Term
c0 = TmAbs $ TmAbs $ TmVar 0

scc :: Term
scc = TmAbs $ TmAbs $ TmAbs $ TmApp (TmVar 1)
  (TmApp (TmApp (TmVar 2) (TmVar 1)) (TmVar 0))

-- TODO: can we evaluate c1 to normal form?
c1 :: Term
c1 = eval1 (TmApp scc c0)

