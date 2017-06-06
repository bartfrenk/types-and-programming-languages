{-| Implementation of the simply typed lambda calculus with boolean base type, as
presented in Chapter 9 of Types and Programming Languages. This is somewhat of a
simplication of the ML implementation presented in Chapter 10, as no information
for debugging or printing is tracked.
-}

module SimpleBool where

-- |Context with type bindings. The first element of the tuple is the name of
-- the variable, which is ignored by the type checker, as free variables are
-- lookup up by index.
type Context = [(String, Binding)]

-- |Types in simply typed lambda calculus with boolean base type.
data Ty
  = TyArr Ty Ty
  | TyBool deriving (Show, Eq)

-- |Type bindings
data Binding
  = NameBind
  | VarBind Ty

-- |Adds a binding to the context.
addBinding :: Context -> String -> Binding -> Context
addBinding ctx x bind = (x, bind):ctx

-- |Returns the i-th value in an association list.
get :: Integer -> [(a, b)] -> Maybe b
get _ [] = Nothing
get 0 ((_, x):_) = Just x
get n (_:xs) | n > 0 = get (n - 1) xs
get _ _ = Nothing

-- |Looks a variable up by index in a context
getTypeFromContext :: Context -> Integer -> Ty
getTypeFromContext ctx i =
  case get i ctx of
    Just (VarBind ty) -> ty
    _ -> error $ "no " ++ show i ++ " in the context"

type Index = Integer

-- |Terms in the simply types lambda calculus with Bool basetype.
data Term
  = TmVar Index
  | TmAbs String Ty Term
  | TmApp Term Term
  | TmTrue
  | TmFalse
  | TmIf Term Term Term

-- |Computes the type of a term in a context.
typeof :: Context -> Term -> Ty
typeof ctx (TmVar i) = getTypeFromContext ctx i
typeof ctx (TmAbs x tyVar body) =
  let ctx' = addBinding ctx x (VarBind tyVar)
      tyBody = typeof ctx' body
  in TyArr tyVar tyBody
typeof ctx (TmApp fn param) =
  let tyFn = typeof ctx fn
      tyParam = typeof ctx param
  in case tyFn of
    TyArr tyParam' tyImage ->
      if tyParam' == tyParam
      then tyImage
      else error $ "parameter type mismatch, actual " ++ show tyParam ++
                   ", expected " ++ show tyParam'
    _ -> error "arrow type expected"
typeof _ TmTrue = TyBool
typeof _ TmFalse = TyBool
typeof ctx (TmIf guard trueBranch falseBranch) =
  if typeof ctx guard == TyBool then
    let tyTrueBranch = typeof ctx trueBranch
    in if tyTrueBranch == typeof ctx falseBranch then
      tyTrueBranch
    else error "branches of conditional have different types"
  else error "guard of conditional not a boolean"

-- |Well-typed term under the context [("z", TyVar TyBool)].
wellTypedTerm :: Term
wellTypedTerm = TmIf (TmVar 0) (TmAbs "x" TyBool (TmVar 0)) (TmAbs "y" TyBool (TmVar 0))

-- |Ill-typed term under any context.
illTypedTerm :: Term
illTypedTerm = TmApp (TmAbs "x" TyBool (TmVar 0)) (TmAbs "x" TyBool (TmVar 0))
