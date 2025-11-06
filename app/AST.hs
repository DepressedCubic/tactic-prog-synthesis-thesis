module AST where

import Data.Map (Map)
import qualified Data.Map as Map

{-
Three useful pieces:
- Zippers *
- Stateful computation (monads) *
- Type variable classification
-}

data TypeVar =
  RigidVar String | -- Rigid Skolem variable; it cannot be anything other than what it is.
  FlexVar String -- Flexible undetermined variable
  deriving (Eq)

-- Helper function to get fresh unification variable names.
{-
getNext :: State Int String
getNext = do
  nextId <- get
  put (nextId + 1)
  return ("T" ++ (show nextId))
-}



instance Show TypeVar where
  show tv =
    case tv of
      RigidVar s -> s
      FlexVar s -> s

data Type =
  Int |
  String |
  Boolean |
  List Type |
  Function Type Type |
  Product Type Type |
  Union Type Type |
  TVar TypeVar
  deriving (Eq)

-- Given a type, finds all flexible variables occurring in it.
fv :: Type -> Set TypeVar
fv t =
  case t of
    List t' -> fv t'
    Function t1 t2 -> union (fv t1) (fv t2)
    Product t1 t2 -> union (fv t1) (fv t2)
    Union t1 t2 -> union (fv t1) (fv t2)
    TVar (FlexVar _) -> singleton t
    _ -> empty

{-
To aid the structural analysis of compound types
(i.e. types that are neither primitive nor flexible) 
we define auxiliary datatypes, encoding the topmost
type constructor and the sub-branches.
-}

data TypeConstructor =
  LIST | FUNC | PROD | UNION

data CompoundType = Compound {
  constructor :: TypeConstructor,
  subtypes :: [Type]
}

{-
If primitive or flexible, returns Nothing;
otherwise, returns the topmost type constructor
and sub-branches.
-}
compoundType :: Type -> Maybe TypeConstructor 
compoundType t =
  case t of
    List t' -> Just (Compound LIST [t'])
    Function t1 t2 -> Just (Compound FUNC [t1, t2])
    Product t1 t2 -> Just (Compound PROD [t1, t2])
    Union t1 t2 -> Just (Compound UNION [t1, t2])


{-
Determines whether a type is primitive: that is,
to attempt unification with it, it suffices to check
for structural equality.
-}
isPrimitive :: Type -> Bool
isPrimitive t =
  case t of
    Int -> True
    String -> True
    Boolean -> True
    TVar (RigidVar _) -> True
    _ -> False


instance Show Type where
  show t =
    case t of
      Int -> "ℤ"
      String -> "String"
      Boolean -> "Bool"
      List t1 -> "[" ++ show t1 ++ "]"
      Function t1 t2 -> show t1 ++ " → " ++ show t2
      Product t1 t2 -> show t1 ++ " × " ++ show t2
      Union t1 t2 -> show t1 ++ " ⊔ " ++ show t2


{-
Zipper-friendly data type for expressions,
inspired by Huet's original paper.
-}

-- Indents the whole representation by one tab.
tab :: String -> String
tab s = unlines $ map ("  " ++) $ lines s

-- Takes a list of strings s1, s2, ... and writes them in
-- 'application notation': (s1) (s2) ...
applyText :: [String] -> String
applyText [] = ""
applyText [x] = "(" ++ x ++ ")"
applyText (x : xs) = x ++ " " ++ (applyText xs)

data ExpressionData =
  App |
  Var String |
  Ifte |
  Lambda String Type |
  Pair |
  Num Integer |
  Bool Bool |
  IDHole Int Type |
  Let String Type |
  LetRec String Type |
  Program

data Expression = Expr ExpressionData [Expression]

-- Consider zipper-based pretty printing to make this
instance Show Expression where
  show (Expr exprData subExps) =
    case exprData of
      App -> applyText $ Prelude.map show subExps
      Bool b -> show b
      Num n -> show n
      Var s -> s
      Ifte ->
        "if (" ++ show (subExps !! 0) ++ ")\n" ++
        tab ( "then (" ++ show (subExps !! 1) ++ ")\n")
        ++ "else (" ++ show (subExps !! 2) ++ ")"
      Lambda s t ->
        "λ(" ++ s ++ " : " ++ show t ++ ") ↦ \n"
        ++ (tab $ show (subExps !! 0))
      Pair ->
        "(" ++ show (subExps !! 0) ++ ", " ++ show (subExps !! 1) ++ ")"
      IDHole id t ->
        "(__#" ++ show id ++ " : " ++ show t ++ ")"
      Let s t -> "let (" ++ s ++ " : " ++ show t ++ ") =\n" ++ (tab $ show (subExps !! 0)) ++ "\n"
      LetRec s t -> "letrec (" ++ s ++ " : " ++ show t ++ ") =\n" ++ (tab $ show (subExps !! 0)) ++ "\n"
      Program -> unlines $ Prelude.map show subExps

data PathChoice = PathChoice {
  leftSiblings :: [Expression],
  parentData :: ExpressionData,
  rightSiblings :: [Expression]
}
type Location = [PathChoice]

data ExprZipper = Zipper Expression Location

-- Just one zipper that moves from one hole to the other.



-- Let's begin by assuming no type polymorphism.

type Context = Map String Type
type Substitution = Map TypeVar Type
type ConstraintSet = [(TypeVar, Type)]

emptySubstitution :: Substitution
emptySubstitution = Map.empty

emptyConstraint :: ConstraintSet
emptyConstraint = []

-- any mention of rigid variables are ignored if they appear.

substitute :: Substitution -> Type -> Type
substitute sub t =
    case t of
      List t' -> List (substitute sub t')
      Function t1 t2 -> Function (substitute sub t1) (substitute sub t2)
      Product t1 t2 -> Product (substitute sub t1) (substitute sub t2)
      Union t1 t2 -> Union (substitute sub t1) (substitute sub t2)
      TVar (FlexVar s) -> fromMaybe t Map.lookup (FlexVar s) sub
      _ -> t

substituteCtxt :: Substitution -> Context -> Context
substituteCtxt sub = Map.map (substitute sub)

-- Extracts a flexible type variable from
-- a type exactly when the type is this
-- flexible type variable.
extractFlexible :: Type -> Maybe TypeVar
extractFlexible (TVar (FlexVar t)) = Just (FlexVar t)
extractFlexible _ = Nothing

-- singleton substitution
(|->) :: TypeVar -> Type -> Substitution
x |-> t = singleton x t


-- composition of substitutions
(*) :: Substitution -> Substitution -> Substitution
s1 * s2 =
  let
    s2' = map (substitute s1) s2
    s1' = filterWithKey (\k _ -> not $ k `member` s2) s1
  in 
    union s1' s2'

{-
unify :: ConstraintSet -> Maybe Substitution
unify c =
  case c of
    [] -> Just emptySubstitution
    (s, t) : c' ->
      if s == t then unify cs'
      else 
        let
          s' = extractFlexible s
          t' = extractFlexible t
        in
          if isJust s' && not $ (fromJust s') `member` (fv t)
            then do
              r1 <- unify (((fromJust s') |-> t) * c')
              return ( r1 * ((fromJust s') |-> t) )
          else if isJust t' && not $ (fromJust t') `member` (fv s)
            then do
              r2 <- unify (((fromJust t') |-> s) * c')
              return ( r2 * ((fromJust t') |-> s) )
          else
            case

-}
