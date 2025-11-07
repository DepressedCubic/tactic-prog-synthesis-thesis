module AST where

import Data.Maybe
import qualified Data.Map as MP

import qualified Data.Set as ST

{-
Three useful pieces:
- Zippers *
- Stateful computation (monads) *
- Type variable classification
-}

data TypeVar =
  RigidVar String | -- Rigid Skolem variable; it cannot be anything other than what it is.
  FlexVar String -- Flexible undetermined variable
  deriving (Eq, Ord)

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
fv :: Type -> ST.Set TypeVar
fv t =
  case t of
    List t' -> fv t'
    Function t1 t2 -> fv t1 `ST.union` fv t2
    Product t1 t2 -> fv t1 `ST.union` fv t2
    Union t1 t2 -> fv t1 `ST.union` fv t2
    TVar (FlexVar t1) -> ST.singleton (FlexVar t1)
    _ -> ST.empty

{-
To aid the structural analysis of compound types
(i.e. types that are neither primitive nor flexible) 
we define auxiliary datatypes, encoding the topmost
type constructor and the sub-types.
-}

data TypeConstructor =
  LIST | FUNC | PROD | UNION
  deriving (Eq)

data CompoundType = Compound {
  constructor :: TypeConstructor,
  subtypes :: [Type]
}

instance Eq CompoundType where
  c1 == c2 = (constructor c1 == constructor c2) && (length (subtypes c1) == length (subtypes c2))

{-
If primitive or flexible, returns Nothing;
otherwise, returns the topmost type constructor
and sub-types.
-}
compoundType :: Type -> Maybe CompoundType
compoundType t =
  case t of
    List t' -> Just (Compound LIST [t'])
    Function t1 t2 -> Just (Compound FUNC [t1, t2])
    Product t1 t2 -> Just (Compound PROD [t1, t2])
    Union t1 t2 -> Just (Compound UNION [t1, t2])
    _ -> Nothing


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
      TVar t1 -> show t1


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
applyText (x : xs) = x ++ " " ++ applyText xs

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
      App -> applyText $ map show subExps
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
      Program -> unlines $ map show subExps

data PathChoice = PathChoice {
  leftSiblings :: [Expression],
  parentData :: ExpressionData,
  rightSiblings :: [Expression]
}
type Location = [PathChoice]

data ExprZipper = Zipper Expression Location

-- Just one zipper that moves from one hole to the other.



-- Let's begin by assuming no type polymorphism.

type Context = MP.Map String Type
type Substitution = MP.Map TypeVar Type
type ConstraintSet = [(Type, Type)]

emptySubstitution :: Substitution
emptySubstitution = MP.empty

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
      TVar (FlexVar s) -> fromMaybe t $ MP.lookup (FlexVar s) sub
      _ -> t

substituteCtxt :: Substitution -> Context -> Context
substituteCtxt sub = MP.map (substitute sub)

-- Substitution of constraints
(-*>) :: Substitution -> ConstraintSet -> ConstraintSet
sub -*> constraint = map (\(t1, t2) -> (substitute sub t1, substitute sub t2)) constraint

-- Extracts a flexible type variable from
-- a type exactly when the type is this
-- flexible type variable.
extractFlexible :: Type -> Maybe TypeVar
extractFlexible (TVar (FlexVar t)) = Just (FlexVar t)
extractFlexible _ = Nothing

-- Singleton substitution
(|->) :: TypeVar -> Type -> Substitution
x |-> t = MP.singleton x t


-- Composition of substitutions
(-*-) :: Substitution -> Substitution -> Substitution
s1 -*- s2 =
  let
    s2' = MP.map (substitute s1) s2
    s1' = MP.filterWithKey (\k _ -> not $ k `MP.member` s2) s1
  in 
    MP.union s1' s2'

{- Take two compound types and create constraints for each sub-type,
unless the type constructors or the number of sub-type are not the same.
-}
zipConstraints :: CompoundType -> CompoundType -> Maybe ConstraintSet
zipConstraints struct1 struct2 =
  if struct1 == struct2
    then
      Just $ zip (subtypes struct1) (subtypes struct2)
    else 
      Nothing

unify :: ConstraintSet -> Maybe Substitution
unify c =
  case c of
    -- The empty substitution unifies the empty constraint.
    [] -> Just emptySubstitution
    (t1, t2) : cs ->
      if t1 == t2 then unify cs -- Structural equality can be dropped.
      else
        case (extractFlexible t1, extractFlexible t2) of
          (Just t1', _) ->
            if t1' `ST.member` fv t2
              then Nothing
              else do
                u1 <- unify ((t1' |-> t2) -*> cs)
                return (u1 -*- (t1' |-> t2))
          (_, Just t2') ->
            if t2' `ST.member` fv t1
              then Nothing
              else do
                u2 <- unify ((t2' |-> t1) -*> cs)
                return (u2 -*- (t2' |-> t1))
          (Nothing, Nothing) -> -- Whenever neither are flexible nor structurally equal.
            do
              struct1 <- compoundType t1
              struct2 <- compoundType t2
              zipped <- zipConstraints struct1 struct2
              unify $ zipped ++ cs


