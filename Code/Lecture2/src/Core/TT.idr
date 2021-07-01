module Core.TT

import Data.List
import Decidable.Equality

-- In Idris2, this is defined in Core.Name
public export
data Name : Type where
     UN : String -> Name -- user written name
     MN : String -> Int -> Name -- machine generated name

export
nameEq : (x : Name) -> (y : Name) -> Maybe (x = y)
nameEq (UN x) (UN y) with (decEq x y)
  nameEq (UN y) (UN y) | (Yes Refl) = Just Refl
  nameEq (UN x) (UN y) | (No contra) = Nothing
nameEq (MN x t) (MN x' t') with (decEq x x')
  nameEq (MN x t) (MN x t') | (Yes Refl) with (decEq t t')
    nameEq (MN x t) (MN x t) | (Yes Refl) | (Yes Refl) = Just Refl
    nameEq (MN x t) (MN x t') | (Yes Refl) | (No contra) = Nothing
  nameEq (MN x t) (MN x' t') | (No contra) = Nothing
nameEq _ _ = Nothing

export
Eq Name where
  (==) (UN x) (UN y) = x == y
  (==) (MN x i) (MN y j) = i == j && x == y
  (==) _ _ = False

nameTag : Name -> Int
nameTag (UN _) = 0
nameTag (MN _ _) = 1

export
Ord Name where
  compare (UN x) (UN y) = compare x y
  compare (MN x i) (MN y j)
      = case compare x y of
             EQ => compare i j
             t => t
  compare x y = compare (nameTag x) (nameTag y)

public export
data NameType : Type where
     Func : NameType
     Bound : NameType
     DataCon : (tag : Int) -> (arity : Nat) -> NameType
     TyCon : (tag : Int) -> (arity : Nat) -> NameType

export
Show NameType where
  show Func = "Func"
  show (DataCon t a) = "DataCon " ++ show (t, a)
  show (TyCon t a) = "TyCon " ++ show (t, a)
  show Bound = "Bound"

public export
data IsVar : Name -> Nat -> List Name -> Type where
     First : IsVar n Z (n :: ns)
     Later : IsVar n i ns -> IsVar n (S i) (m :: ns)

public export
dropVar : (ns : List Name) -> {idx : Nat} ->
          (0 p : IsVar name idx ns) -> List Name
dropVar (_ :: ns) {idx = 0} First = ns
dropVar (_ :: ns) {idx = (S k)} (Later p) = dropVar ns p

public export
data Var : List Name -> Type where
     MkVar : {i : Nat} -> (0 p : IsVar n i vars) -> Var vars

weakenVar :  (outer : List Name)
          -> Var (outer ++ inner)
          -> Var (outer ++ n :: inner)
weakenVar [] (MkVar p) = MkVar (Later p)
weakenVar (x :: xs) (MkVar {i = 0} First) = MkVar First
weakenVar (x :: xs) (MkVar {i = (S k)} (Later p)) =
  let MkVar p2 = weakenVar xs (MkVar p) in MkVar (Later p2)

contractVar :  (outer : List Name)
            -> Var (outer ++ v :: inner)
            -> Maybe $ Var (outer ++ inner)
contractVar [] (MkVar {i = 0} p)             = Nothing
contractVar [] (MkVar {i = (S k)} (Later p)) = Just $ MkVar p
contractVar (_ :: _) (MkVar {i = 0} First) = Just $ MkVar First
contractVar (y :: xs) (MkVar {i = (S k)} (Later p)) = 
  case contractVar xs (MkVar p) of
    Nothing           => Nothing
    (Just $ MkVar p2) => Just $ MkVar (Later p2)

appendNilNeutral : (as : List a) -> as ++ [] = as
appendNilNeutral [] = Refl
appendNilNeutral (x :: xs) = cong (x ::) $ appendNilNeutral xs


embedIsVar : IsVar n i ns -> IsVar n i (ns ++ more)
embedIsVar First = First
embedIsVar (Later x) = Later (embedIsVar x)

public export
data PiInfo : Type where
     Implicit : PiInfo
     Explicit : PiInfo

public export
data Binder : Type -> Type where
     Lam : PiInfo -> ty -> Binder ty
     Pi : PiInfo -> ty -> Binder ty

     PVar : ty -> Binder ty -- pattern bound variables ...
     PVTy : ty -> Binder ty -- ... and their type

export
Functor Binder where
  map func (Lam x ty) = Lam x (func ty)
  map func (Pi x ty) = Pi x (func ty)
  map func (PVar ty) = PVar (func ty)
  map func (PVTy ty) = PVTy (func ty)

export
Foldable Binder where
  foldr f acc b = ?foldrImpl

export
Traversable Binder where
  traverse f b = ?travImpl

public export
data Term : List Name -> Type where
     Local : (idx : Nat) -> -- de Bruijn index
             (0 p : IsVar name idx vars) -> -- proof that index is valid
             Term vars
     Ref : NameType -> Name -> Term vars -- a reference to a global name
     Meta : Name -> List (Term vars) -> Term vars
     Bind : (x : Name) -> -- any binder, e.g. lambda or pi
            Binder (Term vars) ->
            (scope : Term (x :: vars)) -> -- one more name in scope
            Term vars
     App : Term vars -> Term vars -> Term vars -- function application
     TType : Term vars
     Erased : Term vars

-- Term manipulation

weakenInner : {outer : _} -> Term (outer ++ inner) -> Term (outer ++ n :: inner)
weakenInner (Local idx p) =
  let MkVar {i} p2 = weakenVar outer (MkVar p) in Local i p2
weakenInner (Ref y z)     = Ref y z
weakenInner (Meta y xs)   = Meta y $ map weakenInner xs
weakenInner (Bind y z scope) =
  Bind y (map weakenInner z) (weakenInner {outer = y :: outer} scope)
weakenInner (App y z) = App (weakenInner y) (weakenInner z)
weakenInner TType  = TType
weakenInner Erased = Erased

export
weaken : Term vars -> Term (x :: vars)
weaken = weakenInner {outer = []}

-- this is just the identity function
export
embed : Term vars -> Term (vars ++ more)
embed (Local idx p) = Local idx $ embedIsVar p
embed (Ref x y) = Ref x y
embed (Meta x xs) = Meta x $ map embed xs
embed (Bind x y scope) = Bind x (map embed y) (embed scope)
embed (App x y) = App (embed x) (embed y)
embed TType = TType
embed Erased = Erased

contractInner : {outer : _}
              -> Term (outer ++ v :: inner)
              -> Maybe $ Term (outer ++ inner)
contractInner (Local idx p) =
  case contractVar outer (MkVar p) of
    Nothing              => Nothing
    (Just $ MkVar {i} x) => Just $ Local i x
contractInner (Ref x y) = Just $ Ref x y
contractInner (Meta x xs) =
  Meta x <$> traverse contractInner xs
contractInner (Bind x y scope) = do
  y2 <- traverse contractInner y
  s2 <- contractInner {outer = x :: outer} scope
  pure $ Bind x y2 s2
contractInner (App x y) = [| App (contractInner x) (contractInner y) |]
contractInner TType = Just TType
contractInner Erased = Just Erased

export
contract : Term (x :: vars) -> Maybe (Term vars)
contract = contractInner {outer = []}

export
substInner :  {outer : _}
           -> Term (outer ++ vars)
           -> Term (outer ++ x :: vars)
           -> Term (outer ++ vars)
substInner t (Local idx p) =
  case contractVar outer (MkVar p) of
    Just $ MkVar {i} x => Local i x
    Nothing            => t
substInner t (Ref z w) = Ref z w
substInner t (Meta z xs) = Meta z $ map (substInner t) xs
substInner t (Bind z w scope) =
  Bind z (map (substInner t) w)
    (substInner {outer = z :: outer} (weaken t) scope)
substInner t (App z w) = App (substInner t z) (substInner t w)
substInner t TType = TType
substInner t Erased = TType

export
subst : Term vars -> Term (x :: vars) -> Term vars

public export
data CompatibleVars : List Name -> List Name -> Type where
     CompatPre : CompatibleVars xs xs
     CompatExt : CompatibleVars xs ys -> CompatibleVars (n :: xs) (m :: ys)

export
renameVars : CompatibleVars xs ys -> Term xs -> Term ys

--- Show instances

export
getFnArgs : Term vars -> (Term vars, List (Term vars))
getFnArgs tm = getFA [] tm
  where
    getFA : List (Term vars) -> Term vars ->
            (Term vars, List (Term vars))
    getFA args (App f a) = getFA (a :: args) f
    getFA args tm = (tm, args)

export
showSep : String -> List String -> String
showSep sep [] = ""
showSep sep [x] = x
showSep sep (x :: xs) = x ++ sep ++ showSep sep xs

export
Show Name where
  show (UN n) = n
  show (MN n i) = "{" ++ n ++ ":" ++ show i ++ "}"

export
nameAt : {vars : _} ->
         (idx : Nat) -> (0 p : IsVar n idx vars) -> Name
nameAt {vars = n :: ns} Z First = n
nameAt {vars = n :: ns} (S k) (Later p) = nameAt k p

export 
{vars : _} -> Show (Term vars) where
  show tm = let (fn, args) = getFnArgs tm in showApp fn args
    where
      showApp : {vars : _} -> Term vars -> List (Term vars) -> String
      showApp (Local {name} idx p) []
         = show (nameAt idx p) ++ "[" ++ show idx ++ "]"
      showApp (Ref _ n) [] = show n
      showApp (Meta n args) []
          = "?" ++ show n ++ "_" ++ show args
      showApp (Bind x (Lam p ty) sc) []
          = "\\" ++ show x ++ " : " ++ show ty ++
            " => " ++ show sc
      showApp (Bind x (Pi Explicit ty) sc) []
          = "((" ++ show x ++ " : " ++ show ty ++
            ") -> " ++ show sc ++ ")"
      showApp (Bind x (Pi Implicit ty) sc) []
          = "{" ++ show x ++ " : " ++ show ty ++
            "} -> " ++ show sc
      showApp (Bind x (PVar ty) sc) []
          = "pat " ++ show x ++ " : " ++ show ty ++
            " => " ++ show sc
      showApp (Bind x (PVTy ty) sc) []
          = "pty " ++ show x ++ " : " ++ show ty ++
            " => " ++ show sc
      showApp (App _ _) [] = "[can't happen]"
      showApp TType [] = "Type"
      showApp Erased [] = "[_]"
      showApp _ [] = "???"
      showApp f args = "(" ++ assert_total (show f) ++ " " ++
                        assert_total (showSep " " (map show args))
                     ++ ")"
