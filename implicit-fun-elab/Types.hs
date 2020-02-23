
module Types (
  module Types,
  module Text.Megaparsec
  ) where

import Control.Exception
import Text.Megaparsec (SourcePos(..), unPos, initialPos)
import Text.Printf
import Lens.Micro.Platform

import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet        as IS

-- Raw syntax
--------------------------------------------------------------------------------

-- | We wrap `SourcePos` to avoid printing it in `Show`.
newtype SPos = SPos SourcePos deriving (Eq, Ord, Read)
instance Show SPos where show _ = ""

type Name = String
data Icit = Impl | Expl deriving (Eq)

instance Show Icit where
  show Expl = "explicit"
  show Impl = "implicit"

icit :: Icit -> a -> a -> a
icit Impl i e = i
icit Expl i e = e

data Raw
  = RVar Name                        -- ^ x
  | RLam Name (Maybe Raw) Icit Raw   -- ^ λx.t  or λ{x}.t with optional type annotation
                                     --   on x
  | RApp Raw Raw Icit                -- ^ t u  or  t {u}
  | RU                               -- ^ U
  | RPi Name Icit Raw Raw            -- ^ (x : A) → B  or  {x : A} → B
  | RLet Name Raw Raw Raw            -- ^ let x : A = t in u
  | RHole                            -- ^ _
  | RSrcPos SPos Raw                 -- ^ source position annotation, added by parsing

deriving instance Show Raw


-- Types
--------------------------------------------------------------------------------

-- | Elaboration problem identifier.
type MId = Int

-- | Blocked problems.
type Blocking  = IS.IntSet
type BlockedBy = IS.IntSet

data MetaEntry
  = Unsolved Blocking ~VTy
  | Solved Val

  -- | Constancy (Γ, x : Rec A) B   + a list of blocking metas.
  --   When B becomes constant, A is solved to ε
  | Constancy Cxt VTy VTy BlockedBy


-- | A partial mapping from levels to levels. Undefined domain reresents
--   out-of-scope or "illegal" variables.
type Renaming = IM.IntMap Lvl

-- | Explicit strengthening. We use this for pruning and checking meta solution
--   candidates.
data Str = Str {
  _strDom :: Lvl,        -- ^ size of renaming domain
  _strCod :: Lvl,        -- ^ size of renaming codomain
  _strRen :: Renaming,   -- ^ partial renaming
  _strOcc :: Maybe MId   -- ^ meta for occurs strengthening
  }

-- | Lift over a bound variable.
liftStr :: Str -> Str
liftStr (Str c d r occ) = Str (c + 1) (d + 1) (IM.insert d c r) occ

-- | Skip a bound variable.
skipStr :: Str -> Str
skipStr (Str c d r occ) = Str c (d + 1) r occ


data Vals  = VNil | VDef Vals ~Val | VSkip Vals
data Types = TNil | TDef Types ~VTy | TBound Types ~VTy
type Ix    = Int
type Lvl   = Int
type Ty    = Tm
type VTy   = Val
type MCxt  = IM.IntMap MetaEntry

-- | Extending `Types` with any type.
pattern TSnoc :: Types -> VTy -> Types
pattern TSnoc as a <- ((\case TBound as a -> Just (as, a)
                              TDef as a   -> Just (as, a)
                              TNil        -> Nothing) -> Just (as, a))

lvlName :: [Name] -> Lvl -> Name
lvlName ns x = ns !! (length ns - x - 1)

data NameOrigin =
    NOSource        -- ^ Names which come from surface syntax.
  | NOInserted      -- ^ Names of binders inserted by elaboration.

type MetaInsertion = Bool

-- | Context for elaboration and unification.
data Cxt = Cxt {
  cxtVals       :: Vals,
  cxtTypes      :: Types,
  cxtNames      :: [Name],
  cxtNameOrigin :: [NameOrigin],
  cxtLen        :: Int}

data Tm
  = Var Ix             -- ^ x
  | Let Name Ty Tm Tm  -- ^ let x : A = t in u

  | Pi Name Icit Ty Ty  -- ^ (x : A) → B)  or  {x : A} → B
  | Lam Name Icit Ty Tm -- ^ λ(x : A).t  or  λ{x : A}.t
  | App Tm Tm Icit      -- ^ t u  or  t {u}

  | Tel               -- ^ Tel
  | TEmpty            -- ^ ε
  | TCons Name Ty Ty  -- ^ (x : A) ▷ B
  | Rec Tm            -- ^ Rec A

  | Tempty            -- ^ []
  | Tcons Tm Tm       -- ^ t :: u
  | Proj1 Tm          -- ^ π₁ t
  | Proj2 Tm          -- ^ π₂ t

  | PiTel Name Ty Ty  -- ^ {x : A⃗} → B
  | AppTel Ty Tm Tm   -- ^ t {u : A⃗}

  | LamTel Name Ty Tm -- ^ λ{x : A⃗}.t

  | U                 -- ^ U
  | Meta MId          -- ^ α

  | Skip Tm           -- ^ explicit weakening (convenience feature in closing types)

data Spine
  = SNil
  | SApp Spine ~Val Icit
  | SAppTel ~Val Spine ~Val
  | SProj1 Spine
  | SProj2 Spine

valsLen :: Vals -> Int
valsLen = go 0 where
  go acc VNil        = acc
  go acc (VDef vs _) = go (acc + 1) vs
  go acc (VSkip vs)  = go (acc + 1) vs

data Head
  = HVar Lvl
  | HMeta MId
  deriving (Eq, Show)

data Val
  = VNe Head Spine

  | VPi Name Icit ~VTy (VTy -> VTy)
  | VLam Name Icit ~VTy (Val -> Val)
  | VU

  | VTel
  | VRec ~Val
  | VTEmpty
  | VTCons Name ~Val (Val -> Val)
  | VTempty
  | VTcons ~Val ~Val

  | VPiTel Name ~Val (Val -> Val)
  | VLamTel Name ~Val (Val -> Val)

pattern VVar :: Lvl -> Val
pattern VVar x = VNe (HVar x) SNil

pattern VMeta :: MId -> Val
pattern VMeta m = VNe (HMeta m) SNil

-- Errors
--------------------------------------------------------------------------------

data SpineError
  = SpineNonVar
  | SpineProjection
  | NonLinearSpine Lvl
  deriving (Show, Exception)

data StrengtheningError
  = ScopeError Lvl
  | OccursCheck
  deriving (Show, Exception)

data UnifyError
  = UnifyError [Name] Tm Tm
  | SpineError [Name] Tm Tm SpineError
  | StrengtheningError [Name] Tm Tm StrengtheningError
  deriving (Show, Exception)

data ElabError
  = UnifyErrorWhile Tm Tm UnifyError
  | NameNotInScope Name
  | ExpectedFunction Tm
  | IcitMismatch Icit Icit

data Err = Err {
  errNames :: [Name],
  errErr   :: ElabError,
  errPos   :: Maybe SPos}

instance Show Err where
  show _ = "Error"

instance Exception Err

report :: [Name] -> ElabError -> a
report ns e = throw (Err ns e Nothing)

-- | Rethrow an `Err` with source position attached.
addSrcPos :: SPos -> IO a -> IO a
addSrcPos p act = act `catch` \case
  Err ns e Nothing -> throwIO (Err ns e (Just p))
  e                -> throwIO e


-- Pretty printing
--------------------------------------------------------------------------------

prettyTm :: Int -> [Name] -> Tm -> ShowS
prettyTm prec = topLams (prec /= 0) "λ" "" where

  -- special case printing of top lambdas, since they are usually used
  -- to postulate stuff
  topLams :: Bool -> String -> String -> [Name] -> Tm -> ShowS
  topLams p pre post ns (Lam (fresh ns -> x) i a t) =
    showParen p (
      (pre++)
    . icit i bracket parens (
           ((if null x then "_" else x)++) . (" : "++) . go False ns a)
    . topLams False "\n" ".\n\n" (x:ns) t)
  topLams _ pre post ns t = (post++) . go False ns t

  fresh :: [Name] -> Name -> Name
  fresh _ "_" = "_"
  fresh ns n | elem n ns = fresh ns (n++"'")
             | otherwise = n

  goVar :: [Name] -> Ix -> ShowS
  goVar ns topX = go ns topX where
    -- go []     _ = error "impossible"
    go []     _ = (show topX++)
    go (n:ns) 0 = (n++)
    go (n:ns) x = go ns (x - 1)

  goArg :: [Name] -> Tm -> Icit -> ShowS
  goArg ns t i = icit i (bracket (go False ns t)) (go True ns t)

  goLamBind :: Name -> Icit -> ShowS
  goLamBind x i = icit i bracket id ((if null x then "_" else x) ++)

  bracket s = ('{':).s.('}':)
  parens  s = ('(':).s.(')':)

  goLam :: [Name] -> Tm -> ShowS
  goLam ns (Lam (fresh ns -> x) i a t)  = (' ':) . goLamBind x i . goLam (x:ns) t
  goLam ns (LamTel(fresh ns -> x) a t) =
    (' ':) . bracket ((x++) . (" : "++) . go False ns a) . goLam (x:ns) t
  goLam ns t = (". "++) . go False ns t

  goPiBind :: [Name] -> Name -> Icit -> Tm -> ShowS
  goPiBind ns x i a =
    icit i bracket (showParen True) ((x++) . (" : "++) . go False ns a)

  goPi :: [Name] -> Bool -> Tm -> ShowS
  goPi ns p (Pi (fresh ns -> x) i a b)
    | x /= "_" = goPiBind ns x i a . goPi (x:ns) True b
    | otherwise =
       (if p then (" → "++) else id) .
       go (case a of App{} -> False; AppTel{} -> False; _ -> True) ns a .
       (" → "++) . go False (x:ns) b

  goPi ns p (PiTel (fresh ns -> x) a b)
    | x /= "_" = goPiBind ns x Impl a . goPi (x:ns) True b
    | otherwise =
       (if p then (" → "++) else id) .
       go (case a of App{} -> False; AppTel{} -> False; _ -> True) ns a .
       (" → "++) . go False (x:ns) b

  goPi ns p t = (if p then (" → "++) else id) . go False ns t

  go :: Bool -> [Name] -> Tm -> ShowS
  go p ns = \case
    Var x -> goVar ns x
    Meta m -> ("?"++).(show m++)
    Let (fresh ns -> x) a t u ->
      ("let "++) . (x++) . (" : "++) . go False ns a . ("\n    = "++)
      . go False ns t  . ("\nin\n"++) . go False (x:ns) u
    App (App t u i) u' i' ->
      showParen p (go False ns t . (' ':) . goArg ns u i . (' ':) . goArg ns  u' i')
    App (AppTel _ t u) u' i' ->
      showParen p (go False ns t . (' ':) . goArg ns u Impl . (' ':) . goArg ns u' i')
    App t u i      -> showParen p (go True ns t . (' ':) . goArg ns u i)
    Lam (fresh ns -> x) i a t  -> showParen p (("λ "++) . goLamBind x i . goLam (x:ns) t)
    t@Pi{}         -> showParen p (goPi ns False t)
    U              -> ("U"++)
    Tel            -> ("Tel"++)
    TEmpty         -> ("ε"++)
    TCons "_" a as -> showParen p (go False ns a . (" ▷ "++). go False ns as)
    TCons (fresh ns -> x) a as ->
              showParen p (showParen True ((x++) . (" : "++) . go False ns a)
            . (" ▷ "++). go False (x:ns) as)
    Tempty         -> ("[]"++)
    Rec a          -> showParen p (("Rec "++) . go True ns a)
    Tcons t u      -> showParen p (go True ns t . (" ∷ "++). go False ns u)
    Proj1 t        -> showParen p (("π₁ "++). go True ns t)
    Proj2 t        -> showParen p (("π₂ "++). go True ns t)
    t@PiTel{}      -> showParen p (goPi ns False t)
    AppTel a (App t u i) u'  ->
      showParen p (go False ns t . (' ':) . goArg ns u i . (' ':) .
                   bracket (go False ns u' . (" : "++) . go False ns a))

    AppTel a' (AppTel a t u) u' ->
      showParen p (go False ns t . (' ':)
                   . bracket (go False ns u  . (" : "++) . go False ns a)
                   . bracket (go False ns u' . (" : "++) . go False ns a'))
    AppTel a t u ->
      showParen p (go True ns t . (' ':)
                   . bracket (go False ns u  . (" : "++) . go False ns a))
    LamTel x a t -> showParen p (("λ"++)
                   . bracket ((x++) . (" : "++) . go False ns a) . goLam (x:ns) t)

    Skip t -> go p ("_":ns) t

showTm :: [Name] -> Tm -> String
showTm ns t = prettyTm 0 ns t []
-- showTm ns t = show t
-- deriving instance Show Tm
instance Show Tm where show = showTm []

showError :: [Name] -> ElabError -> String
showError ns = \case
  UnifyErrorWhile lhs rhs e ->
    let err1 = case e of
          UnifyError ns lhs rhs -> printf
            ("Cannot unify\n\n" ++
             "  %s\n\n" ++
             "with\n\n" ++
             "  %s\n\n")
            (showTm ns lhs) (showTm ns rhs)
          StrengtheningError ns lhs rhs e -> case e of
            ScopeError x -> printf (
              "Variable %s is out of scope in equation\n\n" ++
              "  %s =? %s\n\n")
              (lvlName ns x) (showTm ns lhs) (showTm ns rhs)
            OccursCheck -> printf (
              "Meta occurs cyclically in its solution candidate in equation:\n\n" ++
              "  %s =? %s\n\n")
              (showTm ns lhs) (showTm ns rhs)
          SpineError ns lhs rhs e -> case e of
            SpineNonVar -> printf (
              "Non-bound-variable value in meta spine in equation:\n\n" ++
              "  %s =? %s\n\n")
              (showTm ns lhs) (showTm ns rhs)
            SpineProjection ->
              "Projection in meta spine\n\n"
            NonLinearSpine x -> printf
              ("Nonlinear variable %s in meta spine in equation\n\n" ++
               "  %s =? %s\n\n")
              (lvlName ns x)
              (showTm ns lhs) (showTm ns rhs)
    in err1 ++ printf
         ("while trying to unify\n\n" ++
         "  %s\n\n" ++
         "with\n\n" ++
         "  %s") (showTm ns lhs) (showTm ns rhs)

  NameNotInScope x ->
    "Name not in scope: " ++ x
  ExpectedFunction ty ->
    "Expected a function type, instead inferred:\n\n  " ++ showTm ns ty
  IcitMismatch i i' -> printf (
    "Function icitness mismatch: expected %s, got %s.")
    (show i) (show i')

-- Lenses
--------------------------------------------------------------------------------

makeFields ''Cxt
makeFields ''Err
makeFields ''Str
