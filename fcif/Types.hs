
module Types (
  module Types,
  module Text.Megaparsec
  ) where

import Text.Megaparsec (SourcePos(..), unPos, initialPos)
import Lens.Micro.Platform

import qualified Data.IntMap.Strict as IM
import Data.Kind

type Dbg = (() :: Constraint)
-- type Dbg = HasCallStack

-- Raw syntax
--------------------------------------------------------------------------------

-- | We wrap `SourcePos` to avoid printing it in `Show`, as that would be
--   unreadable because of clutter.
newtype SPos = SPos SourcePos deriving (Eq, Ord, Read)
instance Show SPos where show _ = ""

type Name = String
data Icit = Impl | Expl deriving (Eq)

instance Show Icit where
  show Expl = "explicit"
  show Impl = "implicit"

type Stage   = Int
type StageId = Int

data SHead = SHMeta StageId | SHVar Lvl | SHZero deriving (Eq)

data StageTm = SZero | SSuc StageTm | SMeta StageId | SVar Ix | SOmega

data VStage = VSFin SHead Int | VOmega

  -- SFin SHead Int | SOmega

pattern VSSuc :: VStage -> VStage
pattern VSSuc s <- ((\case VSFin h n | n > 0 -> Just (VSFin h (n - 1))
                           _                 -> Nothing) -> Just s) where
  VSSuc (VSFin h n) = VSFin h (n + 1)
  VSSuc _           = error "impossible"

pattern VSZero :: VStage
pattern VSZero = VSFin SHZero 0

pattern VSVar :: Lvl -> VStage
pattern VSVar x = VSFin (SHVar x) 0

pattern VSMeta :: StageId -> Int -> VStage
pattern VSMeta m n = VSFin (SHMeta m) n

sFin :: Stage -> VStage
sFin = VSFin SHZero


icit :: Icit -> a -> a -> a
icit Impl i e = i
icit Expl i e = e

-- | Surface syntax.
data Raw
  = RVar Name                        -- ^ x
  | RLam Name (Maybe Raw) Icit Raw   -- ^ λ x. t  or λ{x}. t with optional type annotation
                                     --   on x
  | RApp Raw Raw Icit                -- ^ t u  or  t {u}
  | RU (Maybe Stage)                 -- ^ U  or  U i

  | RCode Raw                        -- ^ (^A)
  | RUp Raw                          -- ^ <t>
  | RDown Raw                        -- ^ ~t

  | RPi Name Icit Raw Raw            -- ^ (x : A) → B  or  {x : A} → B
  | RLet Name Raw Raw Raw            -- ^ let x : A = t in u
  | RHole                            -- ^ _
  | RSrcPos SPos Raw                 -- ^ source position annotation, added by parsing

deriving instance Show Raw


-- Types
--------------------------------------------------------------------------------

-- | Elaboration problem identifier.
type MId = Int

data MetaEntry
  = Unsolved ~VTy ~StageTm
  | Solved Val

-- | A partial mapping from levels to levels. Undefined domain represents
--   out-of-scope variables.
type Renaming = IM.IntMap Lvl

-- | Explicit strengthening. We use this for pruning and checking meta solution
--   candidates.
data Str = Str {
  _strDom :: Lvl,        -- ^ size of renaming domain
  _strCod :: Lvl,        -- ^ size of renaming codomain
  _strRen :: Renaming,   -- ^ partial renaming
  _strOcc :: Maybe MId   -- ^ meta for occurs checking
  }

-- | Lift a `Str` over a bound variable.
liftStr :: Str -> Str
liftStr (Str c d r occ) = Str (c + 1) (d + 1) (IM.insert d c r) occ

-- | Skip a bound variable.
skipStr :: Str -> Str
skipStr (Str c d r occ) = Str c (d + 1) r occ

-- | Value environment. `VSkip` skips over a bound variable.
data Vals
  = VNil
  | VDef Vals ~Val
  | VSkip Vals
  | VDefStage Vals VStage
  | VSkipStage Vals

-- | Type environment.
data Types =
  TNil | TDef Types ~VTy StageTm | TBound Types ~VTy StageTm | TStage Types


data StageEntry = SEUnsolved Lvl | SESolved VStage

type Ix       = Int
type Lvl      = Int
type Ty       = Tm
type VTy      = Val
type MCxt     = IM.IntMap MetaEntry
type StageCxt = IM.IntMap StageEntry

-- | Extending `Types` with any type.
pattern TSnoc :: Types -> VTy -> StageTm -> Types
pattern TSnoc as a s <- ((\case TBound as a s -> Just (as, a, s)
                                TDef as a s   -> Just (as, a, s)
                                TNil          -> Nothing) -> Just (as, a, s))

-- | We need to distinguish invented names from source names, as
--   we don't want the former to shadow the latter during name lookup
--   in elaboration.
data Origin =
    Source        -- ^ Names which come from surface syntax.
  | Inserted      -- ^ Names of binders inserted by elaboration.
  deriving (Eq, Show)


-- | Context for elaboration and unification.
data Cxt = Cxt {
  cxtVals       :: Vals,
  cxtTypes      :: Types,
  cxtNames      :: [Name],
  cxtNameOrigin :: [Origin],
  cxtLen        :: Int}

instance Show Cxt where show = show . cxtNames

lvlName :: Cxt -> Lvl -> Name
lvlName cxt x = cxtNames cxt !! (cxtLen cxt - x - 1)

data Tm
  = Var Ix                      -- ^ x
  | Let Name Ty StageTm Tm Tm  -- ^ let x : A : U i = t in u

  | Pi Name Icit Ty Ty         -- ^ (x : A : U i) → B)  or  {x : A : U i} → B
  | Lam Name Icit Origin Ty Tm -- ^ λ(x : A).t  or  λ{x : A}.t
  | App Tm Tm Icit Origin      -- ^ t u  or  t {u}

  | PiStage [Name] Tm StageTm
  | AppStage Tm [StageTm]
  | LamStage [Name] Tm

  | Code Tm             -- ^ ^A
  | Up Tm               -- ^ <t>
  | Down Tm             -- ^ [t]

  | Tel StageTm       -- ^ Tel
  | TEmpty            -- ^ ε
  | TCons Name Ty Ty  -- ^ (x : A) ▷ B
  | Rec Tm            -- ^ Rec A

  | Tempty            -- ^ []
  | Tcons Tm Tm       -- ^ t :: u
  | Proj1 Tm          -- ^ π₁ t
  | Proj2 Tm          -- ^ π₂ t
  | U StageTm         -- ^ U i
  | Meta MId          -- ^ α

  | Skip Tm           -- ^ explicit strengthening
  | Wk Tm             -- ^ explicit weakening

data Spine
  = SNil
  | SApp Spine ~Val Icit Origin
  | SProj1 Spine
  | SProj2 Spine
  | SDown Spine

valsLen :: Vals -> Int
valsLen = go 0 where
  go acc VNil             = acc
  go acc (VDef vs _)      = go (acc + 1) vs
  go acc (VSkip vs)       = go (acc + 1) vs
  go acc (VSkipStage vs)  = go (acc + 1) vs
  go acc (VDefStage vs _) = go (acc + 1) vs

data Head
  = HVar Lvl
  | HMeta MId
  deriving (Eq, Show)

data Val
  = VNe Head Spine

  | VPi Name Icit ~VTy (VTy -> VTy)
  | VLam Name Icit Origin ~VTy (Val -> Val)
  | VU VStage

  | VCode VTy
  | VUp Val

  | VPiStage [Name] ([VStage] -> (VTy, VStage))
  | VLamStage [Name] ([VStage] -> Val)
  | VAppStage Val [VStage]

  | VTel VStage
  | VRec ~Val
  | VTEmpty
  | VTCons Name ~Val (Val -> Val)
  | VTempty
  | VTcons ~Val ~Val

pattern VVar :: Lvl -> Val
pattern VVar x = VNe (HVar x) SNil

pattern VMeta :: MId -> Val
pattern VMeta m = VNe (HMeta m) SNil

-- Lenses
--------------------------------------------------------------------------------

makeFields ''Cxt
makeFields ''Str
