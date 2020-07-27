
module Types (
  module Types,
  module Text.Megaparsec
  ) where

import Text.Megaparsec (SourcePos(..), unPos, initialPos)
import Lens.Micro.Platform

import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet        as IS
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

data SHead = SHVar StageId | SHZero deriving Eq
data StageExp = StageExp SHead Int

pattern SSuc :: StageExp -> StageExp
pattern SSuc s <- ((\case StageExp h n | n > 0     -> Just (StageExp h (n - 1))
                                       | otherwise -> Nothing) -> Just s)
                 where
  SSuc (StageExp h n) = StageExp h (n + 1)

pattern SZero :: StageExp
pattern SZero = StageExp SHZero 0

pattern SVar :: StageId -> StageExp
pattern SVar x = StageExp (SHVar x) 0

sLit :: Stage -> StageExp
sLit = StageExp SHZero

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

-- | Blocked problems.
type Blocking  = IS.IntSet
type BlockedBy = IS.IntSet

data MetaEntry
  = Unsolved Blocking ~VTy ~StageExp
  | Solved Val

  -- | Constancy (Γ, x : Rec A : U i) B   + a list of blocking metas.
  --   When B becomes constant, A is solved to ε
  | Constancy Cxt VTy StageExp VTy BlockedBy


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
data Vals  = VNil | VDef Vals ~Val | VSkip Vals

-- | Type environment.
data Types = TNil | TDef Types ~VTy StageExp | TBound Types ~VTy StageExp

type Ix       = Int
type Lvl      = Int
type Ty       = Tm
type VTy      = Val
type MCxt     = IM.IntMap MetaEntry
type StageCxt = IM.IntMap (Maybe StageExp)

-- | Extending `Types` with any type.
pattern TSnoc :: Types -> VTy -> StageExp -> Types
pattern TSnoc as a s <- ((\case TBound as a s -> Just (as, a, s)
                                TDef as a s   -> Just (as, a, s)
                                TNil          -> Nothing) -> Just (as, a, s))

lvlName :: [Name] -> Lvl -> Name
lvlName ns x = ns !! (length ns - x - 1)

-- | We need to distinguish invented names from source names, as
--   we don't want the former to shadow the latter during name lookup
--   in elaboration.
data NameOrigin =
    NOSource        -- ^ Names which come from surface syntax.
  | NOInserted      -- ^ Names of binders inserted by elaboration.


-- | Context for elaboration and unification.
data Cxt = Cxt {
  cxtVals       :: Vals,
  cxtTypes      :: Types,
  cxtNames      :: [Name],
  cxtNameOrigin :: [NameOrigin],
  cxtLen        :: Int}


data Tm
  = Var Ix                      -- ^ x
  | Let Name Ty StageExp Tm Tm  -- ^ let x : A : U i = t in u

  | Pi Name Icit Ty Ty  -- ^ (x : A : U i) → B)  or  {x : A : U i} → B
  | Lam Name Icit Ty Tm -- ^ λ(x : A).t  or  λ{x : A}.t
  | App Tm Tm Icit      -- ^ t u  or  t {u}

  | Code Tm             -- ^ ^A
  | Up Tm               -- ^ <t>
  | Down Tm             -- ^ ~t

  | Tel StageExp      -- ^ Tel
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

  | U StageExp        -- ^ U i
  | Meta MId          -- ^ α

  | Skip Tm           -- ^ explicit strengthening (convenience feature for closing types)
  | Wk Tm             -- ^ explicit weakening (convenience feature for ^ coercion)

data Spine
  = SNil
  | SApp Spine ~Val Icit
  | SAppTel ~Val Spine ~Val
  | SProj1 Spine
  | SProj2 Spine
  | SDown Spine

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
  | VU StageExp

  | VCode VTy
  | VUp Val

  | VTel StageExp
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

-- Lenses
--------------------------------------------------------------------------------

makeFields ''Cxt
makeFields ''Str
