module Types where

import Control.Monad.Except
import Control.Monad.ST (ST)
import qualified Data.IntMap as IM
import Data.STRef
import Relude hiding (Type)

{-# ANN module ("HLint: ignore Use camelCase" ∷ String) #-}

type Name = Text
type Type = Term

data Surface
  = SVar Name
  | Sλ Name Surface
  | SΠ Name Surface Surface
  | SApp Surface Surface
  | SLet Name Surface Surface Surface
  | SType
  | SHole
  deriving Show

data BD = Bound | Defined
  deriving Show

data Term
  = Var Name
  | Λ Name Term
  | Π Name Type Type
  | Term :$ Term
  | Let Name Type Term Term
  | Type
  | Meta MetaVar
  | InsertedMeta MetaVar [BD]
  deriving Show

type VType = Val
type Spine = [Val]

data Val
  = VFlex MetaVar Spine
  | VRigid Name Spine
  | Vλ Name (Val → Val)
  | VΠ Name Val (Val → Val)
  | VType

type Env = [(Name, Val)]
type Ctx = [(Name, VType)]

data MetaEntry = Solved Val | Unsolved

newtype MetaVar = MetaVar { unMetaVar ∷ Int }
  deriving newtype (Eq, Show, Enum)

data MetaCtx = MetaCtx
  { nextMeta ∷ MetaVar
  , metaCtx  ∷ IntMap MetaEntry
  }

data TypeError
  = Mismatch Term Term
  | CantInferLambda
  | UnknownName Name
  | NotPi Term
  | CantUnify
  | Internal_NoMetaVar MetaVar
  deriving Show

type M s = ReaderT (STRef s MetaCtx) (ExceptT TypeError (ST s))

getMetaCtx ∷ M s MetaCtx
getMetaCtx = join $ asks $ lift . lift . readSTRef

modifyMetaCtx ∷ (MetaCtx → MetaCtx) → M s ()
modifyMetaCtx f = join $ asks $ lift . lift . flip modifySTRef' f

lookupMeta ∷ MetaVar → M s MetaEntry
lookupMeta mv@(MetaVar v) = do
  mctx ← metaCtx <$> getMetaCtx
  whenNothing (IM.lookup v mctx) $
    throwError $ Internal_NoMetaVar mv

freshMetaVar ∷ M s MetaVar
freshMetaVar = do
  mv ← nextMeta <$> getMetaCtx
  modifyMetaCtx $ \mctx@MetaCtx{metaCtx} → mctx
    { nextMeta = succ mv
    , metaCtx = IM.insert (unMetaVar mv) Unsolved metaCtx
    }
  pure mv
