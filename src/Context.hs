{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore #-}
module Context where
import Language.Haskell.TH
import Data.Map
import Control.Monad.State.Strict
import Control.Monad.Except (ExceptT)
import GHC.IO (unsafePerformIO)

type Id = String

newtype ContextDef = ContextDef
    { unContextDef :: (Id, Q Type) }


instance Show ContextDef where
  show (ContextDef (name, ty)) = 
    name ++ " = [(Id, " 
    ++ unsafePerformIO (runQ ty >>= pure . pprint) 
    ++ ")]"

-- | @
-- type `name = Map Id `valueTy
-- type `nameM = Except String {- Error Info -} (State `name)
-- @
genContext :: ContextDef -> Q [Dec]
genContext (ContextDef (name, valueTy)) = do 
  vt <- valueTy 
  pure 
    [ TySynD (mkName name) []
        (ConT ''Map `AppT`
          ConT ''String `AppT`
          vt)
    ]


