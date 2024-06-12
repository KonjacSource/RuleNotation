{-# LANGUAGE TemplateHaskell #-}

module STLC where 

import Syntax
import Context
import Control.Monad (join, guard)
import Data.List (nub)
import qualified Data.Map as M
import Data.Map (Map, insert, member)
import Control.Applicative
import Language.Haskell.TH
import STLC.Template
import Rule
import Data.Maybe (fromJust)


-- typeof :: (Monad f, .Alternative f) => Map String Ty -> Term -> f Ty
$(genFuncion typeofFunc)
-- smallstep :: (Monad f, Alternative f) => Term -> f Term
$(genFuncion smallstepFunc)
-- Map String Value -> Term -> Maybe Value
$(genFuncion evalFunc)