{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <&>" #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
module Test where

import Syntax
import Context
import Control.Monad (join, guard)
import Data.List (nub)
import qualified Data.Map as M
import Data.Map (Map, insert, member)
import Control.Applicative
import Language.Haskell.TH

import Rule
import Data.Maybe (fromJust)

-- genAST stlcType
-- genAST stlcTerm

-- type Ctx = Map String Ty

-- $(pure (genFreeVar stlcTerm "fv" ("Var", 0) [("Lam", 0)]))
-- $(pure (genSubstitute stlcTerm "subst" ("Var", 0) [("Lam", 0)] "fv" "genName"))

-- term :: Term
-- term = Lam "x" Int (Var "x") `App` Var "y"

-- genName :: [String] -> String -> String
-- genName n x = try (0 :: Int)
--   where try i = let v = x ++ show i in 
--           if v `elem` n then try (i + 1) else v 

-- type Rule m = (Alternative m, Monad m, MonadFail m) => Map String Ty -> Term -> m Ty

-- justAlt :: (Alternative m) => Maybe a -> m a
-- justAlt (Just x) = pure x
-- justAlt Nothing = empty

{-
  Typing is 
-}

-- $(typingRules
--    [  [e|
--                            True
--           |---------------------------------------------| {- T int -}
--                    厂 |- IntLit n : Int
--       |]
--    ,  [e| 
--                     insert y t 厂 |- b : bt 
--           |---------------------------------------------| {- T abs -}
--                     厂 |- Lam y t b : t :-> bt    
--       |]
--    ,  [e| 
--            厂 |- f : a :-> b /\ 厂 |- x : xt /\ a == xt
--           |---------------------------------------------| {- T app -}
--                         厂 |- App f x : b     
--       |]
--    ,  [e|
--                              x ∈ 厂
--           |---------------------------------------------| {- T var -}
--                厂 |- Var x : fromJust (M.lookup x 厂)
--       |]
--    ]
--  )

-- typeofFunc :: Function 


parseTest :: IO ()
parseTest = do 
  -- e <- [e| 
  --        Γ |- f : (a :-> b) /\ Γ |- x : t /\ a == xt
  --      |----------------------------------------|
  --                   Γ |- App f x : b
  --      |]
  e <- [e| 
                    insert y t Γ |- b : bt 
          |---------------------------------------------| {- T abs -}
                    Γ |- Lam y t b : t :-> bt    
       |] 
  ab <- runQ $ sequence 
    [ define [e| (c :* expr) |- (x :* expr)  : (t :* patt) |]   `bindTo` [e| t .<- typing c x |]
    , define [e| λ (x :* expr) : (t :* expr) |-> (b :* expr) |] `bindTo` [e| Lam x t b |]
    , define [e| Γ |] `bindTo` [e| gamma |]
    ]
  bl <- runQ $ sequence
    [ define [e| (c :* expr) |- (x :* expr)  : (t :* patt) |]   `bindTo` [e| typing c x .:= t |]
    , define [e| Γ |] `bindTo` [e| gamma |]
    ]
  let pr = substOp (ab,bl) e
  putStrLn . pprint $ pr 
  putStrLn "\n\n"
  putStrLn . pprint $ rule2Dec (mkName "tyApp") (parseRule (ab,bl) e)

