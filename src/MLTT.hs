{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore #-}
module MLTT where
import MLTT.Rules
import MLTT.AST
import Rule
import Data.Maybe 
import Control.Applicative (Alternative, empty)
import Data.Map(Map)

-- Test
-- funT :: Term -> Term -> Term 
-- funT a b = Pi "_" a b 

-- infixr 6 @=>
-- (@=>) = funT

-- -- Pi "A" (U 0) (Pi "x" (Var "A") (Var "A"))
-- idF :: Term 
-- idF = Lam "A" (U 0) $ Lam "x" (Var "A") (Var "x")

-- app :: Term
-- app = Lam "A" (U 0) $ Lam "B" (U 0) $ 
--   Lam "f" (Var "A" @=> Var "B") $ 
--   Lam "x" (Var "A") $ 
--     Var "f" `App` Var "x"

-- flipF :: Term 
-- flipF = Lam "A" (U 0) $ Lam "B" (U 0) $ Lam "C" (U 0) $
--   Lam "f" (Var "A" @=> Var "B" @=> Var "C") $ 
--   Lam "x" (Var "B") $ 
--   Lam "y" (Var "A") $
--     (Var "f") `App` (Var "y") `App` (Var "x")




$(genFuncion typeofFunc)

levelOf :: (Monad m, Alternative m) => Map String Term -> Term -> m Int
levelOf ctx t = case typeof ctx t of 
  Just t' -> case t' of 
    (U n) -> pure n 
    _ -> empty
  _ -> empty

-- TODO
-- pp :: Term -> String 
-- pp (Var x) = x 
-- pp (Pi "_" t b) = "(" ++ pp t ++ " -> " ++ pp b ++ ")"
-- pp (Pi x t b) = "(" ++ "P (" ++ x ++ ":" ++ pp t ++ ") [" ++ pp b ++ "]" ++ ")"
-- pp (Lam x t b) = "(" ++ "\\ (" ++ x ++ ":" ++ pp t ++ "). [" ++ pp b ++ "]" ++ ")"
-- pp (U n) = "U " ++ show n
-- pp e = let (f, xs) = flattenApp e in foldl (\ f x -> f ++ " " ++ pp x) (pp f) xs
--   where 
--     flattenApp (App a b) = let (f, xs) = flattenApp a in (f , xs ++ [b])
--     flattenApp e = (e, [])

