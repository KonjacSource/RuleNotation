{-# LANGUAGE TemplateHaskell #-}
module MLTT.Rules where
import Context
import Control.Monad (join, guard)
import Data.List (nub)
import qualified Data.Map as M
import Data.Map (Map, insert, member)
import Control.Applicative
import Language.Haskell.TH
import Rule
import Data.Maybe
import Syntax

import MLTT.AST
import Control.Monad.Identity
import Debug.Trace (trace)

genName :: [String] -> String -> String
genName n x = try (0 :: Int)
  where try i = let v = x ++ show i in
          if v `elem` n then try (i + 1) else v

genAST mlttTerm

$(pure (genFreeVar mlttTerm "freevar" ("Var", 0) [("Lam", 0), ("Pi", 0)]))
$(pure (genSubstitute mlttTerm "subst" ("Var", 0) [("Lam", 0), ("Pi", 0)] "freevar" "genName"))
$(pure (genTrav mlttTerm "travTerm"))
$(pure (genTrav1 mlttTerm "travTerm1"))


infix 6 -->
(-->) = undefined

normalize :: Term -> Term
normalize term = runIdentity (travTerm1 help (fromMaybe term (help1 term)))
  where help1 :: Term -> Maybe Term
        -- If you defined more eliminator, add it here.
        help1 (App f arg) = case normalize f of
          Lam x t b -> pure $ normalize (subst (x, normalize arg) b)
          f' -> pure $ App f' (normalize arg)
        help1 _ = Nothing
        help x = case help1 x of
          Just x' -> pure x'
          _ -> pure $ normalize x


maybeAlt :: (Alternative m) => Maybe a -> m a
maybeAlt (Just x) = pure x
maybeAlt Nothing = empty
-- -- | Alpha equivalent
-- $(pure (genAlphaEq mlttTerm "alphaEq" ("Var", 0) [("Lam", 0), ("Pi", 0)]))

infix 4 =*=
(=*=) :: Term -> Term -> Bool 
(=*=) = alphaCtx M.empty 
  where 
    alphaCtx :: Map String String -> Term -> Term -> Bool 
    alphaCtx vars (Var a) (Var b) = case M.lookup a vars of 
      Just a' -> a' == b 
      _ -> a == b 
    alphaCtx vars (U l1) (U l2) = l1 == l2 
    alphaCtx vars (Pi n t b) (Pi n' t' b') = let vars' = insert n n' vars in
      alphaCtx vars t t' && alphaCtx vars' b b' 
    alphaCtx vars (Lam n t b) (Lam n' t' b') = let vars' = insert n n' vars in 
      alphaCtx vars t t' && alphaCtx vars' b b' 
    alphaCtx vars (App f x) (App f' x') = alphaCtx vars f f' && alphaCtx vars x x' 
    alphaCtx _ _ _ = False

infix 4 =~ 
(=~) :: Term -> Term -> Bool 
t =~ t' = normalize t =*= normalize t'


typeofFunc :: Function
typeofFunc = Function
  { funcName = "typeof"
  , aboveDefs = [ define [e| (c :* expr) |- (x :* expr)  : (t :* patt) |] `bindTo` [e| t .<- typeof c x |]
                , define [e| (x :* expr) : (t :* patt) ∈ (c :*expr) |] `bindTo` [e| t .<- maybeAlt (M.lookup x c) |]
                , define [e| (c :* expr ) |- (t :* term) : U (l :* patt) |] `bindTo` [e| l .<- levelOf c t |]
                ]
  , belowDefs = [ define [e| (c :* expr) |- (x :* expr)  : (t :* patt) |] `bindTo` [e| typeof c x .:= t |]
                ]
  , bothDefs  = [ define [e| λ (x :* expr) : (t :* expr) ↦ (b :* expr) |] `bindTo` [e| Lam x t b |]
                , define [e| Π ((x :* expr) : (t :* expr)) . (b :* expr) |] `bindTo` [e| Pi x t b |]
                , define [e| Γ |] `bindTo` [e| gamma |]
                , define [e| (c :* expr) <| (x :* expr) : (t :* expr) |] `bindTo` [e| insert x t c |]
                ]
  , rules     = [ [e|
                                       True
                      |---------------------------------------------|
                               Γ |- U n : U (n + 1)
                  |]
                , [e| 
                                      x : t ∈ Γ
                      |---------------------------------------------|
                                    Γ |- Var x : t
                  |]
                , [e| 
                         Γ |- t : U l1 /\ (Γ <| x : t) |- b : U l2
                      |---------------------------------------------|
                           Γ |- (Π (x : t) . b) : U (max l1 l2)
                  |]
                , [e| 
                                  (Γ <| x : s) |- b : t
                      |---------------------------------------------|
                           Γ |- (λ x : s ↦ b) : (Π (x : s) . t)
                  |]
                , [e| 
                         Γ |- f : (Π (y : s) . t) /\ Γ |- x : s' /\ s =~ s'
                      |-------------------------------------------------------|
                                     Γ |- App f x : t
                  |]
                ]
  , argNames  = ["c", "t"]
  }




