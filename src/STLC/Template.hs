{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Eta reduce" #-}
{-# LANGUAGE UndecidableInstances #-}
module STLC.Template where


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

genAST stlcType
genAST stlcTerm

type Ctx = Map String Ty

$(pure (genFreeVar stlcTerm "fv" ("Var", 0) [("Lam", 0)]))
$(pure (genSubstitute stlcTerm "subst" ("Var", 0) [("Lam", 0)] "fv" "genName"))


genName :: [String] -> String -> String
genName n x = try (0 :: Int)
  where try i = let v = x ++ show i in
          if v `elem` n then try (i + 1) else v


maybeAlt :: (Alternative m) => Maybe a -> m a
maybeAlt (Just x) = pure x
maybeAlt Nothing = empty

infix 6 ∈
(∈) = undefined
infixr 0 ↦
(↦) = undefined
infixr 5 ⇒
(⇒) = undefined
infixl 4 <|
(<|) = undefined

typeofFunc :: Function
typeofFunc = Function
  { funcName = "typeof"
  , aboveDefs = [ define [e| (c :* expr) |- (x :* expr)  : (t :* patt) |] `bindTo` [e| t .<- typeof c x |]
                , define [e| (x :* expr) : (t :* patt) ∈ (c :*expr) |] `bindTo` [e| t .<- maybeAlt (M.lookup x c) |]
                ]
  , belowDefs = [ define [e| (c :* expr) |- (x :* expr)  : (t :* patt) |] `bindTo` [e| typeof c x .:= t |]
                ]
  , bothDefs  = [ define [e| λ (x :* expr) : (t :* expr) ↦ (b :* expr) |] `bindTo` [e| Lam x t b |]
                , define [e| Γ |] `bindTo` [e| gamma |]
                , define [e| (a :* expr) ⇒ (b :* expr) |] `bindTo` [e| Func a b |]
                , define [e| (c :* expr) <| (x :* expr) : (t :* expr) |] `bindTo` [e| insert x t c |]
                ]
  , rules     = [ [e|
                                       True
                      |---------------------------------------------| {- T int -}
                               Γ |- IntLit n : Int
                  |]
                , [e|
                                   Γ <| x : s  |- b :   t
                      |---------------------------------------------| {- T abs -} 
                                Γ |- (λ x : s ↦ b) : s ⇒ t
                  |]
                , [e|
                         Γ |- f : a ⇒ b /\ Γ |- x : t /\ a ==   t
                     |---------------------------------------------| {- T app -} 
                                   Γ |- App f x : b
                  |]
                , [e|
                                         x : t ∈ Γ
                      |---------------------------------------------| {- T var -}
                                      Γ |- Var x : t
                  |]
                ]
  , argNames  = ["c", "t"]
  }

infixl 6 -->
(-->) = undefined

infix 7 :=
data (:=) = (:=)

smallstepFunc :: Function
smallstepFunc = Function
  { funcName = "smallstep"
  , aboveDefs = [ define [e| (a :* expr) --> (b :* patt) |] `bindTo` [e| b .<- smallstep a |]
                ]
  , belowDefs = [ define [e| (a :* patt) --> (b :* expr) |] `bindTo` [e| smallstep a .:= b |]
                ]
  , bothDefs  = [ define [e| λ (x :* expr) : (t :* expr) ↦ (b :* expr) |] `bindTo` [e| Lam x t b |]
                , define [e| (a :* expr) ⇒ (b :* expr) |] `bindTo` [e| Func a b |]
                , define [e| (c :* expr) <| (x :* expr) : (t :* expr) |] `bindTo` [e| insert x t c |]
                , define [e| (a:*expr) ((b:*expr) := (c:*expr)) |] `bindTo` [e| subst (b,c) a |]
                ]
  , rules     = [ [e|
                            t1 --> t1'
                    |-------------------------|
                      App t1 t2 --> App t1' t2
                  |]
                , [e|
                            t2 --> t2'
                    |-------------------------|
                      App t1 t2 --> App t1 t2'
                  |]
                , [e|
                                      True
                    |---------------------------------------------|
                        App (λ x : s ↦ b) v --> b (x := v)
                  |]
                ]
  , argNames  = ["t"]

  }

infix 6 ⇓
(⇓) = undefined

data Value = VInt Int
           | VLam Ty (forall m. (Monad m, Alternative m) => Value -> m Value)
           | NVar String

asTerm :: (Monad m, Alternative m) => Value -> m Term
asTerm x = helper [] x
  where helper _ (NVar v) = pure $ Var v
        helper _ (VInt i) = pure $ IntLit i
        helper names (VLam t f) = let n = genName names "x" in do
          v' <- f (NVar n)
          v <- helper (n:names) v'
          pure $ Lam n t v

instance Show Value where
  show x = maybe "Nothing" show (asTerm @Maybe x)

evalFunc :: Function
evalFunc = Function
  { funcName = "eval"
  , aboveDefs = [ define [e| (c :* expr) |- (x :* expr)  ⇓ (t :* patt) |] `bindTo` [e| t .<- eval c x |]
                , define [e| (x :* expr) := (t :* patt) ∈ (c :*expr) |] `bindTo` [e| t .<- maybeAlt (M.lookup x c) |]
                ]
  , belowDefs = [ define [e| (c :* patt) |- (x :* patt)  ⇓ (t :* expr) |] `bindTo` [e| eval c x .:= t |]
                ]
  , bothDefs  = [ define [e| λ (x :* expr) : (t :* expr) ↦ (b :* expr) |] `bindTo` [e| Lam x t b |]
                , define [e| (a :* expr) ⇒ (b :* expr) |] `bindTo` [e| Func a b |]
                , define [e| (c :* expr) <| (x :* expr) := (t :* expr) |] `bindTo` [e| insert x t c |]
                ]
  , rules     = [ [e|
                        x := v ∈ c
                    |---------------|
                      c |- Var x ⇓ v
                  |]
                , [e|
                                           True
                    |-----------------------------------------------------------------|
                     c |- Lam x t v ⇓ VLam t (\xv -> maybeAlt $ eval (c <| x := xv) v)
                  |]
                , [e|
                             True
                    |-------------------------|
                      c |- IntLit x ⇓ VInt x
                  |]
                , [e|
                      c |- f ⇓ VLam _ fun /\ c |- x ⇓ xv /\ ret .<- fun xv
                    |-------------------------------------------------------|
                                     c |- App f x ⇓ ret
                  |]
                ]
  , argNames  = ["c","x"]
  }



