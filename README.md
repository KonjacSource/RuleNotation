# RuleNotation

This is a show case of the application of Template Haskell.

This is an example shows how we write a type checker for STLC,

```haskell

stlcTerm :: ASTDef
stlcTerm = ASTDef ("Term",
           [ ("Var", ["String"])
           , ("Lam", ["String", "Ty", "Term"])
           , ("App", ["Term", "Term"])
           , ("IntLit", ["Int"])
           ])

stlcType :: ASTDef
stlcType = ASTDef ("Ty",
           [ ("Int", [])
           , ("Bot", [])
           , ("Func", ["Ty", "Ty"])
           ])

genAST stlcType
{-
  data Term = Var String 
            | Lam String Ty Term 
            | App Term Term 
            | IntLit Int
-} 
genAST stlcTerm
{-
  data Ty = Int 
          | Bot 
          | Func Ty Ty 
-}

typeofFunc :: Function
typeofFunc = Function
  { funcName = "typeof"
  , aboveDefs = [ define [e| (c :* expr) |- (x :* expr)  : (t :* patt) |] `bindTo` [e| t .<- typeof c x |]
                , define [e| (x :* expr) : (t :* patt) ∈ (c :*expr) |] `bindTo` [e| t .<- liftMaybe (M.lookup x c) |]
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
                                   Γ <| x : s |- b : t
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

genFuncion typeofFunc
{-
typeof :: (Monad f, Alternative f) => Map String Ty -> Term -> f Ty
typeof c t = rule1 c t <|> rule2 c t <|> ...
  where rule1 gamma (IntLit n)  = do guard True
                                     pure Int 
        rule1 gamma _           = empty
        rule2 gamma (Lam x s b) = do t <- typeof (insert x s c) b
                                     pure (Func s t)
        rule2 gamma _           = empty
        ...

-}
```


