{-# LANGUAGE TemplateHaskell #-}
{-# HLINT ignore #-}
module Rule where 

import Language.Haskell.TH
import Control.Monad.State.Strict
import Control.Monad.Except (ExceptT)
import Syntax
import Context
import Rule.Template
import Control.Applicative
import qualified Data.Map as M
import Data.Map (Map, fromList, insert)
import TemplateHaskellUtil
import Control.Monad.Identity (Identity(runIdentity, Identity))
import Control.Monad.Trans.Writer
{-
  typeof :: Ctx -> Term -> m Type 
  eval   :: Ctx -> Term -> m Term 
-}

data JudgementType = JudgementType 
  { mndType   :: Type  -- (Alternative mndType, Monad mndType)
  , ctxType   :: Type 
  , argType   :: Type 
  , retType   :: Type
  }

judgementType :: JudgementType -> Type 
judgementType (JudgementType mndType ctxType argType retType )
    = ctxType --> argType --> mndType `AppT` retType
  where 
    infixr 0 -->   
    a --> b = ArrowT `AppT` a `AppT` b

genLines 100

-- fake define
infix 2 |-
infixr 1 /\
infix 2 .<-
infix 1 .:=
infixl 3 <+ 
(|-) :: a 
(|-) = undefined
(/\) :: a
(/\) = undefined
(<+) :: a
(<+) = undefined
(.<-) :: a
(.<-) = undefined
(.:=) :: a
(.:=) = undefined

tyAppE :: Q Exp
tyAppE = [e| 
     c |- f : a :-> b /\ c |- x : xt /\ a == xt
   |---------------------------------------------|
                c |- App f x : b
  |]

-- tyApp :: Rule m
-- tyApp c (App f x) = do 
--   (a :-> b) <- typeof c f 
--   xt <- typeof c x
--   guard $ a == xt
--   pure b
-- tyApp _ _ = empty

{-

   c <+ y : t |- b : bt 
  |--------------------|
   c |- Lam y t b : Func t bt 

  tyLam :: Rule m
  tyLam c (Lam y t b) = do 
    bt <- typeof (M.insert y t c) b
    pure $ Func t bt
  tyLam _ _ = empty

-}

{- syntax of rule
  rule    = form |-------| to 
  to      = pattern |- pattern : expr 
  from    = from /\ from 
          | give 
          | expr (:: Bool)
  give    = context |- expr : pattern
  context = expr 
          | expr <+ expr : expr
-}


isLine :: Name -> Bool 
isLine name = case nameBase name of 
    "||" -> False
    '|' : rest -> all (== '-') (init rest) && last rest == '|'
    _ -> False

expandFrom :: Exp -> [Exp]
expandFrom (InfixE (Just l) (VarE andop) (Just r)) | nameBase andop == "/\\" = expandFrom l ++ expandFrom r
expandFrom e = [e]

flattenApp :: Exp -> (Exp, [Exp])
flattenApp (AppE a b) = let (f, xs) = flattenApp a in (f , xs ++ [b])
flattenApp (InfixE (Just a) f (Just b)) = flattenApp (f `AppE` a `AppE` b) 
flattenApp (InfixE (Just a) f Nothing) =  flattenApp (f `AppE` a)
flattenApp e = (e, [])


asPat :: Exp -> Pat 
asPat (UnboundVarE n) = VarP n 
asPat e = case flattenApp e of 
  (ConE con, args) -> ConP con [] (asPat <$> args)
  _ -> error $ show e ++ " is not a pattern"

data From = Give Exp {- Ctx -} Exp {- Term -} Pat 
          | Expr Exp

mkFrom :: Exp -> From 
mkFrom (InfixE (Just ctx) (VarE op1) (Just (InfixE (Just term) (ConE op2) (Just ty)))) 
  | nameBase op1 == "|-" && nameBase op2 == ":" = Give ctx term (asPat ty)
mkFrom e = Expr e


-- | Make a single typing rule, to use some oprators, you need the following functions in context:
-- - TODO c |- x : t   <-> t <- typeof c x       where typeof :: Context -> Term -> m Type                        
-- - TODO c <+ x : y   <-> insertTypeBind c x y  where insertTypeBind :: Context -> String -> Type -> Context   
-- - TODO t .<- c .? y <-> t <- getTypeBind c y  where getTypeBind :: Context -> String -> m Type                                
typingRule :: String -> Exp -> [Dec]
typingRule name (InfixE from' (VarE line) (Just to)) | isLine line 
  = [ FunD (mkName name) 
      [ Clause mainPat 
        (NormalB $ DoE Nothing (
          (toStmt <$> fromls) 
          ++ 
          [NoBindS $ VarE 'pure `AppE` retVal]) 
        )
        []
      , Clause [WildP, WildP] (NormalB $ VarE 'empty) []
      ]
    ]
  where from = case from' of { Just f -> f ; Nothing -> ConE 'True }
        fromls = mkFrom <$> expandFrom from
        (mainPat, retVal) = case to of 
          (InfixE (Just ctx) (VarE op1) (Just (InfixE (Just term) (ConE op2) (Just ty)))) 
            | nameBase op1 == "|-" && nameBase op2 == ":" -> ([asPat ctx, asPat term], ty) 
          _ -> error $ pprint to ++ " is not a typing conclusion"  
        toStmt (Give ctx term ty) = BindS ty (VarE (mkName "typeof") `AppE` ctx `AppE` term)
        toStmt (Expr e) = NoBindS (VarE 'guard `AppE` e)
typingRule _ e = fail $ show e ++ " is not a rule"

choice :: (Foldable t, Alternative f) => t (f a) -> f a
choice ls = foldr (<|>) empty ls 

typingRules :: [Q Exp] -> DecsQ 
typingRules es = let ruleBinds = map (("rule_" ++) . show) [1.. length es] in 
    do
      ls <- forM (ruleBinds `zip` es) $ \(name, e') -> do 
          e <- e'
          pure $ typingRule name e
      pure $
           [ FunD (mkName "typeof") 
              [ Clause [VarP (mkName "c"), VarP (mkName "t")]
                  (let [c, t] = map (VarE . mkName) ["c", "t"] in 
                    NormalB $ (VarE 'choice `AppE` ListE (map (\n -> VarE (mkName n) `AppE` c `AppE` t) ruleBinds)))
                  []
              ] 
           ]
        ++ join ls


--------------------------------------------------------------------------------------------------------------------
--                                               General Rules                                                    --
--------------------------------------------------------------------------------------------------------------------

(=#=) :: Name -> Name -> Bool 
(=#=) name1 name2 = nameBase name1 == nameBase name2

{- |
  Syntax to make a rule:

    rule = condition |-----| conclusion 

    conclusion =  name pats .:= exp

    condition = condition /\ condition
              | pat .<- exp
              | expr

  e.g. 
  @
        (a :-> b) .<- typeof c f  /\ xt .<- typeof c x /\ a == xt
      |------------------------------------------------------------|
                          typeof c (App f x) .:= b
  @
  would translate to 
  @
      tyApp :: Rule m
      tyApp c (App f x) = do 
        gen_var <- typeof c f 
        case gen_var of 
          (a :-> b) -> do 
            xt <- typeof c x
            guard $ a == xt
            pure b
          _ -> empty
      tyApp _ _ = empty
  @
  all rules will be listed together and generating "typeof" function.

  @typeof = choice [ tyApp, ... ]@

-}
data TRule = TRule [TCondition] TConclusion deriving (Eq, Show)

-- | conclusion =  name pats .:= exp
data TConclusion = TConclusion [Pat] Exp deriving (Eq, Show)
-- | condition = condition /\ condition
--             | pat .<- exp
--             | expr
data TCondition = CondBind Pat Exp 
                | CondGuard Exp 
                deriving (Eq, Show)

conds2Stmts :: Exp -> [TCondition] -> [Stmt]
conds2Stmts retVal [] = [ NoBindS (VarE 'pure `AppE` retVal) ]
conds2Stmts retVal (s:ss) = 
  let rest = conds2Stmts retVal ss 
  in  case s of 
        CondBind pat val -> let aname = mkName "gen_var" in  -- this is ok, as long as user do not use it. 
          [ BindS (VarP aname) val
          , NoBindS $ CaseE (VarE aname) 
                        [ Match pat   (NormalB (DoE Nothing rest)) []
                        , Match WildP (NormalB $ VarE 'empty)      []
                        ]
          ]
        CondGuard cond ->(NoBindS $ VarE 'guard `AppE` cond) : rest 


rule2Dec :: Name  -- ^ Function name for the rule, e.g. tyApp  
         -> TRule 
         -> Dec 
rule2Dec name (TRule conds (TConclusion pat retv)) =
  let body = conds2Stmts retv conds 
  in  FunD name 
        [ Clause pat (NormalB $ DoE Nothing body) []
        , Clause (replicate (length pat) WildP) (NormalB $ VarE 'empty) []
        ]

parseRule :: ([OperatorDef], [OperatorDef]) -> Exp -> TRule 
parseRule opdef exp' = let (InfixE (Just condt) _ (Just concl)) = substOp opdef exp' in 
  TRule (parseCondition <$> expandFrom condt) (parseConclusion concl)

parseConclusion :: Exp -> TConclusion
parseConclusion (InfixE (Just l) (VarE op) (Just exp)) 
  | op =#= '(.:=) = TConclusion (asPat <$> snd (flattenApp l)) exp
parseConclusion e = error $ show e ++ " is not a conclusion." 

parseCondition :: Exp -> TCondition
parseCondition (InfixE (Just pat) (VarE op) (Just exp))
  | op =#= '(.<-) = CondBind (asPat pat) exp
parseCondition e = CondGuard e

---------------------------------------------- Operators ----------------------------------------------

{- |
  
  We can define some operators to make our rules pretty.
  e.g. 
  @
  c |- x : t  =>  t .<- typing c x
  @
  so that
  @
        (a :-> b) .<- typeof c f  /\ xt .<- typeof c x /\ a == xt
      |------------------------------------------------------------|
                          typeof c (App f x) .:= b 
  @
  can be writen as 
  @
        c |- f : a :-> b /\ c |- x : xt /\ a == xt
     |---------------------------------------------|
                  c |- App f x : b
  @
  But there are some problems. 
  
  Above the line, some elements in the expression may be pattern, others may be expression.
  But below the line, the elements use to be patterns should be expressions, and those expressions should be patterns.
  To solve the problem, we consider that the namespaces in both sides of the line are different.
  
  So we define the operators separately

  Above:  @(c :* exp) |- (x :* exp) : (t :* pat) => t .<- typing c x@
  Below:  @(c :* pat) |- (x :* pat) : (t :* exp) => typing c x .:= t@

  the infixity should be defined in Haskell. 
  e.g.

  @ 
  infix 2 |-
  (|-) :: a 
  (|-) = undefined 
  @

  where (:) has already been defined as @infixr 5 :@

  The @substOp@ is the function we will use before we parse the rule.
-}
substOp :: ([OperatorDef], [OperatorDef]) -> Exp -> Exp 
substOp (ab, bl) (InfixE (Just condt) (VarE line) (Just concl)) | isLine line = 
  InfixE (Just $ substOperators ab condt) (VarE line) (Just $ substOperators bl concl)
substOp _ _ = error "not a rule"

data OperatorDef = 
  OperatorDef
  { lhs  :: Exp
  , rhs  :: Exp 
  } deriving (Show, Eq)


-- fake define
infix 9 :*
data (:*) = () :* ()
expr :: a
expr = undefined
patt :: a
patt = undefined

-- | 
-- @ 
--    unifyOp <$> [e| (c :* expr) |- (x :* expr)  : (t :* patt)  |] 
--            <*> [e|  ctx        |- (Lam x t b)  : (fa :-> fb)  |] 
-- == pure (Just (fromList [("c", ctx), ("x", Lambda x t b), ("t", fa :-> fb)]))
-- @
unifyOp :: Exp -> Exp -> Maybe (Map String Exp)
unifyOp (InfixE (Just (UnboundVarE v)) (ConE el) _) expr
  | el =#= '(:*) = Just (insert (nameBase v) expr M.empty)
unifyOp (AppE f x) (AppE f' x') = do 
  uf <- unifyOp f f' 
  ux <- unifyOp x x' 
  return $ M.union uf ux
unifyOp (InfixE (Just l1) op1 (Just r1)) (InfixE (Just l2) op2 (Just r2)) = do 
  uo <- unifyOp op1 op2
  ul <- unifyOp l1 l2 
  ur <- unifyOp r1 r2 
  return $ uo `M.union` ul `M.union` ur
unifyOp (InfixE Nothing op1 (Just r1)) (InfixE Nothing op2 (Just r2)) = do 
  uo <- unifyOp op1 op2
  ur <- unifyOp r1 r2 
  return $ uo `M.union` ur
unifyOp (InfixE (Just l1) op1 Nothing) (InfixE (Just l2) op2 Nothing) = do 
  uo <- unifyOp op1 op2
  ul <- unifyOp l1 l2 
  return $ uo `M.union` ul
unifyOp (ListE l) (ListE r) = if length l /= length r then Nothing else do 
  us <- mapM (uncurry unifyOp) (zip l r)
  return $ foldr M.union M.empty us
unifyOp (VarE a) (VarE b) | a =#= b = Just M.empty
unifyOp (UnboundVarE a) (UnboundVarE b) | a =#= b = Just M.empty
unifyOp (ConE a) (ConE b) | a =#= b = Just M.empty
unifyOp _ _ = Nothing

-- | 
-- @ 
--    substRhs (fromList [("c", ctx), ("x", Lambda x t b), ("t", fa :-> fb)]) 
--             <$> [e|  t .<- typing c x  |] 
-- == [e| (fa :-> fb) .<- typing ctx (Lambda x t b) |]
-- @
substRhs :: Map String Exp -> Exp -> Exp 
substRhs vmap rhs = runIdentity (travExp helper rhs) 
  where substWithName ex name = case M.lookup (nameBase name) vmap of
          Just e -> e 
          _ -> ex
        helper :: Exp -> Identity Exp
        helper ex@(VarE name) = Identity $ substWithName ex name
        helper ex@(ConE name) = Identity $ substWithName ex name
        helper ex@(UnboundVarE name) = Identity $ substWithName ex name
        helper ex = Identity ex

-- testUnifyOp1 :: IO ()
-- testUnifyOp1 = do 
--   lhs <- [e| (c :* expr) |- (x :* expr)  : (t :* patt)  |]
--   exp <- [e|  ctx        |- (Lam x t b)  : (fa :-> fb)  |] 
--   print $ fmap (map $ \(v,e) -> (v, pprint e)) $ fmap M.toList (unifyOp lhs exp)

-- infixr 0 |-> 
-- (|->) :: a
-- (|->) = undefined

-- testUnifyOp2 :: IO () 
-- testUnifyOp2 = do 
--   lhs <- [e| λ (x :* expr) : (t :* expr) |-> (b :* expr) |]
--   exp <- [e| λ x           : Int         |-> x + 2       |]
--   print $ fmap (map $ \(v,e) -> (v, pprint e)) $ fmap M.toList (unifyOp lhs exp)

-- testSubstRhs :: IO ()
-- testSubstRhs = do
--   lhs <- [e| (gen_c :* expr) |- (gen_x :* expr)  : (gen_t :* patt)  |]
--   exp <- [e|  ctx        |- (Lam x t b)  : (fa :-> fb)  |] 
--   let Just vmap = unifyOp lhs exp
--   print vmap
--   rhs <- [e| t .<- typing c x |]
--   print rhs
--   putStrLn . pprint $ substRhs vmap rhs

-- | 
-- Rename every variable pattern and return the list of the original variables.
-- @ 
--    renameLhs <$> [e|  (c :* expr) |- (x :* expr)  : (t :* patt)  |] 
-- == (,) [e| (c_pat_gen :* expr) |- (x_pat_gen :* expr)  : (t_pat_gen :* patt) |] <$> ["c","x","t"]
-- @
renameLhs :: Exp -> (Exp, [String]) 
renameLhs lhs = runWriter (travExp helper lhs)
  where helper :: Exp -> Writer [String] Exp
        helper (InfixE (Just (UnboundVarE v)) (ConE el) r)
          | el =#= '(:*) = writer ( (InfixE (Just (UnboundVarE (mkName $ nameBase v ++ "_pat_gen"))) (ConE el) r)
                                  , [nameBase v])
        helper e = pure e

-- renameLhsTest :: IO ()
-- renameLhsTest = do 
--   lhs <- [e|  (c :* expr) |- (x :* expr)  : (t :* patt) |] 
--   let (e,s) = renameLhs lhs
--   putStrLn . pprint $ e 
--   print s

-- | 
-- Rename every variable shows in list of the original variables.
-- @ 
--    renameLhs <$> [e|  t .<- typing c x  |] 
-- == [e| t_pat_gen .<- typing c_pat_gen x_pat_gen |] 
-- @
renameRhs :: [String] -> Exp -> Exp
renameRhs set rhs = runIdentity (travExp helper rhs)
  where helper :: Exp -> Identity Exp
        helper (VarE name) | nameBase name `elem` set = Identity . VarE . mkName $ nameBase name ++ "_pat_gen"
        helper (ConE name) | nameBase name `elem` set = Identity . ConE . mkName $ nameBase name ++ "_pat_gen"
        helper (UnboundVarE name) | nameBase name `elem` set = Identity . UnboundVarE . mkName $ nameBase name ++ "_pat_gen"
        helper ex = Identity ex 

renameOperatorDef :: OperatorDef -> OperatorDef
renameOperatorDef (OperatorDef lhs rhs) = let (lhs', set) = renameLhs lhs in OperatorDef lhs' (renameRhs set rhs)

newtype Flag = Flag Bool deriving (Show, Eq)

instance Semigroup Flag where 
  Flag a <> Flag b = Flag $ a || b

instance Monoid Flag where 
  mempty = Flag False

applyOp' :: OperatorDef -> Exp -> Maybe Exp 
applyOp' (OperatorDef lhs rhs) exp = let (exp', Flag flag) = runWriter (helper exp >>= travExp helper) in 
    if flag then 
      Just exp' 
    else 
      Nothing
  where helper :: Exp -> Writer Flag Exp
        helper e = case unifyOp lhs e of 
          Nothing -> pure e 
          Just vmap -> writer (substRhs vmap rhs, Flag True)

applyOp :: OperatorDef -> Exp -> Exp 
applyOp (OperatorDef lhs rhs) exp = runIdentity (helper exp >>= travExp helper)
  where helper :: Exp -> Identity Exp
        helper e = case unifyOp lhs e of 
          Nothing -> pure e 
          Just vmap -> pure $ substRhs vmap rhs

substOperators :: [OperatorDef] -> Exp -> Exp 
substOperators ops exp = foldr applyOp exp $ renameOperatorDef <$> ops 

define :: a -> a
define = id

bindTo :: Q Exp -> Q Exp -> Q OperatorDef
bindTo = liftA2 OperatorDef 

typeofAndLambda :: Q [OperatorDef]
typeofAndLambda = sequence $ 
  [ define [e| (c :* expr) |- (x :* expr)  : (t :* patt) |]   `bindTo` [e| typing c x .:= t |] -- [e| t .<- typing c x |]
  , define [e| λ (x :* expr) : (t :* expr) |-> (b :* expr) |] `bindTo` [e| Lam x t b |]
  ]

testSubstOperators :: IO ()
testSubstOperators = do 
  exp <- [e|
      c |- f : a :-> b /\ c |- x : xt /\ a == xt
     |---------------------------------------------|
                  c |- App f x : b
    |]
  defs <- runQ typeofAndLambda
  putStrLn . pprint $ substOperators defs exp


appList :: Exp -> [Exp] -> Exp 
appList f args = foldl AppE f args

data Function = 
  Function 
  { funcName  :: String
  , aboveDefs :: [Q OperatorDef]
  , belowDefs :: [Q OperatorDef]
  , bothDefs  :: [Q OperatorDef]
  , rules     :: [Q Exp]
  , argNames  :: [String]
  } 

genFuncion :: Function -> DecsQ 
genFuncion (Function funcName aboveDefs belowDefs bothDefs rules argNames) = do 
  both' <- sequence bothDefs
  abv' <- sequence aboveDefs
  bel' <- sequence belowDefs
  let abv = abv' ++ both'
  let bel = bel' ++ both' 
  rules' <- sequence rules
  let names = map (mkName . ((funcName ++ "_") ++) . show) [1 :: Int .. length rules']
  let ruleDecs = zipWith (\name rule -> rule2Dec name (parseRule (abv, bel) rule)) names rules' 
  pure $ [ FunD (mkName funcName) 
              [ Clause (VarP . mkName <$> argNames)
                  (NormalB $ (VarE 'choice `AppE` ListE (map (\ name -> appList (VarE name) (VarE . mkName <$> argNames)) names)))
                  []
              ] 
    ] ++ ruleDecs

