module TemplateHaskellUtil (travExp, travBody, travClause, travDec, travMatch, travGuard, travStmt) where 
import Language.Haskell.TH

infixr 9 **>
(**>) :: Applicative f => Traversable t => (a -> f b) -> t a -> f (t b)
(**>) = traverse

travDec :: Monad m => (Exp -> m Exp) -> Dec -> m Dec
travDec f (FunD name ds) = FunD name <$> travClause f **> ds 
travDec f (ValD ps b c) = ValD ps <$> travBody f b <*> travDec f **> c
travDec _ v = pure v

travClause :: Monad m => (Exp -> m Exp) -> Clause -> m Clause
travClause f (Clause ps b c) = Clause ps <$> travBody f b <*> travDec f **> c

-- TODO
travStmt :: Monad m => (Exp -> m Exp) -> Stmt -> m Stmt
travStmt = const pure

travGuard :: Monad m => (Exp -> m Exp) -> Guard -> m Guard
travGuard f (NormalG e) = fmap NormalG $ f e >>= travExp f 
travGuard f (PatG ss) = PatG <$> travStmt f **> ss

travBody :: Monad m => (Exp -> m Exp) -> Body -> m Body
travBody f (NormalB e) = NormalB <$> (f e >>= travExp f)
travBody f (GuardedB ls) = do 
  let gs = map fst ls 
  let es = map snd ls 
  gs' <- travGuard f **> gs 
  es' <- f **> es 
  es'' <- travExp f **> es'
  pure . GuardedB $ zip gs' es'' 

travMatch :: Monad m => (Exp -> m Exp) -> Match -> m Match
travMatch f (Match ps b c) = Match ps <$> travBody f b <*> travDec f **> c  

travExp :: Monad m => (Exp -> m Exp) -> Exp -> m Exp 
travExp f ex@(AppE l r) = do 
  l' <- f l 
  r' <- f r 
  AppE <$> travExp f l' <*> travExp f r'
travExp f (AppTypeE l r) = do 
  l' <- f l 
  AppTypeE <$> travExp f l' <*> pure r
travExp f ex@(InfixE l e r) = do 
  l' <- f **> l 
  e' <- f e 
  r' <- f **> r 
  InfixE <$> travExp f **> l' <*> travExp f e' <*> travExp f **> r'
travExp f (UInfixE a b c) = do 
  a' <- f a 
  b' <- f b 
  c' <- f c 
  UInfixE <$> travExp f a' <*> travExp f b' <*> travExp f c'
travExp f (ParensE e) = ParensE <$> (f e >>= travExp f)
travExp f (LamE ps e) = LamE ps <$> (f e >>= travExp f)                       
travExp f (LamCaseE ms) = LamCaseE <$> travMatch f **> ms
travExp f (LamCasesE ls) = LamCasesE <$> travClause f **> ls                  
travExp f (TupE lme) = TupE <$> do
  lme' <- (f **>) **> lme
  (travExp f **>) **> lme'
travExp f (UnboxedTupE lme) = UnboxedTupE <$> do 
  lme' <- (f **>) **> lme
  (travExp f **>) **> lme'           
travExp f (UnboxedSumE e s1 s2) = (\x -> UnboxedSumE x s1 s2) <$> (f e >>= travExp f)
travExp f (CondE a b c) = do    
  a' <- f a 
  b' <- f b 
  c' <- f c 
  CondE <$> travExp f a' <*> travExp f b' <*> travExp f c'                  
travExp f (MultiIfE ls) = do 
  let gs = map fst ls 
  let es = map snd ls 
  gs' <- travGuard f **> gs 
  es' <- f **> es 
  es'' <- travExp f **> es'
  pure . MultiIfE $ zip gs' es''  
travExp f (LetE ds e) = do      
  ds' <- travDec f **> ds 
  e' <- f e 
  LetE ds' <$> travExp f e'
travExp f (CaseE e ms) = do 
  e' <- f e 
  CaseE <$> travExp f e' <*> travMatch f **> ms  
travExp f (DoE n ss) = DoE n <$> travStmt f **> ss           
travExp f (MDoE n ss) = MDoE n <$> travStmt f **> ss           
travExp f (CompE ss) = CompE <$> travStmt f **> ss               
travExp f (ListE es) = ListE <$> travExp f **> es                        
travExp f (SigE e t) = flip SigE t <$> (f e >>= travExp f)
travExp f (StaticE e) = StaticE <$> (f e >>= travExp f)
travExp f (GetFieldE e s) = flip GetFieldE s <$> (f e >>= travExp f)

travExp f e@(RecConE n ls) = f e                                    -- TODO
travExp f (RecUpdE e ls) = flip RecUpdE ls <$> (f e >>= travExp f)  -- TODO

travExp f x = f x
