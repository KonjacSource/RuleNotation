{-# LANGUAGE TemplateHaskell #-}
{-# HLINT ignore #-}
module Syntax where

import Language.Haskell.TH
import Data.List(elemIndices)
import Control.Monad(join)

type Id = String

-- | Represents the definition of a syntax tree.
newtype ASTDef = ASTDef { unASTDef :: (Id, [(Id, [Id])]) } deriving (Show, Eq)


-- | Expend the definition of an AST.
genAST :: ASTDef -> Q [Dec]
genAST (ASTDef (name, ls)) = pure . pure $ DataD [] (mkName name) [] Nothing cons
    [DerivClause Nothing [ConT ''Eq, ConT ''Show]]
  where cons =  [ NormalC (mkName conName)
                    [(Bang NoSourceUnpackedness NoSourceStrictness
                      , ConT (mkName ty))
                    | ty <- conArgTy ]
                | (conName, conArgTy) <- ls ]


-- | Syntax tree definition for terms in stlc.
-- 
-- Which represents 
-- @
-- data Term = Var Id 
--           | Lam Id Term 
--           | App Term Term
-- @
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

unjust :: Maybe a -> a
unjust (Just a) = a
unjust _ = error "impossible"

-- mkPat "Var" ["a","b","c"] ==> Var a b c
mkPat :: Id -> [Id] -> Pat
mkPat conId argIds = ConP (mkName conId) [] (map (VarP . mkName) argIds)

genVarName :: [Id] -> [Id]
genVarName = zipWith (\ i v -> "gen_" ++ v ++ show i) [0 :: Int ..]

apply :: Exp -> [Exp] -> Exp
apply = foldl AppE

genFreeVar :: ASTDef
           -> Id              -- ^ Name of the freevar function to be defined
           -> (Id, Int)       -- ^ Var node name and its index of name argument position. 
                              -- e.g. @("Var", 0)@ for @| Var String@
           -> [(Id, Int)]     -- ^ Nodes may intro new variables. 
                              -- e.g. @("Lam", 0)@ for @| Lam String Ty Term@
           -> [Dec]             -- ^ @:: Term -> [Id]@
genFreeVar (ASTDef (tyName, cases)) fn (vcase, nameIx) lamcases =
    [ SigD (mkName fn) (ArrowT `AppT` ConT (mkName tyName) `AppT` (ListT `AppT` ConT ''Id))
    , FunD
        (mkName fn)
        (vclause
          : lamclauses
          ++ otherclauses
                (filter (\(n, _) -> n /= vcase && n `notElem` (fst <$> lamcases))
                  cases))
    ]
  where
    vcase_argsTy = unjust $ lookup vcase cases
    vcase_args = genVarName vcase_argsTy
    vclause = Clause  [mkPat vcase vcase_args]
                      (NormalB (VarE 'pure `AppE` VarE (mkName (vcase_args !! nameIx))))
                      []
    joinE :: [Exp] -> Exp
    joinE [] = ConE '[]
    joinE (x:xs) = VarE '(++) `AppE` x `AppE` joinE xs
    -- fn (Lam x t b) = filter (/= x) (fn b)
    lamclauses = [
        let lamcase_argsTy = unjust $ lookup lamcase cases
            lamcase_args = genVarName lamcase_argsTy
            selfIcs = elemIndices tyName lamcase_argsTy
            varName = mkName (lamcase_args !! varIx)
            selfNames = (mkName . (lamcase_args !!) <$> selfIcs)
        in  Clause
              [mkPat lamcase lamcase_args]
              (NormalB (
                VarE 'filter `AppE`
                    (VarE '(/=) `AppE` VarE varName) `AppE`
                    joinE (map ((VarE (mkName fn) `AppE`) . VarE) selfNames)))
              []
      | (lamcase, varIx) <- lamcases ] :: [Clause]
    otherclauses :: [(Id, [Id])] -> [Clause]
    otherclauses cases' = [
        let case_args = genVarName argls
            selfIcs = elemIndices tyName argls
            selfNames = (mkName . (case_args !!) <$> selfIcs)
        in  Clause
              [mkPat conId case_args]
              (NormalB $
                joinE (map ((VarE (mkName fn) `AppE`) . VarE) selfNames)
              )
              []
      | (conId, argls) <- cases']


{-
subst :: (String, Term) -> Term -> Term 
subst (x, n) (Var y) 
  | y == x    = n
  | otherwise = Var y 

subst (x, n) (Lam y t b) 
  | y == x           = Lam y t b
  | y `notElem` fv n = Lam y t (subst (x, n) b)
  | otherwise        = let ny = newName (fv n ++ fv b) y
                       in  subst (x, n) (Lam ny t (subst (y,Var ny) b))

subst (x, n) (App e1 e2) = App (subst (x, n) e1) (subst (x, n) e2)
subst (x, n) (IntLit i)  = IntLit i
-}
genSubstitute :: ASTDef
              -> Id           -- ^ Name of the substitute function to be define.
              -> (Id, Int)    -- ^ Var node name and its index of name argument position. 
                              -- e.g. @("Var", 0)@ for @| Var String@
              -> [(Id, Int)]  -- ^ Nodes may intro new variables. 
                              -- e.g. @[("Lam", 0)]@ for @| Lam String Ty Term@
              -> Id          -- ^ @:: Term -> [Id]@ A function to get free variables
              -> Id          -- ^ @:: [Id] -> Id -> Id@ New name generator
              -> [Dec]        -- ^ @:: (Id, Term) -> Term -> Term   
genSubstitute (ASTDef (tyName, cases)) fn (vcase, nameIx) lamcases fv_id nameGen_id = 
    [ SigD (mkName fn) (TupleT 2 `AppT` ConT ''Id `AppT` ConT (mkName tyName) --> ConT (mkName tyName) --> ConT (mkName tyName))
    , FunD
        (mkName fn)
        (varclause
          : lamclauses
          ++ otherclauses
                (filter (\(n, _) -> n /= vcase && n `notElem` (fst <$> lamcases))
                  cases))
    ]
  where
    fv = VarE (mkName fv_id)
    nameGen = VarE (mkName nameGen_id)
    infixl 9 $$
    ($$) = AppE
    infixr 0 -->   
    a --> b = ArrowT `AppT` a `AppT` b

    eq :: Exp -> Exp -> Exp
    eq a b = VarE '(==) $$ a $$ b

    vX = mkName "v_X"
    vN = mkName "v_N"
    tupxn = TupE [Just (VarE vX), Just (VarE vN)]
    -- subst (x, n) (Var y) 
    --   | y == x    = n
    --   | otherwise = Var y 
    varclause :: Clause
    varclause =
      let vcase_argsTy = unjust $ lookup vcase cases
          vcase_args = genVarName vcase_argsTy
      in  Clause
            [TupP [VarP vX, VarP vN], mkPat vcase vcase_args]
            (GuardedB $ let vY = mkName (vcase_args !! nameIx) in
              [ (NormalG $ VarE vX `eq` VarE vY , VarE vN)
              , (NormalG $ VarE 'otherwise,
                  apply (ConE (mkName vcase)) (map (VarE . mkName) vcase_args))
              ])
            []
    -- subst (x, n) (Lam y t b) 
    -- | y == x           = Lam y t b
    -- | y `notElem` fv n = Lam y t (subst (x, n) b)
    -- | otherwise        = let ny = newName (fv n ++ fv b) y
    --                      in  subst (x, n) (Lam ny t (subst (y,Var ny) b))
    lamclauses = [
        let lamcase_argsTy = unjust $ lookup lamcase cases
            lamcase_args = genVarName lamcase_argsTy
            selfIcs = elemIndices tyName lamcase_argsTy
            vY = mkName (lamcase_args !! varIx)
            selfNames = (mkName . (lamcase_args !!) <$> selfIcs)
        in Clause
            [TupP [VarP vX, VarP vN], mkPat lamcase lamcase_args]
            (GuardedB 
              [ (NormalG $ VarE vX `eq` VarE vY,
                  apply (ConE (mkName lamcase)) (map (VarE . mkName) lamcase_args) )
              , (NormalG $ VarE 'notElem $$ VarE vY $$ (fv $$ VarE vN),
                  foldl AppE (ConE (mkName lamcase)) 
                        (zipWith  (\v t -> 
                                    if t == tyName then 
                                      VarE (mkName fn) $$ tupxn $$ VarE (mkName v)
                                    else VarE (mkName v)
                                  ) 
                                  lamcase_args lamcase_argsTy))
              , (NormalG $ VarE 'otherwise, let ny = mkName "gen_newY" in 
                  LetE [FunD ny [Clause [] 
                    (NormalB 
                      (nameGen $$ (VarE '(++) $$ (fv $$ VarE vN) $$ (VarE 'join $$ (VarE 'map $$ fv $$ ListE (VarE <$> selfNames)))) $$ VarE vY)) []]] 
                  {- in -}
                  (let subst = VarE (mkName fn) in 
                    subst $$ tupxn $$ foldl AppE (ConE (mkName lamcase)) 
                        (zipWith  (\v t -> 
                                    if t == tyName then 
                                      subst $$ TupE [Just (VarE vY), Just (ConE (mkName vcase) $$ VarE ny)] $$ VarE (mkName v)
                                    else if v == lamcase_args !! varIx then 
                                      VarE ny
                                    else VarE (mkName v)
                                  ) lamcase_args lamcase_argsTy)
                  )
                )
              ]
            )
            []
      | (lamcase, varIx) <- lamcases ]
    -- subst (x, n) (App e1 e2) = App (subst (x, n) e1) (subst (x, n) e2)
    -- subst (x, n) (IntLit i)  = IntLit i
    otherclauses :: [(Id, [Id])] -> [Clause]
    otherclauses cases' = [
        let case_args = genVarName argls
            selfIcs = elemIndices tyName argls
            selfNames = (mkName . (case_args !!) <$> selfIcs)
        in  Clause
              [TupP [VarP vX, VarP vN], mkPat conId case_args]
              (NormalB $
                foldl AppE (ConE (mkName conId))
                  (zipWith (\v t -> 
                    if t == tyName then 
                       VarE (mkName fn) $$ tupxn $$ VarE (mkName v)
                    else VarE (mkName v)  
                  ) case_args argls)
              )
              []
      | (conId, argls) <- cases']

-- TODO
genAlphaEq :: ASTDef
           -> Id           -- ^ Name of the aplpha equivalent to be define.
           -> (Id, Int)    -- ^ Var node name and its index of name argument position. 
                           -- e.g. @("Var", 0)@ for @| Var String@
           -> [(Id, Int)]  -- ^ Nodes may intro new variables. 
                           -- e.g. @[("Lam", 0)]@ for @| Lam String Ty Term@
           -> [Dec]        -- ^ @:: Term -> Term -> Bool 
genAlphaEq (ASTDef (tyName, cases)) fn (vcase, nameIx) = undefined
  where alphaCtx = mkName "gen_AlphaCtx"



genTrav :: ASTDef -> Id -> [Dec]-- :: Monad m => (Term -> m Term) -> Term -> m Term
genTrav (ASTDef (tyName, cases)) traverser = 
  [ let m = mkName "m" in 
    let term = mkName tyName in 
      SigD traverserN (ForallT [PlainTV m SpecifiedSpec] [AppT (ConT ''Monad) (VarT m)] 
      (AppT (AppT ArrowT (AppT (AppT ArrowT (ConT term)) (AppT (VarT m) (ConT term)))) (AppT (AppT ArrowT (ConT term)) (AppT (VarT m) (ConT term)))))
  , FunD traverserN (otherclauses cases) 
  ]
  where traverserN = mkName traverser
        otherclauses :: [(Id, [Id])] -> [Clause]
        otherclauses cases' = [
            let case_args = genVarName argls
                selfIcs = elemIndices tyName argls
                selfStrs = (case_args !!) <$> selfIcs
                selfNames' = (mkName . (++ "\'")) <$> selfStrs
                selfNames = mkName <$> selfStrs
                fn = mkName "gen_f"
                traverserV = VarE traverserN
                infixl 6 |*|
                a |*| b = InfixE (Just a) (VarE '(<*>)) (Just b)
                liftExp :: Exp -> [String] -> Exp
                liftExp f [] = f
                liftExp f (x:xs) | x `elem` selfStrs = liftExp (f |*| (traverserV `AppE` VarE fn `AppE` (VarE (mkName (x ++ "\'"))))) xs
                                 | otherwise = liftExp (f |*| (VarE 'pure `AppE` VarE (mkName x))) xs
            in  Clause
                  [VarP fn, mkPat conId case_args]
                  (NormalB $ DoE Nothing $ 
                    map (\(v, n) -> BindS (VarP v) (VarE fn `AppE` VarE n)) (zip selfNames' selfNames)
                    ++ [NoBindS $ liftExp (VarE 'pure `AppE` (ConE $ mkName conId)) case_args]
                  )
                  []
          | (conId, argls) <- cases']

genTrav1 :: ASTDef -> Id -> [Dec] -- :: Monad m => (Term -> m Term) -> Term -> m Term
genTrav1 (ASTDef (tyName, cases)) traverser = 
  [ let m = mkName "m" in 
    let term = mkName tyName in 
      SigD traverserN (ForallT [PlainTV m SpecifiedSpec] [AppT (ConT ''Monad) (VarT m)] 
      (AppT (AppT ArrowT (AppT (AppT ArrowT (ConT term)) (AppT (VarT m) (ConT term)))) (AppT (AppT ArrowT (ConT term)) (AppT (VarT m) (ConT term)))))
  , FunD traverserN (otherclauses cases) 
  ]
  where traverserN = mkName traverser
        otherclauses :: [(Id, [Id])] -> [Clause]
        otherclauses cases' = [
            let case_args = genVarName argls
                selfIcs = elemIndices tyName argls
                selfStrs = (case_args !!) <$> selfIcs
                selfNames' = (mkName . (++ "\'")) <$> selfStrs
                selfNames = mkName <$> selfStrs
                fn = mkName "gen_f"
                infixl 6 |*|
                a |*| b = InfixE (Just a) (VarE '(<*>)) (Just b)
                liftExp :: Exp -> [String] -> Exp
                liftExp f [] = f
                liftExp f (x:xs) | x `elem` selfStrs = liftExp (f |*| (VarE 'pure `AppE` VarE (mkName (x ++ "\'")))) xs
                                 | otherwise = liftExp (f |*| (VarE 'pure `AppE` VarE (mkName x))) xs
            in  Clause
                  [VarP fn, mkPat conId case_args]
                  (NormalB $ DoE Nothing $ 
                    map (\(v, n) -> BindS (VarP v) (VarE fn `AppE` VarE n)) (zip selfNames' selfNames)
                    ++ [NoBindS $ liftExp (VarE 'pure `AppE` (ConE $ mkName conId)) case_args]
                  )
                  []
          | (conId, argls) <- cases']