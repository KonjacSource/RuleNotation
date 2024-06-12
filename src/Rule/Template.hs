{-# LANGUAGE TemplateHaskell  #-}
module Rule.Template where
import Language.Haskell.TH
import Control.Monad


genLines :: Int -> DecsQ 
genLines l = pure $ join [
    let op = '|' : replicate i '-' ++ "|" in 
      [ InfixD (Fixity 0 InfixN) (mkName op)
      , ValD (VarP (mkName op)) (NormalB $ VarE 'undefined) [] 
      ] 
  | i <- [5, 10..l] ]
