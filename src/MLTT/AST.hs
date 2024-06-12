module MLTT.AST where

import Syntax

mlttTerm :: ASTDef
mlttTerm = ASTDef ("Term",
           [ ("Var", ["String"])
           , ("U", ["Int"])
           , ("Pi", ["String", "Term", "Term"])
           , ("Lam", ["String", "Term", "Term"])
           , ("App", ["Term", "Term"])
           ])
