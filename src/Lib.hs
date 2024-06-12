{-# LANGUAGE TemplateHaskell #-}

module Lib
    ( someFunc
    ) where

import Syntax
import Context


someFunc :: IO ()
someFunc = putStrLn "someFunc"



