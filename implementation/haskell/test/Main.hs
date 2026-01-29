{-# LANGUAGE GADTs #-}

-- |
-- Module      : Main
-- Description : Test suite entry point

module Main where

import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit

import qualified CLAIR.Test.Confidence as TC
import qualified CLAIR.Test.TypeChecker as TT
import qualified CLAIR.Test.Evaluator as TE

main :: IO ()
main = defaultMain $ testGroup "CLAIR Test Suite"
  [ TC.testConfidence
  , TT.testTypeChecker
  , TE.testEvaluator
  ]
