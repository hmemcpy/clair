{-# LANGUAGE GADTs #-}

-- |
-- Module      : CLAIR.Test.HelloWorld
-- Description : Test hello-world.clair examples

module CLAIR.Test.HelloWorld where

import Test.Tasty
import Test.Tasty.HUnit

import CLAIR.Syntax
import CLAIR.Parser
import CLAIR.TypeChecker
import CLAIR.TypeChecker.Types (emptyContext)
import CLAIR.Evaluator
import CLAIR.Confidence (Confidence(..))
import qualified Data.Text as T

-- ============================================================================
-- Hello World Tests
-- ============================================================================

-- | Test parsing of simple hello-world belief
test_hello_world_parse :: TestTree
test_hello_world_parse = testCase "Parse hello-world belief" $ do
  let input = "belief(\"Hello, world!\", 1.0, none, none, none)"
  case parseExpr input of
    Left err -> assertFailure $ "Parse failed: " ++ show err
    Right expr -> do
      -- Should parse to EBelief
      case expr of
        EBelief b -> do
          assertEqual "Confidence" (Confidence 1.0) (beliefConf b)
          assertEqual "Justification" JNone (beliefJustify b)
        _ -> assertFailure $ "Not a belief: " ++ show expr

-- | Test type checking of hello-world belief
test_hello_world_typecheck :: TestTree
test_hello_world_typecheck = testCase "Type check hello-world belief" $ do
  let expr = EBelief (Belief (ELit (LString (T.pack "Hello, world!"))) (Confidence 1.0) JNone INone PNone)
  case infer emptyContext expr of
    Left err -> assertFailure $ "Type check failed: " ++ show err
    Right (TCResult ty _) -> do
      case ty of
        TBelief (Confidence 1.0) (TBase TString) -> return ()
        _ -> assertFailure $ "Wrong type: " ++ show ty

-- | Test evaluation of hello-world belief
test_hello_world_eval :: TestTree
test_hello_world_eval = testCase "Evaluate hello-world belief" $ do
  let expr = EBelief (Belief (ELit (LString (T.pack "Hello, world!"))) (Confidence 1.0) JNone INone PNone)
  case eval expr of
    Left err -> assertFailure $ "Evaluation failed: " ++ show err
    Right val -> do
      case val of
        VBelief bv -> do
          assertEqual "Confidence" (Confidence 1.0) (bvConf bv)
          assertEqual "Value" (VString (T.pack "Hello, world!")) (bvValue bv)
        _ -> assertFailure $ "Not a belief value: " ++ show val

-- | Test box notation for hello-world
test_hello_world_box :: TestTree
test_hello_world_box = testCase "Box notation for hello-world" $ do
  let expr = EBox (Confidence 0.99) (ELit (LString (T.pack "Hello, world!")))
  case eval expr of
    Left err -> assertFailure $ "Evaluation failed: " ++ show err
    Right val -> do
      case val of
        VBelief bv -> do
          assertEqual "Confidence" (Confidence 0.99) (bvConf bv)
          assertEqual "Value" (VString (T.pack "Hello, world!")) (bvValue bv)
        _ -> assertFailure $ "Not a belief value: " ++ show val

-- ============================================================================
-- Test Suite
-- ============================================================================

-- | Main test suite for hello-world examples
testHelloWorld :: TestTree
testHelloWorld = testGroup "CLAIR.HelloWorld"
  [ test_hello_world_parse
  , test_hello_world_typecheck
  , test_hello_world_eval
  , test_hello_world_box
  ]
