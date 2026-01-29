{-# LANGUAGE GADTs #-}

-- |
-- Module      : CLAIR.Test.TypeChecker
-- Description : Tests for CLAIR.TypeChecker

module CLAIR.Test.TypeChecker where

import Test.Tasty
import Test.Tasty.HUnit

import CLAIR.Syntax
import CLAIR.TypeChecker
import CLAIR.TypeChecker.Types (Context(..), emptyContext, extend, ctxLookup, TypeError(..), prettyTypeError)
import CLAIR.Confidence (Confidence(..))

-- ============================================================================
-- Unit Tests
-- ============================================================================

-- | Test type inference for literals
test_literals :: TestTree
test_literals = testCase "Literal type inference" $ do
  let ctx = emptyContext

  case infer ctx (ELit (LNat 5)) of
    Right (TCResult ty _) -> assertEqual "Nat literal" (TBase TNat) ty
    Left err -> assertFailure $ "Failed: " ++ prettyTypeError err

  case infer ctx (ELit (LBool True)) of
    Right (TCResult ty _) -> assertEqual "Bool literal" (TBase TBool) ty
    Left err -> assertFailure $ "Failed: " ++ prettyTypeError err

-- | Test type inference for variables
test_variables :: TestTree
test_variables = testCase "Variable type inference" $ do
  let ctx = extend (name "x") (TBase TNat) emptyContext

  case infer ctx (EVar (name "x")) of
    Right (TCResult ty _) -> assertEqual "Variable x" (TBase TNat) ty
    Left err -> assertFailure $ "Failed: " ++ prettyTypeError err

  case infer ctx (EVar (name "y")) of
    Left (UnboundVar _) -> return ()  -- Expected
    Right _ -> assertFailure "Should fail: unbound variable"
    Left err -> assertFailure $ "Wrong error: " ++ prettyTypeError err

-- | Test type inference for functions
test_functions :: TestTree
test_functions = testCase "Function type inference" $ do
  let ctx = emptyContext
  let lam = ELam (name "x") (TBase TNat) (EVar (name "x"))

  case infer ctx lam of
    Right (TCResult ty _) ->
      assertEqual "λx:Nat. x" (TFun (TBase TNat) (TBase TNat)) ty
    Left err -> assertFailure $ "Failed: " ++ prettyTypeError err

-- | Test type checking for functions
test_check_function :: TestTree
test_check_function = testCase "Function type checking" $ do
  let ctx = emptyContext
  let lam = ELam (name "x") (TBase TNat) (EVar (name "x"))
  let ty = TFun (TBase TNat) (TBase TNat)

  case check ctx lam ty of
    Right _ -> return ()  -- Success
    Left err -> assertFailure $ "Failed: " ++ prettyTypeError err

-- | Test type checking with mismatched types
test_type_mismatch :: TestTree
test_type_mismatch = testCase "Type mismatch" $ do
  let ctx = emptyContext
  let lam = ELam (name "x") (TBase TNat) (EVar (name "x"))
  let ty = TFun (TBase TBool) (TBase TBool)

  case check ctx lam ty of
    Right _ -> assertFailure "Should fail: type mismatch"
    Left (TypeMismatch{}) -> return ()  -- Expected
    Left err -> assertFailure $ "Wrong error: " ++ prettyTypeError err

-- | Test belief type inference
test_belief :: TestTree
test_belief = testCase "Belief type inference" $ do
  let ctx = emptyContext
  let b = EBelief (Belief (ELit (LNat 5)) (Confidence 0.8) JNone INone PNone)

  case infer ctx b of
    Right (TCResult ty _) -> case ty of
      TBelief (Confidence 0.8) (TBase TNat) -> return ()
      _ -> assertFailure $ "Wrong type: " ++ show ty
    Left err -> assertFailure $ "Failed: " ++ prettyTypeError err

-- | Test box (self-reference) type inference
test_box :: TestTree
test_box = testCase "Box type inference" $ do
  let ctx = emptyContext
  let box = EBox (Confidence 0.7) (ELit (LBool True))

  case infer ctx box of
    Right (TCResult ty _) -> case ty of
      TBelief (Confidence 0.7) (TBase TBool) -> return ()
      _ -> assertFailure $ "Wrong type: " ++ show ty
    Left err -> assertFailure $ "Failed: " ++ prettyTypeError err

-- ============================================================================
-- Test Suite
-- ============================================================================

-- | Main test suite for TypeChecker module
testTypeChecker :: TestTree
testTypeChecker = testGroup "CLAIR.TypeChecker"
  [ test_literals
  , test_variables
  , test_functions
  , test_check_function
  , test_type_mismatch
  , test_belief
  , test_box
  ]
