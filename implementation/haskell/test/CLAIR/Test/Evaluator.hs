{-# LANGUAGE GADTs #-}

-- |
-- Module      : CLAIR.Test.Evaluator
-- Description : Tests for CLAIR.Evaluator

module CLAIR.Test.Evaluator where

import Test.Tasty
import Test.Tasty.HUnit

import CLAIR.Syntax
import CLAIR.Evaluator (eval, evalWithFuel, emptyEnv, extendEnv, Value(..), BeliefValue(..), EvalError(..), prettyEvalError)
import CLAIR.Confidence (Confidence(..))

-- ============================================================================
-- Unit Tests
-- ============================================================================

-- | Test evaluation of literals
test_literals :: TestTree
test_literals = testCase "Literal evaluation" $ do
  case eval (ELit (LNat 5)) of
    Right (VNat 5) -> return ()
    Right v -> assertFailure $ "Wrong value: " ++ show v
    Left err -> assertFailure $ "Failed: " ++ prettyEvalError err

  case eval (ELit (LBool True)) of
    Right (VBool True) -> return ()
    Right v -> assertFailure $ "Wrong value: " ++ show v
    Left err -> assertFailure $ "Failed: " ++ prettyEvalError err

-- | Test variable lookup
test_variables :: TestTree
test_variables = testCase "Variable evaluation" $ do
  let env = extendEnv (name "x") (VNat 42) emptyEnv
  case evalWithFuel 1000 env (EVar (name "x")) of
    Right (VNat 42) -> return ()
    Right v -> assertFailure $ "Wrong value: " ++ show v
    Left err -> assertFailure $ "Failed: " ++ prettyEvalError err

-- | Test function application
test_application :: TestTree
test_application = testCase "Function application" $ do
  let lam = ELam (name "x") (TBase TNat) (EVar (name "x"))
  let app = EApp lam (ELit (LNat 10))

  case eval app of
    Right (VNat 10) -> return ()
    Right v -> assertFailure $ "Wrong value: " ++ show v
    Left err -> assertFailure $ "Failed: " ++ prettyEvalError err

-- | Test primitive operations
test_primitives :: TestTree
test_primitives = testCase "Primitive operations" $ do
  let add = EPrim OAdd (ELit (LNat 3)) (ELit (LNat 4))

  case eval add of
    Right (VNat 7) -> return ()
    Right v -> assertFailure $ "Wrong value: " ++ show v
    Left err -> assertFailure $ "Failed: " ++ prettyEvalError err

  let mul = EPrim OMul (ELit (LNat 5)) (ELit (LNat 6))

  case eval mul of
    Right (VNat 30) -> return ()
    Right v -> assertFailure $ "Wrong value: " ++ show v
    Left err -> assertFailure $ "Failed: " ++ prettyEvalError err

-- | Test division by zero
test_div_by_zero :: TestTree
test_div_by_zero = testCase "Division by zero" $ do
  let divByZero = EPrim ODiv (ELit (LNat 10)) (ELit (LNat 0))

  case eval divByZero of
    Left EDivByZero -> return ()  -- Expected
    Right v -> assertFailure $ "Should fail: division by zero, got " ++ show v
    Left err -> assertFailure $ "Wrong error: " ++ prettyEvalError err

-- | Test comparison operations
test_comparison :: TestTree
test_comparison = testCase "Comparison operations" $ do
  let lt = EPrim OLt (ELit (LNat 3)) (ELit (LNat 5))

  case eval lt of
    Right (VBool True) -> return ()
    Right v -> assertFailure $ "Wrong value: " ++ show v
    Left err -> assertFailure $ "Failed: " ++ prettyEvalError err

  let gt = EPrim OGt (ELit (LNat 10)) (ELit (LNat 5))

  case eval gt of
    Right (VBool True) -> return ()
    Right v -> assertFailure $ "Wrong value: " ++ show v
    Left err -> assertFailure $ "Failed: " ++ prettyEvalError err

-- | Test boolean operations
test_boolean :: TestTree
test_boolean = testCase "Boolean operations" $ do
  let andOp = EPrim OAnd (ELit (LBool True)) (ELit (LBool False))

  case eval andOp of
    Right (VBool False) -> return ()
    Right v -> assertFailure $ "Wrong value: " ++ show v
    Left err -> assertFailure $ "Failed: " ++ prettyEvalError err

  let orOp = EPrim OOr (ELit (LBool True)) (ELit (LBool False))

  case eval orOp of
    Right (VBool True) -> return ()
    Right v -> assertFailure $ "Wrong value: " ++ show v
    Left err -> assertFailure $ "Failed: " ++ prettyEvalError err

-- | Test box (self-reference)
test_box :: TestTree
test_box = testCase "Box evaluation" $ do
  let box = EBox (Confidence 0.9) (ELit (LBool True))

  case eval box of
    Right (VBelief bv) -> do
      assertEqual "Confidence" (Confidence 0.9) (bvConf bv)
      assertEqual "Value" (VBool True) (bvValue bv)
    Right v -> assertFailure $ "Wrong value: " ++ show v
    Left err -> assertFailure $ "Failed: " ++ prettyEvalError err

-- | Test nested application
test_nested :: TestTree
test_nested = testCase "Nested application" $ do
  let inc = ELam (name "x") (TBase TNat) (EPrim OAdd (EVar (name "x")) (ELit (LNat 1)))
  let app = EApp (EApp inc (ELit (LNat 5))) (ELit (LNat 2))
  -- This should be: (inc 5) 2 = ((λx. x+1) 5) 2 = 6 2 (error)
  -- Let's do a proper nested lambda instead
  let add = ELam (name "x") (TBase TNat) (ELam (name "y") (TBase TNat) (EPrim OAdd (EVar (name "x")) (EVar (name "y"))))
  let app2 = EApp (EApp add (ELit (LNat 3))) (ELit (LNat 4))

  case eval app2 of
    Right (VNat 7) -> return ()
    Right v -> assertFailure $ "Wrong value: " ++ show v
    Left err -> assertFailure $ "Failed: " ++ prettyEvalError err

-- ============================================================================
-- Test Suite
-- ============================================================================

-- | Main test suite for Evaluator module
testEvaluator :: TestTree
testEvaluator = testGroup "CLAIR.Evaluator"
  [ test_literals
  , test_variables
  , test_application
  , test_primitives
  , test_div_by_zero
  , test_comparison
  , test_boolean
  , test_box
  , test_nested
  ]
