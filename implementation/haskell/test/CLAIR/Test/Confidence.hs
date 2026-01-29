{-# LANGUAGE GADTs #-}

-- |
-- Module      : CLAIR.Test.Confidence
-- Description : Tests for CLAIR.Confidence

module CLAIR.Test.Confidence where

import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit

import qualified CLAIR.Confidence as C
import CLAIR.Confidence (Confidence(..), Defeat(..), oplus, otimes, oneg, undercut, rebut, squareDiscount, linearDiscount, isNormalized)
import Data.Either (isRight)

-- ============================================================================
-- Properties
-- ============================================================================

-- | oplus is commutative: a ⊕ b = b ⊕ a
prop_oplus_commutative :: C.Confidence -> C.Confidence -> Bool
prop_oplus_commutative a b = oplus a b == oplus b a

-- | oplus is associative: (a ⊕ b) ⊕ c = a ⊕ (b ⊕ c)
prop_oplus_associative :: C.Confidence -> C.Confidence -> C.Confidence -> Bool
prop_oplus_associative a b c = oplus (oplus a b) c == oplus a (oplus b c)

-- | oplus has identity 0: a ⊕ 0 = a
prop_oplus_identity :: C.Confidence -> Bool
prop_oplus_identity a = oplus a (C.Confidence 0) == a

-- | otimes is commutative: a ⊗ b = b ⊗ a
prop_otimes_commutative :: C.Confidence -> C.Confidence -> Bool
prop_otimes_commutative a b = otimes a b == otimes b a

-- | otimes is associative: (a ⊗ b) ⊗ c = a ⊗ (b ⊗ c)
prop_otimes_associative :: C.Confidence -> C.Confidence -> C.Confidence -> Bool
prop_otimes_associative a b c = otimes (otimes a b) c == otimes a (otimes b c)

-- | otimes has identity 1: a ⊗ 1 = a
prop_otimes_identity :: C.Confidence -> Bool
prop_otimes_identity a = otimes a (C.Confidence 1) == a

-- | otimes annihilator 0: a ⊗ 0 = 0
prop_otimes_annihilator :: C.Confidence -> Bool
prop_otimes_annihilator a = otimes a (C.Confidence 0) == C.Confidence 0

-- | negation is involutive: ¬(¬a) = a
prop_oneg_involution :: C.Confidence -> Bool
prop_oneg_involution a = oneg (oneg a) == a

-- | undercut(0, c) = c (no defeat)
prop_undercut_zero :: C.Confidence -> Bool
prop_undercut_zero c = undercut (Defeat 0) c == c

-- | undercut(1, c) = 0 (complete defeat)
prop_undercut_one :: C.Confidence -> Property
prop_undercut_one c = (c > C.Confidence 0) ==> undercut (Defeat 1) c == C.Confidence 0

-- | rebut with equal strength gives 0.5
prop_rebut_equal :: Property
prop_rebut_equal = forAll (choose (0.1, 0.9)) $ \d ->
  rebut (Defeat d) (C.Confidence d) (C.Confidence 1) == C.Confidence 0.5

-- | Confidence is always in [0,1]
prop_confidence_normalized :: C.Confidence -> Bool
prop_confidence_normalized = isNormalized

-- ============================================================================
-- Unit Tests
-- ============================================================================

-- | Test specific confidence values
test_confidence_values :: TestTree
test_confidence_values = testCase "Confidence values" $ do
  let c0 = C.Confidence 0
  let c1 = C.Confidence 1
  let c05 = C.Confidence 0.5

  -- oplus tests
  assertEqual "0 ⊕ 0 = 0" (C.Confidence 0) (oplus c0 c0)
  assertEqual "1 ⊕ 0 = 1" c1 (oplus c1 c0)
  assertEqual "0.5 ⊕ 0.5 = 0.75" (C.Confidence 0.75) (oplus c05 c05)

  -- otimes tests
  assertEqual "0 ⊗ 0 = 0" c0 (otimes c0 c0)
  assertEqual "1 ⊗ 1 = 1" c1 (otimes c1 c1)
  assertEqual "0.5 ⊗ 0.5 = 0.25" (C.Confidence 0.25) (otimes c05 c05)

  -- oneg tests
  assertEqual "¬0 = 1" c1 (oneg c0)
  assertEqual "¬1 = 0" c0 (oneg c1)
  assertEqual "¬0.5 = 0.5" c05 (oneg c05)

-- | Test undercut operation
test_undercut :: TestTree
test_undercut = testCase "Undercut" $ do
  let c = C.Confidence 0.8
  assertEqual "undercut(0, 0.8) = 0.8" c (undercut (Defeat 0) c)
  assertEqual "undercut(0.5, 0.8) = 0.4" (C.Confidence 0.4) (undercut (Defeat 0.5) c)
  assertEqual "undercut(1, 0.8) = 0" (C.Confidence 0) (undercut (Defeat 1) c)

-- | Test discount functions
test_discount :: TestTree
test_discount = testCase "Discount functions" $ do
  assertEqual "squareDiscount(0) = 0" (C.Confidence 0) (squareDiscount (C.Confidence 0))
  assertEqual "squareDiscount(1) = 1" (C.Confidence 1) (squareDiscount (C.Confidence 1))
  assertEqual "squareDiscount(0.5) = 0.25" (C.Confidence 0.25) (squareDiscount (C.Confidence 0.5))

  assertEqual "linearDiscount(0) = 0" (C.Confidence 0) (linearDiscount (C.Confidence 0))
  assertEqual "linearDiscount(1) = 0.5" (C.Confidence 0.5) (linearDiscount (C.Confidence 1))

-- ============================================================================
-- Test Suite
-- ============================================================================

-- | Main test suite for Confidence module
testConfidence :: TestTree
testConfidence = testGroup "CLAIR.Confidence"
  [ testProperty "oplus commutative" prop_oplus_commutative
  , testProperty "oplus associative" prop_oplus_associative
  , testProperty "oplus identity" prop_oplus_identity
  , testProperty "otimes commutative" prop_otimes_commutative
  , testProperty "otimes associative" prop_otimes_associative
  , testProperty "otimes identity" prop_otimes_identity
  , testProperty "otimes annihilator" prop_otimes_annihilator
  , testProperty "oneg involution" prop_oneg_involution
  , testProperty "undercut zero defeat" prop_undercut_zero
  , testProperty "undercut complete defeat" prop_undercut_one
  , testProperty "rebut equal strength" prop_rebut_equal
  , testProperty "confidence normalized" prop_confidence_normalized
  , test_confidence_values
  , test_undercut
  , test_discount
  ]
