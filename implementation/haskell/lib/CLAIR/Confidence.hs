{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

-- |
-- Module      : CLAIR.Confidence
-- Description : Confidence algebra for CLAIR
--
-- CLAIR confidence values represent calibrated reliability in [0,1].
--
-- Semantics:
--   - c = 1: Certain/True
--   - c = 0: Certainly False
--   - 0 < c < 1: Degrees of calibrated reliability
--
-- Key properties:
--   - Confidence is NOT probability (though operators overlap)
--   - Independence assumptions are required for ⊕ aggregation
--   - Undercut attenuates by multiplying (1-d)
--   - Rebut normalizes by c_for / (c_for + c_against)

module CLAIR.Confidence
  ( -- * Confidence Type
    Confidence(..)
  , toDouble
  , fromDouble
  , fromRationalConfidence
    -- * Operations
  , oplus
  , otimes
  , oneg
  , oplusAssoc
  , otimesAssoc
    -- * Defeat Operations
  , Defeat(..)
  , undercut
  , rebut
    -- * Discount Functions
  , DiscountFn
  , squareDiscount
  , linearDiscount
    -- * Properties
  , isNormalized
  , clamp
  ) where

import Data.Aeson (ToJSON, FromJSON)
import Data.Ratio
import GHC.Generics (Generic)
import Test.QuickCheck (Arbitrary(..), choose)

-- | A confidence value in the closed interval [0,1].
--
-- The 'Double' representation is used for computational efficiency.
-- For production use, consider using 'Rational' or arbitrary-precision types.
newtype Confidence = Confidence Double
  deriving (Eq, Ord, Generic, ToJSON, FromJSON)

-- | Show confidence with 3 decimal places
instance Show Confidence where
  showsPrec n (Confidence c) =
    showParen (n > 10) $
      showString "Confidence " . shows (fromIntegral (round (c * 1000)) / 1000 :: Double)

-- | Convert Confidence to Double
toDouble :: Confidence -> Double
toDouble (Confidence c) = c

-- | Unsafe conversion from Double.
-- Use 'fromRational' or 'clamp' for safe conversion.
fromDouble :: Double -> Confidence
fromDouble = Confidence

-- | Convert from Rational, automatically clamping to [0,1].
fromRationalConfidence :: Rational -> Confidence
fromRationalConfidence r = clamp (fromRational' r)
  where
    fromRational' :: Rational -> Double
    fromRational' x = fromInteger (numerator x) / fromInteger (denominator x)

-- | Clamp a Double value to the valid range [0,1].
clamp :: Double -> Confidence
clamp c
  | c < 0     = Confidence 0
  | c > 1     = Confidence 1
  | otherwise = Confidence c

-- | QuickCheck instance: generate confidence in [0,1]
instance Arbitrary Confidence where
  arbitrary = Confidence <$> choose (0, 1)

-- | Check if a Confidence is in valid range [0,1]
isNormalized :: Confidence -> Bool
isNormalized (Confidence c) = c >= 0 && c <= 1

-- ============================================================================
-- Operations
-- ============================================================================

-- | Probabilistic sum (independence aggregation):
--   a ⊕ b = 1 - (1-a)(1-b) = a + b - ab
--
-- Properties:
--   - Commutative: a ⊕ b = b ⊕ a
--   - Associative: (a ⊕ b) ⊕ c = a ⊕ (b ⊕ c)
--   - Identity: a ⊕ 0 = a
--   - Idempotent on 1: a ⊕ 1 = 1
--
-- Assumes: sources of evidence are conditionally independent
oplus :: Confidence -> Confidence -> Confidence
oplus (Confidence a) (Confidence b) = clamp (a + b - a * b)

-- | Product t-norm:
--   a ⊗ b = a * b
--
-- Properties:
--   - Commutative: a ⊗ b = b ⊗ a
--   - Associative: (a ⊗ b) ⊗ c = a ⊗ (b ⊗ c)
--   - Identity: a ⊗ 1 = a
--   - Annihilator: a ⊗ 0 = 0
otimes :: Confidence -> Confidence -> Confidence
otimes (Confidence a) (Confidence b) = clamp (a * b)

-- | Negation (standard involutive negation):
--   ¬a = 1 - a
--
-- Properties:
--   - Involution: ¬(¬a) = a
--   - ¬0 = 1
--   - ¬1 = 0
--   - ¬0.5 = 0.5
oneg :: Confidence -> Confidence
oneg (Confidence a) = clamp (1 - a)

-- | N-ary associative oplus (folds from left)
oplusAssoc :: [Confidence] -> Confidence
oplusAssoc = foldr oplus (Confidence 0)

-- | N-ary associative otimes (folds from left)
otimesAssoc :: [Confidence] -> Confidence
otimesAssoc = foldr otimes (Confidence 1)

-- ============================================================================
-- Defeat Operations
-- ============================================================================

-- | A defeat value d ∈ [0,1] represents the strength of a defeater.
--   - d = 0: No defeat
--   - d = 1: Complete defeat (zeroes out target)
newtype Defeat = Defeat Double
  deriving (Eq, Ord, Show, Generic, ToJSON, FromJSON)

instance Arbitrary Defeat where
  arbitrary = Defeat <$> choose (0, 1)

-- | Apply an undercut defeat: multiply by (1-d).
--
--   undercut(d, c) = c * (1-d)
--
-- Properties:
--   - d = 0 → no change: c * 1 = c
--   - d = 1 → complete defeat: c * 0 = 0
--   - Monotonic: larger d → smaller result
--
-- Rationale: Undercut attacks the connection between evidence
-- and conclusion, reducing the evidential support multiplicatively.
undercut :: Defeat -> Confidence -> Confidence
undercut (Defeat d) (Confidence c) = clamp (c * (1 - d))

-- | Apply a rebut defeat with normalization.
--
--   rebut(d_for, d_against) = c_for / (c_for + c_against)
--
-- where c_against = d * (1 - c_for) represents the strength of
-- opposing evidence.
--
-- Properties:
--   - Returns value in [0,1]
--   - Equal strength for/against → 0.5
--   - Strong for, weak against → near 1
--   - Weak for, strong against → near 0
--
-- Limitation: This normalization collapses absolute strength -
-- both weak and strong balanced evidence map to similar ratios.
-- Consider uncertainty-preserving alternatives (subjective logic)
-- for production use.
rebut :: Defeat -> Confidence -> Confidence -> Confidence
rebut (Defeat d_strength) (Confidence c_for) (Confidence c_against_base) =
  -- c_against represents the effective strength of opposing evidence
  let c_against = d_strength * c_against_base
      total = c_for + c_against
  in if total == 0
     then Confidence 0.5  -- ignorance prior when no evidence
     else clamp (c_for / total)

-- ============================================================================
-- Discount Functions
-- ============================================================================

-- | A discount function reduces confidence in self-referential
-- soundness claims.
--
-- In CPL (Confidence-weighted Provability Logic), when a belief
-- references its own justification, we apply a discount:
--
--   □_c φ → □_{g(c)} φ
--
-- where g: [0,1] → [0,1] is strictly decreasing.
--
-- Recommended: g(c) = c² (square discount)
type DiscountFn = Confidence -> Confidence

-- | Square discount: g(c) = c²
--
-- Properties:
--   - g(0) = 0
--   - g(1) = 1
--   - g'(c) = 2c > 0 for c > 0 (strictly increasing)
--   - g(c) < c for 0 < c < 1 (discounting)
--
-- Rationale: The square function provides moderate discounting
-- that prevents bootstrapping while preserving high-confidence
-- self-endorsement for nearly-certain beliefs.
squareDiscount :: DiscountFn
squareDiscount (Confidence c) = clamp (c * c)

-- | Linear discount: g(c) = c / 2
--
-- Stronger discounting, useful for testing or conservative
-- self-reference handling.
linearDiscount :: DiscountFn
linearDiscount (Confidence c) = clamp (c / 2)
