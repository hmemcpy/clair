{-# LANGUAGE OverloadedStrings #-}

module Main where

import           Test.Hspec
import           Test.QuickCheck

import           Clair.Types
import           Clair.Parser
import           Clair.Validation

main :: IO ()
main = hspec $ do
  describe "Clair.Types" $ do
    it "creates valid confidence values" $ do
      mkConfidence 0.5 `shouldBe` Just (Confidence 0.5)
      mkConfidence 1.0 `shouldBe` Just (Confidence 1.0)
      mkConfidence 0.0 `shouldBe` Just (Confidence 0.0)
    
    it "rejects invalid confidence values" $ do
      mkConfidence 1.5 `shouldBe` Nothing
      mkConfidence (-0.1) `shouldBe` Nothing
  
  describe "Clair.Parser" $ do
    it "parses a simple belief" $ do
      let input = "b1 1.0 L0 @user \"test content\""
          result = parseBelief input
      case result of
        Right b -> do
          beliefId b `shouldBe` BeliefId "b1"
          beliefLevel b `shouldBe` Level 0
          beliefSource b `shouldBe` SourceUser
        Left e -> expectationFailure $ "Parse failed: " ++ e
    
    it "parses confidence with shorthand notation" $ do
      let input = "b1 .95 L0 @user \"content\""
          result = parseBelief input
      case result of
        Right b -> unConfidence (beliefConfidence b) `shouldBe` 0.95
        Left e -> expectationFailure $ "Parse failed: " ++ e
    
    it "parses derived content with justifications" $ do
      let input = "b2 .9 L1 @self <b1 \"derived\""
          result = parseBelief input
      case result of
        Right b -> do
          beliefSource b `shouldBe` SourceSelf
          length (beliefJustifications b) `shouldBe` 1
        Left e -> expectationFailure $ "Parse failed: " ++ e
    
    it "parses multiple beliefs" $ do
      let input = "b1 1.0 L0 @user \"first\"\nb2 .9 L1 @self \"second\""
          (beliefs, errors) = parseBeliefs input
      length beliefs `shouldBe` 2
      length errors `shouldBe` 0
    
    it "handles empty lines and comments" $ do
      let input = "# comment\nb1 1.0 L0 @user \"test\"\n\nb2 .9 L0 @self \"test2\""
          (beliefs, _) = parseBeliefs input
      length beliefs `shouldBe` 2
  
  describe "Clair.Validation" $ do
    it "validates confidence bounds" $ do
      let b = Belief (BeliefId "b1") (mkConfidenceUnsafe 0.5) (Level 0) 
                   SourceUser [] (PlainContent "test")
      validateBelief b `shouldBe` Valid
    
    it "detects duplicate IDs" $ do
      let b1 = Belief (BeliefId "b1") (mkConfidenceUnsafe 1.0) (Level 0) 
                    SourceUser [] (PlainContent "test1")
          b2 = Belief (BeliefId "b1") (mkConfidenceUnsafe 0.9) (Level 0) 
                    SourceUser [] (PlainContent "test2")
      case validateBeliefs [b1, b2] of
        Invalid errs -> any isDuplicateError errs `shouldBe` True
        Valid -> expectationFailure "Expected duplicate ID error"
    
    it "detects cycles" $ do
      let b1 = Belief (BeliefId "b1") (mkConfidenceUnsafe 1.0) (Level 0) 
                    SourceUser [Justification (BeliefId "b2")] (PlainContent "test1")
          b2 = Belief (BeliefId "b2") (mkConfidenceUnsafe 0.9) (Level 0) 
                    SourceUser [Justification (BeliefId "b1")] (PlainContent "test2")
      case validateDAG [b1, b2] of
        Invalid errs -> any isCycleError errs `shouldBe` True
        Valid -> expectationFailure "Expected cycle detection"

isDuplicateError :: ValidationError -> Bool
isDuplicateError (DuplicateId _) = True
isDuplicateError _ = False

isCycleError :: ValidationError -> Bool
isCycleError (CycleDetected _) = True
isCycleError _ = False
