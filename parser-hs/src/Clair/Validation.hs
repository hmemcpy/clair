{-# LANGUAGE OverloadedStrings #-}

module Clair.Validation
  ( validateBelief
  , validateBeliefs
  , validateDAG
  , checkReferencesExist
  , buildBeliefStore
  ) where

import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import           Data.Set        (Set)
import qualified Data.Set        as S
import           Data.Text       (Text)

import           Clair.Types

-- | Validate a single belief
validateBelief :: Belief -> ValidationResult
validateBelief b = 
  checkConfidenceBounds (beliefConfidence b) <>
  checkLevelBounds (beliefLevel b)

-- | Check confidence is in valid bounds [0, 1]
checkConfidenceBounds :: Confidence -> ValidationResult
checkConfidenceBounds (Confidence c)
  | c >= 0 && c <= 1 = Valid
  | otherwise        = Invalid [InvalidConfidence c]

-- | Check level is non-negative
checkLevelBounds :: Level -> ValidationResult
checkLevelBounds (Level n)
  | n >= 0    = Valid
  | otherwise = Invalid [InvalidLevel n]

-- | Build dependency graph from beliefs
buildDependencyGraph :: [Belief] -> Map BeliefId (Set BeliefId)
buildDependencyGraph beliefs =
  M.fromList $ map (\b -> (beliefId b, getDependencies b)) beliefs
  where
    getDependencies b = S.fromList $ map unJustification $ beliefJustifications b

-- | Detect cycles using DFS
detectCycles :: Map BeliefId (Set BeliefId) -> Maybe [BeliefId]
detectCycles graph = go [] S.empty (M.keysSet graph)
  where
    go path visited remaining
      | S.null remaining = Nothing
      | otherwise =
          let current = S.findMin remaining
          in dfs current path visited (S.delete current remaining)
    
    dfs node path visited remaining
      | node `elem` path = Just $ dropWhile (/= node) (path ++ [node])
      | node `S.member` visited = go path (S.insert node visited) remaining
      | otherwise =
          case M.lookup node graph of
            Nothing -> go (path ++ [node]) (S.insert node visited) remaining
            Just deps ->
              let depsList = S.toList deps
              in checkDeps depsList (node:path) (S.insert node visited) remaining
    
    checkDeps [] path' visited' remaining' = go path' visited' remaining'
    checkDeps (d:ds) path' visited' remaining' =
      case dfs d path' visited' remaining' of
        Just cycle -> Just cycle
        Nothing    -> checkDeps ds path' visited' remaining'

-- | Validate that beliefs form a DAG (no cycles)
validateDAG :: [Belief] -> ValidationResult
validateDAG beliefs =
  let graph = buildDependencyGraph beliefs
  in case detectCycles graph of
       Nothing -> Valid
       Just cycle -> Invalid [CycleDetected cycle]

-- | Check for duplicate IDs
checkDuplicateIds :: [Belief] -> ValidationResult
checkDuplicateIds beliefs =
  let ids = map beliefId beliefs
      grouped = foldr (\bid m -> M.insertWith (++) bid [bid] m) M.empty ids
      dups = M.filter (\v -> length v > 1) grouped
  in if M.null dups
     then Valid
     else Invalid $ map DuplicateId (M.keys dups)

-- | Check that all justifications reference existing beliefs
checkReferencesExist :: Belief -> BeliefStore -> ValidationResult
checkReferencesExist belief store =
  let refs = map unJustification $ beliefJustifications belief
      missing = filter (\r -> lookupBelief r store == Nothing) refs
  in if null missing
     then Valid
     else Invalid $ map (MissingReference (beliefId belief)) missing

-- | Validate a list of beliefs
validateBeliefs :: [Belief] -> ValidationResult
validateBeliefs beliefs = 
  let individual = mconcat $ map validateBelief beliefs
      dagCheck = validateDAG beliefs
      duplicateCheck = checkDuplicateIds beliefs
  in individual <> dagCheck <> duplicateCheck

-- | Build a belief store with validation
buildBeliefStore :: [Belief] -> Either [ValidationError] BeliefStore
buildBeliefStore beliefs =
  case validateBeliefs beliefs of
    Valid      -> Right $ foldr addBelief emptyBeliefStore beliefs
    Invalid es -> Left es
