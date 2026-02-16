{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE OverloadedStrings #-}

module Clair.Types
  ( -- * Core Types
    BeliefId(..)
  , Confidence(..)
  , Level(..)
  , Source(..)
  , Justification(..)
  , Belief(..)
  , BeliefStore(..)
  , ValidationError(..)
  , ValidationResult(..)
  , ParsedContent(..)
    -- * Constructors
  , mkConfidence
  , mkConfidenceUnsafe
  , mkLevel
  , mkBeliefId
  , emptyBeliefStore
  , addBelief
  , lookupBelief
  , getAllBeliefs
    -- * Predicates
  , isValidConfidence
  , isUserSource
  , isSelfSource
  , isFileSource
  , isModelSource
  ) where

import           Data.Aeson      (FromJSON, ToJSON, object, pairs, parseJSON,
                                  toEncoding, toJSON, withObject, withText,
                                  (.:), (.=))
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import           Data.Scientific (Scientific, toRealFloat)
import           Data.Text       (Text)
import qualified Data.Text       as T
import           GHC.Generics    (Generic)

-- | Unique identifier for a belief (e.g., "b1", "b2")
newtype BeliefId = BeliefId { unBeliefId :: Text }
  deriving (Eq, Ord, Generic, Show)

instance ToJSON BeliefId where
  toJSON = toJSON . unBeliefId
  toEncoding = toEncoding . unBeliefId

instance FromJSON BeliefId where
  parseJSON = withText "BeliefId" (pure . BeliefId)

-- | Create a BeliefId from Text
mkBeliefId :: Text -> BeliefId
mkBeliefId = BeliefId

-- | Confidence value in [0, 1]
newtype Confidence = Confidence { unConfidence :: Scientific }
  deriving (Eq, Ord, Generic, Show)

instance ToJSON Confidence where
  toJSON = toJSON . unConfidence
  toEncoding = toEncoding . unConfidence

instance FromJSON Confidence where
  parseJSON v = do
    sci <- parseJSON v
    if isValidConfidence sci
      then pure $ Confidence sci
      else fail $ "Confidence must be in [0, 1], got: " ++ show sci

-- | Check if a scientific number is a valid confidence value
isValidConfidence :: Scientific -> Bool
isValidConfidence s = s >= 0 && s <= 1

-- | Smart constructor for confidence (returns Nothing if out of bounds)
mkConfidence :: Scientific -> Maybe Confidence
mkConfidence s
  | isValidConfidence s = Just $ Confidence s
  | otherwise           = Nothing

-- | Unsafe constructor for confidence (use with caution)
mkConfidenceUnsafe :: Scientific -> Confidence
mkConfidenceUnsafe = Confidence

-- | Level of belief (L0, L1, L2, ...)
newtype Level = Level { unLevel :: Int }
  deriving (Eq, Ord, Generic, Show)

instance ToJSON Level where
  toJSON = toJSON . unLevel
  toEncoding = toEncoding . unLevel

instance FromJSON Level where
  parseJSON v = Level <$> parseJSON v

-- | Create a level from an integer
mkLevel :: Int -> Level
mkLevel = Level

-- | Source of a belief
data Source
  = SourceUser              -- ^ @user
  | SourceSelf              -- ^ @self
  | SourceFile FilePath     -- ^ @file:path
  | SourceModel Text        -- ^ @model:name
  deriving (Eq, Generic, Show)

instance ToJSON Source where
  toJSON SourceUser     = "user"
  toJSON SourceSelf     = "self"
  toJSON (SourceFile p) = object ["type" .= ("file" :: Text), "path" .= p]
  toJSON (SourceModel n) = object ["type" .= ("model" :: Text), "name" .= n]
  
  toEncoding SourceUser     = toEncoding ("user" :: Text)
  toEncoding SourceSelf     = toEncoding ("self" :: Text)
  toEncoding (SourceFile p) = pairs $ "type" .= ("file" :: Text) <> "path" .= p
  toEncoding (SourceModel n) = pairs $ "type" .= ("model" :: Text) <> "name" .= n

instance FromJSON Source where
  parseJSON = withText "Source" $ \t ->
    case t of
      "user" -> pure SourceUser
      "self" -> pure SourceSelf
      _      -> fail $ "Unknown source: " ++ T.unpack t

-- | Source predicates
isUserSource :: Source -> Bool
isUserSource SourceUser = True
isUserSource _          = False

isSelfSource :: Source -> Bool
isSelfSource SourceSelf = True
isSelfSource _          = False

isFileSource :: Source -> Bool
isFileSource (SourceFile _) = True
isFileSource _              = False

isModelSource :: Source -> Bool
isModelSource (SourceModel _) = True
isModelSource _               = False

-- | Justification reference to another belief
newtype Justification = Justification { unJustification :: BeliefId }
  deriving (Eq, Ord, Generic, Show)

instance ToJSON Justification where
  toJSON = toJSON . unJustification
  toEncoding = toEncoding . unJustification

instance FromJSON Justification where
  parseJSON v = Justification <$> parseJSON v

-- | The content of a belief (can be plain text or derived)
data ParsedContent
  = PlainContent Text                    -- ^ "content here"
  | DerivedContent [Justification] Text  -- ^ <b1 "derived content"
  deriving (Eq, Generic, Show)

instance ToJSON ParsedContent where
  toJSON (PlainContent t) = object
    [ "type"    .= ("plain" :: Text)
    , "content" .= t
    ]
  toJSON (DerivedContent refs t) = object
    [ "type"    .= ("derived" :: Text)
    , "references" .= refs
    , "content" .= t
    ]
  
  toEncoding (PlainContent t) = pairs $
    "type"    .= ("plain" :: Text) <>
    "content" .= t
  toEncoding (DerivedContent refs t) = pairs $
    "type"       .= ("derived" :: Text) <>
    "references" .= refs <>
    "content"    .= t

instance FromJSON ParsedContent where
  parseJSON = withObject "ParsedContent" $ \o -> do
    ty <- o .: "type"
    case (ty :: Text) of
      "plain"   -> PlainContent <$> o .: "content"
      "derived" -> DerivedContent <$> o .: "references" <*> o .: "content"
      _         -> fail $ "Unknown content type: " ++ T.unpack ty

-- | A belief with all its attributes
data Belief = Belief
  { beliefId       :: !BeliefId
  , beliefConfidence :: !Confidence
  , beliefLevel    :: !Level
  , beliefSource   :: !Source
  , beliefJustifications :: ![Justification]
  , beliefContent  :: !ParsedContent
  } deriving (Eq, Generic, Show)

instance ToJSON Belief where
  toJSON b = object
    [ "id"            .= beliefId b
    , "confidence"    .= beliefConfidence b
    , "level"         .= beliefLevel b
    , "source"        .= beliefSource b
    , "justifications".= beliefJustifications b
    , "content"       .= beliefContent b
    ]
  
  toEncoding b = pairs $
    "id"             .= beliefId b <>
    "confidence"     .= beliefConfidence b <>
    "level"          .= beliefLevel b <>
    "source"         .= beliefSource b <>
    "justifications" .= beliefJustifications b <>
    "content"        .= beliefContent b

instance FromJSON Belief where
  parseJSON = withObject "Belief" $ \o -> Belief
    <$> o .: "id"
    <*> o .: "confidence"
    <*> o .: "level"
    <*> o .: "source"
    <*> o .: "justifications"
    <*> o .: "content"

-- | Store for managing beliefs
newtype BeliefStore = BeliefStore
  { unBeliefStore :: Map BeliefId Belief
  } deriving (Eq, Show)

-- | Create an empty belief store
emptyBeliefStore :: BeliefStore
emptyBeliefStore = BeliefStore M.empty

-- | Add a belief to the store
addBelief :: Belief -> BeliefStore -> BeliefStore
addBelief b (BeliefStore m) = BeliefStore $ M.insert (beliefId b) b m

-- | Look up a belief by ID
lookupBelief :: BeliefId -> BeliefStore -> Maybe Belief
lookupBelief bid (BeliefStore m) = M.lookup bid m

-- | Get all beliefs from the store
getAllBeliefs :: BeliefStore -> [Belief]
getAllBeliefs (BeliefStore m) = M.elems m

-- | Validation errors
data ValidationError
  = DuplicateId BeliefId
  | InvalidConfidence Scientific
  | InvalidLevel Int
  | MissingReference BeliefId BeliefId  -- ^ belief id, missing reference id
  | CycleDetected [BeliefId]
  | InvalidSource Text
  deriving (Eq, Show)

-- | Result of validation
data ValidationResult
  = Valid
  | Invalid [ValidationError]
  deriving (Eq, Show)

instance Semigroup ValidationResult where
  Valid <> x = x
  x <> Valid = x
  (Invalid es1) <> (Invalid es2) = Invalid (es1 ++ es2)

instance Monoid ValidationResult where
  mempty = Valid
