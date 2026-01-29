{-# LANGUAGE GADTs #-}

-- |
-- Module      : CLAIR.Internal.Utils
-- Description : Internal utilities for CLAIR implementation

module CLAIR.Internal.Utils where

import qualified Data.Text as T

-- | Show Text without quotes (for debugging)
showText :: T.Text -> String
showText = T.unpack
