{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- |
-- Module      : CLAIR.Evaluator
-- Description : Small-step operational semantics for CLAIR
--
-- Implements the small-step semantics:
--   e → e'
--
-- Evaluation uses a fuel parameter to ensure termination for
-- potentially non-terminating constructs (e.g., fixed-point
-- iteration for cyclic justification graphs).

module CLAIR.Evaluator
  ( -- * Evaluation
    eval
  , evalWithFuel
  , step
    -- * Values
  , Value(..)
  , BeliefValue(..)
  , fromValue
  , toValue
    -- * Environment
  , Env(..)
  , emptyEnv
  , extendEnv
    -- * Configuration
  , Config(..)
  , defaultConfig
    -- * Errors
  , EvalError(..)
  , prettyEvalError
    -- * Fuel
  , Fuel
  , initialFuel
  , consumeFuel
  , hasFuel
  ) where

import CLAIR.Syntax
import CLAIR.Confidence
import CLAIR.Confidence (fromRationalConfidence)
import qualified Data.Text as T
import Data.Ratio ((%))

-- ============================================================================
-- Fuel (Termination)
-- ============================================================================

-- | Fuel ensures termination of evaluation.
-- Each reduction step consumes one unit of fuel.
type Fuel = Int

-- | Initial fuel allocation (default: 1,000,000 steps).
initialFuel :: Fuel
initialFuel = 1000000

-- | Consume one unit of fuel.
consumeFuel :: Fuel -> Maybe Fuel
consumeFuel f
  | f > 0     = Just (f - 1)
  | otherwise = Nothing

-- | Check if fuel remains.
hasFuel :: Fuel -> Bool
hasFuel f = f > 0

-- ============================================================================
-- Values
-- ============================================================================

-- | Runtime values (weak head normal form).
data Value
  = -- | Closure: λx.e with environment
    VClosure Name Expr Env
  | -- | Natural number
    VNat Integer
  | -- | Boolean
    VBool Bool
  | -- | String
    VString T.Text
  | -- | Unit
    VUnit
  | -- | Belief value
    VBelief BeliefValue
  deriving (Eq, Show)

-- | Belief value at runtime.
data BeliefValue = BeliefValue
  { bvValue     :: Value
  , bvConf      :: Confidence
  ,bvJustify    :: [Value]  -- Flattened justification list
  , bvInvalidated :: Bool   -- Simple invalidated flag
  } deriving (Eq, Show)

-- | Environment mapping variables to values.
newtype Env = Env [(Name, Value)]
  deriving (Eq, Show)

-- | Empty environment.
emptyEnv :: Env
emptyEnv = Env []

-- | Extend environment.
extendEnv :: Name -> Value -> Env -> Env
extendEnv x v (Env env) = Env ((x, v) : env)

-- | Look up variable in environment.
lookupEnv :: Name -> Env -> Maybe Value
lookupEnv x (Env env) = lookup x env

-- ============================================================================
-- Evaluation Errors
-- ============================================================================

-- | Runtime errors during evaluation.
data EvalError
  = -- | Variable not found
    EUnboundVar Name
  | -- | Type error in operation
    ETypeError String
  | -- | Division by zero
    EDivByZero
  | -- | Out of fuel
    EOutOfFuel
  | -- | Stuck state (no reduction rule applies)
    EStuck Expr
  deriving (Eq, Show)

-- | Pretty print evaluation error.
prettyEvalError :: EvalError -> String
prettyEvalError = \case
  EUnboundVar x -> "Unbound variable: " ++ T.unpack (getName x)
  ETypeError msg -> "Type error: " ++ msg
  EDivByZero -> "Division by zero"
  EOutOfFuel -> "Evaluation ran out of fuel (possible infinite loop)"
  EStuck e -> "Stuck state: cannot reduce " ++ show e

-- ============================================================================
-- Evaluation Configuration
-- ============================================================================

-- | Configuration for evaluation.
data Config = Config
  { cfgMaxFuel :: Fuel  -- ^ Maximum fuel (steps)
  } deriving (Eq, Show)

-- | Default configuration.
defaultConfig :: Config
defaultConfig = Config initialFuel

-- ============================================================================
-- Single-Step Reduction
-- ============================================================================

-- | Single-step reduction: e → e'
--
-- Uses the small-step semantics rules from the CLAIR specification.
step :: Env -> Expr -> Either EvalError (Maybe Expr)
step env expr = case expr of
  -- E-Beta: (λx:τ.e) v → e[x := v]
  EApp (ELam varName _ty body) arg
    | isValue arg -> do
        v <- evalExpr env arg
        return (Just (subst varName v body))
    | otherwise -> do
        mArg' <- step env arg
        return (EApp (ELam varName _ty body) <$> mArg')

  EApp e1 e2 -> do
    me1' <- step env e1
    case me1' of
      Just e1New -> return (Just (EApp e1New e2))
      Nothing -> do
        me2' <- step env e2
        return (EApp e1 <$> me2')

  -- E-Prim: Reduce primitive operations
  EPrim op e1 e2
    | isValue e1 && isValue e2 -> evalPrimOp env op e1 e2
    | isValue e1 -> do
        me2' <- step env e2
        return (EPrim op e1 <$> me2')
    | otherwise -> do
        me1' <- step env e1
        case me1' of
          Just e1New -> return (Just (EPrim op e1New e2))
          Nothing -> return Nothing

  -- E-Belief: Evaluate belief content
  EBelief (Belief e c j i p) -> do
    me' <- step env e
    case me' of
      Just e' -> return (Just (EBelief (Belief e' c j i p)))
      Nothing -> do
        -- Fully evaluated: this is now a value, no further reduction
        return Nothing  -- EBelief is a value when its content is fully evaluated

  -- E-Box: □_c e → Belief(e, c, [], none, none)
  -- When e is fully evaluated, EBox becomes a value (no further reduction)
  EBox c e -> do
    me' <- step env e
    case me' of
      Just e' -> return (Just (EBox c e'))
      Nothing -> return Nothing  -- EBox is a value when its content is fully evaluated

  -- Already a value - no reduction
  _ | isValue expr -> return Nothing

  -- Variable - look up in environment
  EVar x -> case lookupEnv x env of
    Just v -> return (Just (toValue v))
    Nothing -> Left (EUnboundVar x)

  -- Type annotation - erase and continue
  EAnn e _ -> step env e

  -- Other constructs are stuck (shouldn't happen in well-typed programs)
  e -> Left (EStuck e)

-- ============================================================================
-- Evaluation
-- ============================================================================

-- | Evaluate an expression to a value.
eval :: Expr -> Either EvalError Value
eval = evalWithFuel initialFuel emptyEnv

-- | Evaluate with explicit fuel and environment.
evalWithFuel :: Fuel -> Env -> Expr -> Either EvalError Value
evalWithFuel fuel env expr = go fuel expr
  where
    go f e
      | not (hasFuel f) = Left EOutOfFuel
      | otherwise = case step env e of
          Left err -> Left err
          Right Nothing -> evalExpr env e  -- Done, convert to value
          Right (Just e') -> go (f-1) e'

-- | Evaluate expression in environment to value.
evalExpr :: Env -> Expr -> Either EvalError Value
evalExpr env = \case
  EVar x -> case lookupEnv x env of
    Just v -> Right v
    Nothing -> Left (EUnboundVar x)

  ELit (LNat n) -> Right (VNat n)
  ELit (LBool b) -> Right (VBool b)
  ELit (LString s) -> Right (VString s)
  ELit LUnit -> Right VUnit

  ELam{} -> Left (ETypeError "Cannot evaluate lambda to value directly (use evaluation)")
  EBox c e -> do
    v <- evalExpr env e
    return (VBelief (BeliefValue v c [] False))
  EBelief (Belief e c j i p) -> do
    v <- evalExpr env e
    let jVals = evalJustification env j
    let invd = isInvalidated env i
    return (VBelief (BeliefValue v c jVals invd))

  EAnn e _ -> evalExpr env e

  _ -> Left (ETypeError "Cannot evaluate to value directly")

-- ============================================================================
-- Primitive Operations
-- ============================================================================

-- | Evaluate primitive operation.
evalPrimOp :: Env -> Op -> Expr -> Expr -> Either EvalError (Maybe Expr)
evalPrimOp env op e1 e2 = do
  v1 <- evalExpr env e1
  v2 <- evalExpr env e2
  result <- evalPrimOpValues op v1 v2
  return (Just (toValue result))

-- | Evaluate primitive on values.
evalPrimOpValues :: Op -> Value -> Value -> Either EvalError Value
evalPrimOpValues = \case
  OAdd -> binOp (+) VNat
  OSub -> binOp (-) VNat
  OMul -> binOp (*) VNat
  ODiv -> binOpSafe Prelude.div VNat (== 0)
  OEq -> relOp (==)
  OLt -> relOp (<)
  OGt -> relOp (>)
  OAnd -> boolOp (&&)
  OOr -> boolOp (||)
  OImp -> boolOp (\a b -> not a || b)
  OPlus -> confidenceOp oplus
  OTimes -> confidenceOp otimes
  where
    binOp :: (Integer -> Integer -> Integer) -> (Integer -> Value) -> Value -> Value -> Either EvalError Value
    binOp f cons (VNat n1) (VNat n2) = Right (cons (f n1 n2))
    binOp _ _ _ _ = Left (ETypeError "Numeric operation requires Nat arguments")

    binOpSafe :: (Integer -> Integer -> Integer) -> (Integer -> Value) -> (Integer -> Bool) -> Value -> Value -> Either EvalError Value
    binOpSafe f cons check (VNat n1) (VNat n2)
      | check n2 = Left EDivByZero
      | otherwise = Right (cons (f n1 n2))
    binOpSafe _ _ _ _ _ = Left (ETypeError "Numeric operation requires Nat arguments")

    relOp :: (Integer -> Integer -> Bool) -> Value -> Value -> Either EvalError Value
    relOp op (VNat n1) (VNat n2) = Right (VBool (op n1 n2))
    relOp _ _ _ = Left (ETypeError "Comparison requires Nat arguments")

    boolOp :: (Bool -> Bool -> Bool) -> Value -> Value -> Either EvalError Value
    boolOp op (VBool b1) (VBool b2) = Right (VBool (op b1 b2))
    boolOp _ _ _ = Left (ETypeError "Boolean operation requires Bool arguments")

    confidenceOp :: (Confidence -> Confidence -> Confidence) -> Value -> Value -> Either EvalError Value
    confidenceOp op v1 v2 = case (fromValue' v1, fromValue' v2) of
      (Just c1, Just c2) -> Right (toConfidenceValue (op c1 c2))
      _ -> Left (ETypeError "Confidence operation requires confidence values")
      where
        fromValue' (VNat n) = Just (fromRationalConfidence (n % 1000))
        fromValue' _ = Nothing
        toConfidenceValue c = VNat (round (toDouble c * 1000))

-- ============================================================================
-- Substitution
-- ============================================================================

-- | Capture-avoiding substitution: e[x := v].
subst :: Name -> Value -> Expr -> Expr
subst x v = go
  where
    go (EVar y)
      | x == y = toValue v
      | otherwise = EVar y
    go (ELam y ty body)
      | x == y = ELam y ty body
      | otherwise = ELam y ty (go body)
    go (EApp e1 e2) = EApp (go e1) (go e2)
    go (EAnn e ty) = EAnn (go e) ty
    go (EBelief b) = EBelief (substBelief b)
    go (EBox c e) = EBox c (go e)
    go (EPrim op e1 e2) = EPrim op (go e1) (go e2)
    go e@ELit{} = e
    go e@EJustify{} = e
    go e@EInvalidate{} = e

    substBelief (Belief e c j i p) =
      Belief (go e) c j i p  -- Simplified: don't substitute in j,i,p

-- ============================================================================
-- Helpers
-- ============================================================================

-- | Check if expression is a value.
-- VBelief expressions are values when fully evaluated.
isValue :: Expr -> Bool
isValue = \case
  ELit{} -> True
  ELam{} -> True
  EBox{} -> True  -- Box expressions are values (syntactic sugar for Belief)
  EVar{} -> False  -- Variables need to be looked up
  EBelief{} -> True  -- Belief expressions are values (only created when content is a value)
  _ -> False

-- | Convert Value to Expr.
toValue :: Value -> Expr
toValue = \case
  VClosure{} -> error "Cannot convert closure to expression"
  VNat n -> ELit (LNat n)
  VBool b -> ELit (LBool b)
  VString s -> ELit (LString s)
  VUnit -> ELit LUnit
  VBelief bv -> EBelief (toBelief bv)
  where
    toBelief (BeliefValue v c j inv) =
      Belief (toValue v) c JNone (if inv then IUndercut (Defeat 1) else INone) PNone

-- | Convert Expr to Value (if already a value).
fromValue :: Value -> Either EvalError Expr
fromValue = Right . toValue

-- | Evaluate justification to value list.
evalJustification :: Env -> Justification -> [Value]
evalJustification env = \case
  JNone -> []
  JSingle e -> case evalExpr env e of
    Right v -> [v]
    Left _ -> []
  JAggregate es -> concatMap (\e -> case evalExpr env e of
    Right v -> [v]
    Left _ -> []) es

-- | Check if invalidation indicates defeated belief.
isInvalidated :: Env -> Invalidation -> Bool
isInvalidated env = \case
  INone -> False
  IUndercut (Defeat d) -> d > 0.5  -- Simple threshold
  IRebut (Defeat d) _ -> d > 0.5
  ICombined is -> any (isInvalidated env) is
