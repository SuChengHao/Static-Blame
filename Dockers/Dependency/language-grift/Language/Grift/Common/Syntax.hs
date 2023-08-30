{-# LANGUAGE DeriveFoldable       #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE DeriveTraversable    #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Grift.Common.Syntax (
  Name
  , Operator(..)
  , ScopeF (..)
  , ProgramF (..)
  , ModuleF (..)
  , Prim(..)
  , Ann (..)
  ) where

type Name = String

data Operator = Plus | Minus | Mult | Div | Eq | Ge | Gt | Le | Lt
              | ShiftR | ShiftL | BAnd | BOr
              | PlusF | MinusF | MultF | DivF| ModuloF | AbsF | LtF
              | LeF | EqF | GtF | GeF | MinF | MaxF | RoundF | FloorF
              | CeilingF | TruncateF | SinF | CosF | TanF | AsinF
              | AcosF | AtanF | LogF | ExpF | SqrtF | ExptF
              | FloatToInt | IntToFloat | CharToInt | ReadInt
              | ReadFloat | ReadChar | DisplayChar
                deriving (Eq,Show)

data Prim =
  Var Name
  | N Integer
  | F Double String
  | B Bool
  | Unit
  | C String
  deriving (Eq, Show)

data ProgramF e =
  Script (ScopeF e)
  | Modules [ModuleF e]
  deriving (Functor, Foldable, Traversable, Show)

data ModuleF e = Module {
  moduleName :: Name
  , moduleImports :: [Name]
  , moduleExports :: [Name]
  , moduleDefinitions :: [e]
  , moduleExpressions :: [e]
  }
  deriving (Functor, Foldable, Traversable, Show)

data ScopeF e = Scope {
  scopeDefinitions :: [e]
  , scopeExpressions :: [e]
  }
  deriving (Functor, Foldable, Traversable, Show)

data Ann a e = Ann a (e (Ann a e))

deriving instance (Show a, Show (e (Ann a e))) => Show (Ann a e)
