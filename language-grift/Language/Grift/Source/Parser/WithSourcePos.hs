module Language.Grift.Source.Parser.WithSourcePos( TypeWithLoc
                                                 , ExpF1
                                                 , Bind1
                                                 , L1
                                                 , Scope1
                                                 , Module1
                                                 , ParsedGriftFileF (..)
                                                 , ParsedGriftFile1
                                                 , Program1 ) where

import           Text.Parsec.Pos (SourcePos)

import           Language.Grift.Common.Syntax
import           Language.Grift.Source.Syntax

data ParsedGriftFileF e =
  Module (ModuleF e)
  | Script (ScopeF e)

type WithLoc a = Ann SourcePos a

type TypeWithLoc = WithLoc Type
type ExpF1 = ExpF TypeWithLoc
type L1 = WithLoc ExpF1
type Bind1 = BindF TypeWithLoc L1
type Scope1 = ScopeF L1
type Module1 = ModuleF L1
type ParsedGriftFile1 = ParsedGriftFileF L1
type Program1 = ProgramF L1
