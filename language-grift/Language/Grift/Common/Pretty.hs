{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Grift.Common.Pretty where

import           Prelude hiding ((<>))

import           Text.PrettyPrint

import           Language.Grift.Common.Syntax

indent :: Doc -> Doc
indent = nest 2

vcat' :: [Doc] -> Doc
vcat' = foldr ($+$) empty

class Pretty p where
  ppe :: p -> Doc

instance Pretty Name where
  ppe = text

instance Pretty Prim where
  ppe (Var x) = text x
  ppe (N a)   = integer a
  ppe (F _ s) = text s
  ppe (B b)   = ppe b
  ppe Unit    = text "()"
  ppe (C c)   = text "#\\" <> ppe c

instance Pretty (e (Ann a e)) => Pretty (Ann a e) where
  ppe (Ann _ e) = ppe e

instance Pretty e => Pretty (ProgramF e) where
  ppe (Script scope) = ppe scope
  ppe (Modules modules) = vcat' $ map (($+$ text "") . ppe) modules

instance Pretty e => Pretty (ScopeF e) where
  ppe (Scope d es) = vcat' (map ppe d) $+$ vcat' (map ppe es)

instance Pretty e => Pretty (ModuleF e) where
  ppe (Module name _ _ defs es) =
    let sepComment = ppe $ replicate 20 '-'
    in text ";;" <> sepComment <+> ppe name <+> text "module" <+> sepComment $+$ vcat' (map ppe defs) $+$ vcat' (map ppe es)
-- code generation to grift modules is disabled because Grift does not support modules yet
  -- ppe (Module name imports exports defs es) = 
  --   parens (text "module" <+> text name $+$ 
  --           indent (if null imports then empty
  --                   else parens (text "imports" $+$ indent (vcat' (map ppe imports)))) $+$
  --           indent (if null exports then empty
  --                   else parens (text "exports" $+$ indent (vcat' (map ppe exports)))) $+$
  --           indent  (vcat' (map ppe defs)) $+$ indent (vcat' $ map ppe es))

instance Pretty Operator where
  ppe Plus        = char '+'
  ppe Minus       = char '-'
  ppe Mult        = char '*'
  ppe Eq          = char '='
  ppe Ge          = text ">="
  ppe Gt          = char '>'
  ppe Le          = text "<="
  ppe Lt          = char '<'
  ppe ShiftR      = text "%>>"
  ppe ShiftL      = text "%<<"
  ppe BAnd        = text "binary-and"
  ppe BOr         = text "binary-or"
  ppe Div         = text "%/"
  ppe PlusF       = text "fl+"
  ppe MinusF      = text "fl-"
  ppe MultF       = text "fl*"
  ppe DivF        = text "fl/"
  ppe ModuloF     = text "flmodulo"
  ppe AbsF        = text "flabs"
  ppe LtF         = text "fl<"
  ppe LeF         = text "fl<="
  ppe EqF         = text "fl="
  ppe GtF         = text "fl>"
  ppe GeF         = text "fl>="
  ppe MinF        = text "flmin"
  ppe MaxF        = text "flmax"
  ppe RoundF      = text "flround"
  ppe FloorF      = text "flfloor"
  ppe CeilingF    = text "flceiling"
  ppe TruncateF   = text "fltruncate"
  ppe SinF        = text "flsin"
  ppe CosF        = text "flcos"
  ppe TanF        = text "fltan"
  ppe AsinF       = text "flasin"
  ppe AcosF       = text "flacos"
  ppe AtanF       = text "flatan"
  ppe LogF        = text "fllog"
  ppe ExpF        = text "flexp"
  ppe SqrtF       = text "flsqrt"
  ppe ExptF       = text "flexpt"
  ppe FloatToInt  = text "float->int"
  ppe IntToFloat  = text "int->float"
  ppe CharToInt   = text "char->int"
  ppe ReadInt     = text "read-int"
  ppe ReadFloat   = text "read-float"
  ppe ReadChar    = text "read-char"
  ppe DisplayChar = text "display-char"

instance Pretty Bool where
  ppe True  = text "#t"
  ppe False = text "#f"

codeGen :: Pretty p => p -> String
codeGen = render . ppe
