module example2

import ORSI.Core
import ORSI.Program

%access public export
%default total

data Sajt : Type where
  Trappista : Sajt
  Eidami : Sajt

data ExTypeSpace : ORSI.Core.TypeSpace where
  ExInt : Int -> ExTypeSpace
  ExSajt : Sajt -> ExTypeSpace

F1 : ExInt gh ExInt gh ExInt 

data ExVarSpace : ORSI.Core.VarSpace where
  X1 : ExVarSpace
  X2 : ExVarSpace

DecEq ExVarSpace where
  decEq X1 X1 = Yes Refl
  decEq X2 X2 = Yes Refl
  decEq X1 X2 = No ?a
  decEq X2 X1 = No ?b

ExStateSpace : ORSI.Core.StateSpace ExVarSpace
ExStateSpace X1 = ExInt
ExStateSpace X2 = ExSajt

-- data ExExpression : ORSI.Core.Expression ExTypeSpace ExVarSpace where
--   Var : (v : ExVarSpace) -> ExExpression (ExStateSpace v)
--   -- Equal () () : Expression
