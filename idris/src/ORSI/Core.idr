module ORSI.Core

%access public export
%default total

TypeSpace : Type -- actually TypeSpace : Type 1
TypeSpace = Type

VarSpace : Type -- actually VarSpace : Type 1
VarSpace = Type

StateSpace : (varSpace : VarSpace) -> Type
StateSpace varSpace = varSpace -> TypeSpace

State :
  (varSpace : VarSpace) ->
  (stateSpace : StateSpace varSpace) ->
  Type
State
  varSpace
  stateSpace
  =
    (x : varSpace) -> (stateSpace x)

-- data Expression : (operatorSpace : OperatorSpace) -> Type

Expression :
  (typeSpace : TypeSpace) ->
  (varSpace : VarSpace) ->
  Type
Expression
  typeSpace
  varSpace
  =
    typeSpace -> Type
