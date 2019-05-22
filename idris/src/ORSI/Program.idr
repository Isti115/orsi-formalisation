module ORSI.Program

import ORSI.Core

%access public export
%default total

data
  Instruction :
    (varSpace : VarSpace) ->
    (stateSpace : StateSpace varSpace) ->
    Type
  where
    SKIP : Instruction varSpace stateSpace
    Assignment :
      (x : varSpace) ->
      (value : stateSpace x) ->
      Instruction varSpace stateSpace

infix 0 #:=#
(#:=#) :
  (x : varSpace) ->
  (value : stateSpace x) ->
  Instruction varSpace stateSpace
(#:=#) = Assignment

--

assign :
  DecEq varSpace =>
  State varSpace stateSpace ->
  (x : varSpace) ->
  (value : stateSpace x) ->
  State varSpace stateSpace
  -- (y : varSpace) ->
  -- (stateSpace y)
assign state x value =
    \y =>
      case decEq x y of
        Yes pro => rewrite sym pro in value
        No contra => state y

execute :
  DecEq varSpace =>
  State varSpace stateSpace ->
  Instruction varSpace stateSpace ->
  State varSpace stateSpace
execute state instruction =
  case instruction of
    SKIP => state
    Assignment x value => assign state x value


--

-- data
--   Expression :
--     (typeSpace : TypeSpace) ->
--     (varSpace : VarSpace) ->
--     (stateSpace : StateSpace varSpace) ->
--     (type : typeSpace) ->
--     Type
--   where
--     Value : (a : type2) -> Expression typeSpace varSpace stateSpace type2
--     -- Var : (x : varSpace) -> Expression typeSpace varSpace stateSpace (stateSpace x)



-- data
--   Predicate :
--     (varSpace : VarSpace) ->
--     (stateSpace : StateSpace varSpace) ->
--     Type
--   where
--     Equal :
--       (x : varSpace) ->
--       (value : stateSpace x) ->
-- Predicate :
--   (varSpace : VarSpace) ->
--   (stateSpace : StateSpace varSpace) ->
--   Type
-- Predicate varSpace stateSpace =
--   State varSpace stateSpace -> Bool
