module Operators

%access public export
%default total

-- infix 1 \¬/
infix 2 /\
-- infix 3 ><

infix 0 |>
infix 0 |->
infix 0 ~~>

mutual

  Statement : Type
  Statement = Type

  -- Predicate : String -> Statement
  -- Predicate =
  data Predicate : Statement where
    MkPredicate : String -> Predicate

  syntax [p] "\\¬/" [q] = Or p q

  data Or : (p : Statement) -> (q : Statement) -> Statement where
    OrLeft : (p : Statement) -> p \¬/ q
    OrRight : (q : Statement) -> p \¬/ q

  data (/\) : (p : Statement) -> (q : Statement) -> Statement where
    And : (p : Statement) -> (q : Statement) -> p /\ q

  data NNott : (p : Statement) -> Statement where
    MkNNott : (p : Statement) -> (NNott p)


  -- Unless

  -- P |>S Q = P /\ Not Q => lf(S, P \¬/ Q)
  data (|>) : Statement -> Statement -> Type where
    Unless : (p : Statement) -> (q : Statement) -> p |> q


  -- Ensures

  -- P |->S Q = P |> Q /\ exists s in S: P /\ Not Q =>
  data (|->) : Statement -> Statement -> Type where
    Ensures : (p : Statement) -> (q : Statement) -> p |-> q


  -- LeadsTo

  data (~~>) : Statement -> Statement -> Type where
    LeadsTo1 :
      -- (p : Statement) ->
      -- (q : Statement) ->
      (p |-> q) ->
      p ~~> q
    LeadsTo2 :
      (p ~~> q) ->
      (q ~~> r) ->
      (p ~~> r)
    LeadsTo3 :
      (p ~~> r) ->
      (q ~~> r) ->
      ((p \¬/ q) ~~> r)
