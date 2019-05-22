module Operators

%access public export
%default total

infix 1 \/
infix 2 /\
-- infix 3 ><

infix 0 |>
infix 0 |->
infix 0 ~~>

mutual

  data Predicate : Type where
    MkPredicate : String -> Predicate

  -- data StatementType : Type where
  --   PredicateStatement : StatementType

  data Statement : Type -> Type where
    PredicateStatement : Predicate -> Statement Predicate
    OrStatement : (p : Statement a) -> (q : Statement b) -> Statement (p \/ q)
    AndStatement : (p : Statement a) -> (q : Statement b) -> Statement (p /\ q)
    NotStatement : (p : Statement a) -> Statement (NNott p)

  data (\/) : (p : Statement a) -> (q : Statement b) -> Type where
    OrLeft : (p : Statement a) -> p \/ q
    OrRight : (q : Statement b) -> p \/ q

  data (/\) : (p : Statement a) -> (q : Statement b) -> Type where
    And : (p : Statement a) -> (q : Statement b) -> p /\ q

  data NNott : (p : Statement a) -> Type where
    MkNNott : (p : Statement a) -> (NNott p)


  -- Unless

  -- P |>S Q = P /\ Not Q => lf(S, P \/ Q)
  data (|>) : Statement a -> Statement b -> Type where
    Unless : (p : Statement a) -> (q : Statement b) -> p |> q


  -- Ensures

  -- P |->S Q = P |> Q /\ exists s in S: P /\ Not Q =>
  data (|->) : Statement a -> Statement b -> Type where
    Ensures : (p : Statement a) -> (q : Statement b) -> p |-> q


  -- LeadsTo

  data (~~>) : Statement a -> Statement b -> Type where
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
      (OrStatement p q ~~> r)
