module Prototype_3.util

import public Data.Vect
import public Data.HVect

%access public export
%default total

typeTuplify : List Type -> Type
typeTuplify = foldr Pair ()

termTuplify : (xs : List (DPair Type Prelude.Basics.id)) -> typeTuplify (map Prelude.Pairs.DPair.fst xs)
termTuplify [] = ()
termTuplify ((_ ** x)::xs) = (x, termTuplify xs)

-- hVectMap : {fromT : Vect k Type} -> {toT : Vect k Type} -> {fsT : Vect k Type} -> (HVect from) -> (HVect fsT) -> (HVect toT)
-- hVectMap Nil Nil = Nil
-- hVectMap (t :: ts) (f :: fs) = (f t) :: hvectMap ts fs

-- tuplify : List Type -> Type
-- tuplify list = foldr f () list
--   where
--     f t () = (t, ())
--     f t rest = (t, rest)

-- tuplify : List Type -> Type
-- tuplify [] = Unit
-- tuplify (t::ts) with (tuplify ts)
--   | (t', Unit) = (t, t')
--   | rest = (t, rest)

-- tuplify : List Type -> Type
-- tuplify [] = Unit
-- tuplify (t::ts) = (t, tuplify ts)

-- data TypeTuple : Type where
--   Empty : TypeTuple
--   Cons : Type -> TypeTuple -> TypeTuple

-- tuplify : List Type -> TypeTuple
-- tuplify [] = Empty
-- tuplify (t::ts) = Cons t (tuplify ts)

-- TypeTuple : Type
-- TypeTuple = Either Unit (Type, TypeTuple)

-- tuplify : List Type -> TypeTuple
-- tuplify [] = (the TypeTuple (Left ()))
-- tuplify (t::ts) = Right (t, tuplify ts)
