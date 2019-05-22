module Prototype_2.util

import public Data.Vect
import public Data.HVect

%access public export
%default total

-- typeTuplify : List Type -> Type
-- typeTuplify = foldr Pair ()

-- termTuplify : (xs : List (DPair Type Prelude.Basics.id)) -> typeTuplify (map Prelude.Pairs.DPair.fst xs)
-- termTuplify [] = ()
-- termTuplify ((_ ** x)::xs) = (x, termTuplify xs)

-- makeFunctionTypeList :
--   (fromT : List Type) ->
--   (toT : List Type) ->
--   List Type -- (\(f, t) => (f -> t)))
-- makeFunctionTypeList Nil _ = Nil
-- makeFunctionTypeList _ Nil = Nil
-- makeFunctionTypeList (f :: fs) (t :: ts) = (f -> t) :: makeFunctionTypeList fs ts

-- tupleApply :
--   (fromT : List Type) ->
--   (toT : List Type) ->
--   (from : Prototype_2.util.typeTuplify fromT) ->
--   (funs : Prototype_2.util.typeTuplify $ Prototype_2.util.makeFunctionTypeList fromT toT) ->
--   (Prototype_2.util.typeTuplify toT)
-- tupleApply Nil Nil () () = ()
-- tupleApply (ft :: fts) (tt :: tts) (fr, frs) (fun, funs) = (fun fr, tupleApply fts tts frs funs)
-- tupleApply _ _ _ _ = ()
-- listApply (f :: fs) (t :: ts) =
--   MkDPair (f, t) (f -> t) :: makeFunctionTypeList fs ts

-- applyTuplify : (fromT : List Type) -> (toT : List Type)

makeFunctionTypeVect :
  (fromTypes : Vect k Type) ->
  (toTypes : Vect k Type) ->
  (Vect k Type)
makeFunctionTypeVect Nil Nil = Nil
makeFunctionTypeVect (fromType :: fromTypes) (toType :: toTypes) =
  (fromType -> toType) :: (makeFunctionTypeVect fromTypes toTypes)

hVectApply :
  {k : Nat} ->
  {fromT : Vect k Type} ->
  {toT : Vect k Type} ->
  -- {fsT : Vect k Type} ->
  (HVect fromT) ->
  (HVect (Prototype_2.util.makeFunctionTypeVect fromT toT)) ->
  (HVect toT)
hVectApply {toT = Nil} Nil Nil = Nil
hVectApply {toT = (tt :: tts)} (t :: ts) (f :: fs) = (f t) :: hVectApply ts fs

-- hVectApply :
--   (k : Nat) ->
--   (fromT : Vect k Type) ->
--   (toT : Vect k Type) ->
--   -- {fsT : Vect k Type} ->
--   (HVect fromT) ->
--   (HVect (Prototype_2.util.makeFunctionTypeVect fromT toT)) ->
--   (HVect toT)
-- hVectApply Z Nil Nil Nil Nil = Nil
-- hVectApply (S k) (ft :: fts) (tt :: tts) (t :: ts) (f :: fs) = (f t) :: hVectApply k fts tts ts fs

-- hVectApply Z fromT toT from functions with (toT)
--   | Nil = Nil
-- hVectApply (S _) fromT toT from functions with (makeFunctionTypeVect fromT toT, from, functions)
--   | (t' :: t's, fr :: frs, fun :: funs) = (fun fr) :: hvectMap frs funs

-- hVectApply Z  = (the (HVect toT) Nil)
-- hVectApply Z fromT toT Nil Nil = (the (HVect toT) Nil)
-- hVectApply (S _) fromT toT (t :: ts) (f :: fs) = (f t) :: hvectMap ts fs

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
