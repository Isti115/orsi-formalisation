module example

import ORSI

%access public export
%default total

data Fin : Nat -> Type where
  zero : {n : Nat} -> Fin (S n)
  suc  : {n : Nat} -> Fin n -> Fin (S n)

f1 : Fin 2
f1 = zero

f2 : Fin 2
f2 = suc zero

f3 : Fin 2
f3 = suc (suc zero)

data ExVarSpace : ORSI.VarSpace where
  X1 : ExVarSpace
  X2 : ExVarSpace

disjoint : (X1 = X2) -> Void
disjoint p = replace {P = disjointTy} p ()
  where
    disjointTy : ExVarSpace -> Type
    disjointTy X1 = ()
    disjointTy X2 = Void

DecEq ExVarSpace where
  decEq X1 X1 = Yes Refl
  decEq X2 X2 = Yes Refl
  decEq X1 X2 = No disjoint
  decEq X2 X1 = No ?b

ExStateSpace : ORSI.StateSpace ExVarSpace
ExStateSpace X1 = Integer
ExStateSpace X2 = Bool

exX1 : ExVarSpace
exX1 = X1

exState : ORSI.State ExVarSpace ExStateSpace
exState X1 = 5
exState X2 = False

exInstruction : ORSI.Instruction ExVarSpace ExStateSpace
exInstruction = X2 #:=# True

-- data ExStateSpace : ORSI.StateSpace where
--    : ExStateSpace X1
--    : ExStateSpace X2
