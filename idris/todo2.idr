----------              Assumptions:              ----------
 program : List ((Nat -> Nat) -> Bool, Instruction)
 state : Nat -> Nat
 p : True = True
----------                 Goal:                  ----------
{hole_3} : foldl (\x, y => x && Delay True) True (map (conditionalExecute state) program) = True

----------              Assumptions:              ----------
cond : (Nat -> Nat) -> Bool
inst : Instruction
xs : List ((Nat -> Nat) -> Bool, Instruction)
state : Nat -> Nat
p : True = True
----------                 Goal:                  ----------
{hole_5} : foldl (\x, y => x && Delay True) True (map (conditionalExecute state) xs) = True
