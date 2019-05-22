module example3

%access public export
%default total

sajt : Bool -> Nat
sajt x = ?sa

-- isTrue (n < m)
isTrue : Bool -> Type
isTrue True = Unit
isTrue False = Void

logEqIsTrueTo : {b : Bool} -> (isTrue b) -> (b = True)
logEqIsTrueTo {b = True} p = Refl

logEqIsTrueFrom : {b : Bool} -> (b = True) -> (isTrue b)
logEqIsTrueFrom {b = False} p = absurd p
logEqIsTrueFrom {b = True} p = ()

--

logEqTo_lemma : {m, n : Nat} -> (m <= n = True) -> ((S m) <= (S n) = True)
logEqTo_lemma {m} {n} p with (compare m n)
  | LT = p
  | EQ = p
  | GT = p

logEqTo : {n, m : Nat} -> LTE n m -> (n <= m = True)
logEqTo {n = Z} {m = Z} LTEZero = Refl
logEqTo {n = Z} {m = (S k)} LTEZero = Refl
logEqTo {n = (S left)} {m = (S right)} (LTESucc x) = logEqTo_lemma (logEqTo x)

logEqFrom_lemma : {m, n : Nat} -> ((S m) <= (S n) = True) -> (m <= n = True)
logEqFrom_lemma {m} {n} p with (compare m n)
  | LT = p
  | EQ = p
  | GT = p

logEqFrom : {n, m : Nat} -> (n <= m = True) -> LTE n m
logEqFrom {n = Z} {m = m} p = LTEZero
logEqFrom {n = (S k)} {m = Z} p = absurd p
logEqFrom {n = (S k)} {m = (S j)} p = LTESucc $ logEqFrom (logEqFrom_lemma p)

--

logEqTo_lemma' : {m, n : Nat} -> (m < n = True) -> ((S m) < (S n) = True)
logEqTo_lemma' {m} {n} p with (compare m n)
  | LT = p
  | EQ = p
  | GT = p

logEqTo' : {n, m : Nat} -> LT n m -> (n < m = True)
logEqTo' {n = Z} {m = (S _)} p = Refl
logEqTo' {n = (S j)} {m = (S k)} (LTESucc x) = logEqTo_lemma' (logEqTo' x)

logEqFrom_lemma' : {m, n : Nat} -> ((S m) < (S n) = True) -> (m < n = True)
logEqFrom_lemma' {m} {n} p with (compare m n)
  | LT = p
  | EQ = p
  | GT = p

logEqFrom' : {n, m : Nat} -> (n < m = True) -> LT n m
logEqFrom' {n = Z} {m = Z} p = absurd p
logEqFrom' {n = Z} {m = (S k)} p = LTESucc LTEZero
logEqFrom' {n = (S k)} {m = Z} p = absurd p
logEqFrom' {n = (S k)} {m = (S j)} p = LTESucc $ logEqFrom' (logEqFrom_lemma' p)


--

test : (m, n : Nat) -> (p : example3.isTrue ((S m) < (S n))) -> (example3.isTrue (m < n))
test m n p with (compare m n)
  | LT = p
  | EQ = p
  | GT = p

test2 : (m, n : Nat) -> ((S m) < (S n) = True) -> (m < n = True)
test2 m n p with (compare m n)
  | LT = p
  | EQ = p
  | GT = p

-- test3 : (st : Nat -> Nat) -> (st 3 < 10 = True) -> (st 3 + 5 < 20 = True)
-- test3 st p with (compare (st 3) 10)
--   | LT with (compare (st 3 + 5) 20)
--     | LT = p
--     | EQ = ?a
--     | GT = ?a
--   | EQ = void $ uninhabited p
--   | GT = void $ uninhabited p

trans_lemma : {n, l : Nat} -> (LTE (S (S n)) l) -> (LT n l)
trans_lemma (LTESucc x) = lteSuccRight x

trans : {n, m, l : Nat} -> (n < m = True) -> (m < l = True) -> (n < l = True)
trans {n} {m} {l} p q =
  let
    p' = logEqFrom' {n = n} {m = m} p
    q' = logEqFrom' {n = m} {m = l} q
    r' = lteTransitive (LTESucc p') q'
    r = logEqTo' (trans_lemma r')
  in
    r

leSucc : {n, m : Nat} -> (n < m = True) -> (1 + n < 1 + m = True)
leSucc = logEqTo_lemma'

lePlus : {n, m : Nat} -> (l : Nat) -> (n < m = True) -> (l + n < l + m = True)
lePlus Z p = p
lePlus (S k) p = leSucc (lePlus k p)

test5 : (n : Nat) -> (isTrue (n < 5)) -> (isTrue (n < 6))
test5 n p =
  let
    p' = logEqIsTrueTo p
    p'' = logEqFrom' p'
    q'' = lteSuccRight p''
    q' = logEqTo' q''
    q = logEqIsTrueFrom q'
  in
    q

test5' : (n : Nat) -> ((n < 5) = True) -> ((n < 6) = True)
test5' n p = example3.trans p Refl
-- test5' n p = example3.trans p (the (5 < 6 = True) Refl)

lteRightPlus : {n, m : Nat} -> (p : Nat) -> LTE n m -> LTE n (p + m)
lteRightPlus Z l = l
lteRightPlus (S k) l = lteSuccRight (lteRightPlus k l)

-- lteRightPlus : (n, m, p : Nat) -> LTE n m -> LTE n (p + m)
-- lteRightPlus n m Z l = l
-- lteRightPlus n m (S k) l = lteSuccRight (lteRightPlus n m k l)

test6 : (s : Nat -> Nat) -> Nat.LTE (S (plus (s 3) 5)) 10 -> Nat.LTE (S (plus (s 3) 5)) 20
test6 s p = lteRightPlus 10 p
  -- lteSuccRight $
  -- lteSuccRight $
  -- lteSuccRight $
  -- lteSuccRight $
  -- lteSuccRight $
  -- lteSuccRight $
  -- lteSuccRight $
  -- lteSuccRight $
  -- lteSuccRight $
  -- lteSuccRight $
  -- p

-- with (compare k j)
--   | LT = LTESucc $ ?sajt
--   | EQ = LTESucc $ ?sajt
--   | GT = LTESucc $ ?sajt

-- LTESucc $ logEqFrom {n = k} {m = j} p

-- foo : Int -> Int -> Bool
-- foo n m with (succ n)
--   foo _ m | 2 with (succ m)
--     foo _ _ | 2 | 3 = True
--     foo _ _ | 2 | _ = False
--   foo _ _ | _ = False

-- foo' : Int -> Int -> Bool
-- foo' n m with (succ n)
--   | 2 with (succ m)
--     | 2 | 3 = True
--     | 2 | _ = False
--   | _ = False

-- foo'' : Int -> Int -> Bool
-- foo'' n m with (succ n)
--   | 2 with (succ m)
--     | 3 = True
--     | _ = False
--   | _ = False

-- min3 : (n, m, l : Nat) -> Nat
-- min3 n m l with (compare n m)
--   | LT with (compare n l)
--   | EQ

rewriteTest' :
  (a = False) ->
  (a = True) ->
  Void
rewriteTest' p = rewrite p in (\q => absurd q)

rewriteTest :
  (a = False) ->
  (a = True) ->
  Void
rewriteTest p q = rewriteTest' p q

--

postulate aornota : (a : Type) -> Either a (Not a)
