import SyntheticComputability.PartialComputable

namespace SyntheticComputability
namespace Arithmetic
namespace Arithmetization

open PrimitiveComputable
open PartialComputable

/-!
# Arithmetization

This file contains the first arithmetization layer.

It provides a concrete numerical coding layer with proved constructor/destructor
laws for:

* pairing;
* numerical list codes;
* syntax codes;
* certificate codes.

The previous Cantor-pairing/bounded-search version has been removed.  The
pairing used here is chosen because its inverse equations are directly
provable in the bare Lean development.
-/

/-! ## Small numerals -/

def num0 : N := N.zero
def num1 : N := N.succ num0
def num2 : N := N.succ num1
def num3 : N := N.succ num2
def num4 : N := N.succ num3
def num5 : N := N.succ num4
def num6 : N := N.succ num5
def num7 : N := N.succ num6

/-! ## Conversion to Lean Nat for termination proofs -/

def toNat : N -> Nat
  | N.zero =>
      Nat.zero
  | N.succ n =>
      Nat.succ (toNat n)

theorem toNat_inj {a b : N}
    (h : toNat a = toNat b) :
    a = b := by
  induction a generalizing b with
  | zero =>
      cases b with
      | zero =>
          rfl
      | succ b =>
          simp [toNat] at h
  | succ a ih =>
      cases b with
      | zero =>
          simp [toNat] at h
      | succ b =>
          apply congrArg N.succ
          apply ih
          exact Nat.succ.inj h

theorem ne_of_toNat_ne {a b : N}
    (h : toNat a ≠ toNat b) :
    a ≠ b := by
  intro hab
  exact h (congrArg toNat hab)

/-! ## Basic numerical tests -/

/-
  Numerical truth convention:

    0 = false
    1 = true
-/

def leqN (a b : N) : N :=
  N.isZero (N.tsub a b)

def ltN (a b : N) : N :=
  leqN (N.succ a) b

def eqN (a b : N) : N :=
  N.mul (leqN a b) (leqN b a)

def neqZeroN (a : N) : N :=
  N.sg a

/-! ## A structurally usable pairing function -/

/-
  Double a natural number.

  This is used to split the natural numbers into even and odd codes.
-/

def double : N -> N
  | N.zero =>
      N.zero
  | N.succ n =>
      N.succ (N.succ (double n))

/-
  Half, rounded down.
-/

def half : N -> N
  | N.zero =>
      N.zero
  | N.succ N.zero =>
      N.zero
  | N.succ (N.succ n) =>
      N.succ (half n)

/-
  Boolean parity test.
-/

def isEven : N -> Bool
  | N.zero =>
      true
  | N.succ N.zero =>
      false
  | N.succ (N.succ n) =>
      isEven n

@[simp]
theorem isEven_double (n : N) :
    isEven (double n) = true := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [double, isEven, ih]

@[simp]
theorem isEven_succ_double (n : N) :
    isEven (N.succ (double n)) = false := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [double, isEven, ih]

@[simp]
theorem half_double (n : N) :
    half (double n) = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [double, half, ih]

/-
  A small termination lemma for recursive decoders.
-/

theorem toNat_half_lt_succ :
    (n : N) -> toNat (half n) < Nat.succ (toNat n)
  | N.zero =>
      Nat.zero_lt_succ Nat.zero
  | N.succ N.zero =>
      Nat.zero_lt_succ (Nat.succ Nat.zero)
  | N.succ (N.succ n) => by
      have ih : toNat (half n) < Nat.succ (toNat n) :=
        toNat_half_lt_succ n

      have h :
          Nat.succ (toNat (half n))
            <
          Nat.succ (Nat.succ (Nat.succ (toNat n))) :=
        Nat.succ_lt_succ
          (Nat.lt_trans
            ih
            (Nat.lt_succ_self (Nat.succ (toNat n))))

      simpa [half, toNat] using h

def pair : N -> N -> N
  | N.zero, y =>
      double y
  | N.succ x, y =>
      N.succ (double (pair x y))

/-
  First projection.

  If the code is even, the first component is 0.
  If the code is odd, remove the leading odd layer and continue.
-/

def pairFst : N -> N
  | N.zero =>
      N.zero
  | N.succ n =>
      match isEven n with
      | true =>
          N.succ (pairFst (half n))
      | false =>
          N.zero
termination_by n => toNat n
decreasing_by
  simpa [toNat] using toNat_half_lt_succ n

/-
  Second projection.
-/

def pairSnd : N -> N
  | N.zero =>
      N.zero
  | N.succ n =>
      match isEven n with
      | true =>
          pairSnd (half n)
      | false =>
          half (N.succ n)
termination_by n => toNat n
decreasing_by
  simpa [toNat] using toNat_half_lt_succ n

@[simp]
theorem pairFst_succ_double (n : N) :
    pairFst (N.succ (double n)) = N.succ (pairFst n) := by
  simp [pairFst]

@[simp]
theorem pairSnd_succ_double (n : N) :
    pairSnd (N.succ (double n)) = pairSnd n := by
  simp [pairSnd]

@[simp]
theorem pairFst_double (n : N) :
    pairFst (double n) = N.zero := by
  induction n with
  | zero =>
      simp [double, pairFst]
  | succ n ih =>
      simp [double, pairFst]

@[simp]
theorem pairSnd_double (n : N) :
    pairSnd (double n) = n := by
  induction n with
  | zero =>
      simp [double, pairSnd]
  | succ n ih =>
      simp [double, pairSnd, half]

@[simp]
theorem pairFst_pair (x y : N) :
    pairFst (pair x y) = x := by
  induction x with
  | zero =>
      simp [pair]
  | succ x ih =>
      simp [pair, ih]

@[simp]
theorem pairSnd_pair (x y : N) :
    pairSnd (pair x y) = y := by
  induction x with
  | zero =>
      simp [pair]
  | succ x ih =>
      simp [pair, ih]

theorem pair_inj {x y x' y' : N}
    (h : pair x y = pair x' y') :
    x = x' ∧ y = y' := by
  constructor
  · simpa using congrArg pairFst h
  · simpa using congrArg pairSnd h

theorem pair_ext {x y x' y' : N}
    (hx : x = x')
    (hy : y = y') :
    pair x y = pair x' y' := by
  cases hx
  cases hy
  rfl

/-
  The second projection of any positive code is structurally smaller than the
  positive code.  This is used to define list recursion by following tails.
-/

def pairSnd_lt_succ_aux :
    (n : N) -> toNat (pairSnd n) < Nat.succ (toNat n)
  | N.zero => by
      simp [pairSnd, toNat]
  | N.succ n => by
      cases h : isEven n with
      | false =>
          have hhalf :
              toNat (half (N.succ n))
                <
              Nat.succ (toNat (N.succ n)) :=
            toNat_half_lt_succ (N.succ n)

          simpa [pairSnd, h] using hhalf

      | true =>
          have ih :
              toNat (pairSnd (half n))
                <
              Nat.succ (toNat (half n)) :=
            pairSnd_lt_succ_aux (half n)

          have hhalf :
              toNat (half n)
                <
              toNat (N.succ n) := by
            simpa [toNat] using toNat_half_lt_succ n

          have hlt :
              toNat (pairSnd (half n))
                <
              Nat.succ (toNat (N.succ n)) :=
            Nat.lt_trans ih (Nat.succ_lt_succ hhalf)

          simpa [pairSnd, h] using hlt
termination_by n => toNat n
decreasing_by
  simpa [toNat] using toNat_half_lt_succ n

theorem pairSnd_lt_succ (n : N) :
    toNat (pairSnd n) < Nat.succ (toNat n) :=
  pairSnd_lt_succ_aux n

/-! ## Numerical list codes -/

/-
  Numerical lists are coded by:

    []      := 0
    h :: t  := S(pair h t)
-/

def nilCode : N :=
  N.zero

def consCode (h t : N) : N :=
  N.succ (pair h t)

def singletonCode (x : N) : N :=
  consCode x nilCode

def isNilCode (xs : N) : N :=
  N.isZero xs

def isConsCode (xs : N) : N :=
  N.sg xs

/-
  Default-valued destructors.
-/

def head0 : N -> N
  | N.zero =>
      N.zero
  | N.succ m =>
      pairFst m

def tail0 : N -> N
  | N.zero =>
      N.zero
  | N.succ m =>
      pairSnd m

@[simp]
theorem head0_nilCode :
    head0 nilCode = N.zero := by
  rfl

@[simp]
theorem tail0_nilCode :
    tail0 nilCode = N.zero := by
  rfl

@[simp]
theorem head0_consCode (h t : N) :
    head0 (consCode h t) = h := by
  simp [consCode, head0]

@[simp]
theorem tail0_consCode (h t : N) :
    tail0 (consCode h t) = t := by
  simp [consCode, tail0]

theorem consCode_inj {h t h' t' : N}
    (hc : consCode h t = consCode h' t') :
    h = h' ∧ t = t' := by
  have hp : pair h t = pair h' t' := by
    have hpred := congrArg N.pred hc
    simpa [consCode, N.pred] using hpred
  exact pair_inj hp

theorem nilCode_ne_consCode (h t : N) :
    nilCode ≠ consCode h t := by
  intro hc
  cases hc

theorem consCode_ne_nilCode (h t : N) :
    consCode h t ≠ nilCode := by
  intro hc
  cases hc

/-
  Iterated tail.
-/

def tailIter (xs : N) : N -> N
  | N.zero =>
      xs
  | N.succ i =>
      tail0 (tailIter xs i)

/-
  Length of a list code.

  This follows the actual numerical tail, using the proved fact that tails are
  smaller than nonzero list codes.
-/

def len : N -> N
  | N.zero =>
      N.zero
  | N.succ m =>
      N.succ (len (pairSnd m))
termination_by xs => toNat xs
decreasing_by
  simpa [toNat] using pairSnd_lt_succ m

@[simp]
theorem len_nilCode :
    len nilCode = N.zero := by
  simp [len, nilCode]

@[simp]
theorem len_consCode (h t : N) :
    len (consCode h t) = N.succ (len t) := by
  simp [consCode, len]

/-
  Default-valued lookup.
-/

def nth (xs : N) : N -> N
  | N.zero =>
      head0 xs
  | N.succ i =>
      nth (tail0 xs) i

@[simp]
theorem nth_zero_consCode (h t : N) :
    nth (consCode h t) N.zero = h := by
  simp [nth]

@[simp]
theorem nth_succ_consCode (h t i : N) :
    nth (consCode h t) (N.succ i) = nth t i := by
  simp [nth]

/-
  Append of numerical list codes.
-/

def append : N -> N -> N
  | N.zero, v =>
      v
  | N.succ m, v =>
      consCode (pairFst m) (append (pairSnd m) v)
termination_by u _ => toNat u
decreasing_by
  simpa [toNat] using pairSnd_lt_succ m

@[simp]
theorem append_nilCode (v : N) :
    append nilCode v = v := by
  simp [append, nilCode]

@[simp]
theorem append_consCode (h t v : N) :
    append (consCode h t) v = consCode h (append t v) := by
  simp [append, consCode]

/-
  Convert a finite vector into a numerical list code.
-/

def listCode : {k : N} -> Vec k -> N
  | N.zero, Vec.nil =>
      nilCode
  | N.succ _, Vec.cons x xs =>
      consCode x (listCode xs)

@[simp]
theorem listCode_nil :
    listCode Vec.nil = nilCode := by
  rfl

@[simp]
theorem listCode_cons {k : N} (x : N) (xs : Vec k) :
    listCode (Vec.cons x xs) = consCode x (listCode xs) := by
  rfl

/-! ## Small vector destructors -/

def firstOfTwo (xs : Vec N.two) : N :=
  Vec.head xs

def secondOfTwo (xs : Vec N.two) : N :=
  Vec.head (Vec.tail xs)

def firstOfThree (xs : Vec N.three) : N :=
  Vec.head xs

def secondOfThree (xs : Vec N.three) : N :=
  Vec.head (Vec.tail xs)

def thirdOfThree (xs : Vec N.three) : N :=
  Vec.head (Vec.tail (Vec.tail xs))

/-! ## Syntax tags and syntax-code constructors -/

def tagZero : N := num0
def tagConst : N := num1
def tagSucc : N := num2
def tagProj : N := num3
def tagComp : N := num4
def tagRec : N := num5
def tagMu : N := num6

/-
  A raw packed syntax code is nonzero.

  Numerically, packed syntax codes are of the form

    S(pair tag payload).

  This predicate only says that the number is nonzero.  It does not say that
  the tag is one of the valid syntax tags, nor that the payload is well-formed.
-/

def SynCodeT : N -> Type
  | N.zero =>
      Void
  | N.succ _ =>
      One

def mkSynCode (tag payload : N) : N :=
  N.succ (pair tag payload)

def codeZero (k : N) : N :=
  mkSynCode tagZero k

def codeConst (k c : N) : N :=
  mkSynCode tagConst (pair k c)

def codeSucc : N :=
  mkSynCode tagSucc N.zero

def codeProj (k i : N) : N :=
  mkSynCode tagProj (pair k i)

def codeComp (r h gs : N) : N :=
  mkSynCode tagComp (pair r (pair h gs))

def codeRec (g h : N) : N :=
  mkSynCode tagRec (pair g h)

def codeMu (g : N) : N :=
  mkSynCode tagMu g

def tagOf (e : N) : N :=
  pairFst (N.pred e)

def payloadOf (e : N) : N :=
  pairSnd (N.pred e)

@[simp]
theorem tagOf_mkSynCode (tag payload : N) :
    tagOf (mkSynCode tag payload) = tag := by
  simp [tagOf, mkSynCode, N.pred]

@[simp]
theorem payloadOf_mkSynCode (tag payload : N) :
    payloadOf (mkSynCode tag payload) = payload := by
  simp [payloadOf, mkSynCode, N.pred]

theorem mkSynCode_inj {tag payload tag' payload' : N}
    (h : mkSynCode tag payload = mkSynCode tag' payload') :
    tag = tag' ∧ payload = payload' := by
  have hp : pair tag payload = pair tag' payload' := by
    have hpred := congrArg N.pred h
    simpa [mkSynCode, N.pred] using hpred
  exact pair_inj hp

theorem mkSynCode_ne_of_tag_ne
    {tag payload tag' payload' : N}
    (ht : tag ≠ tag') :
    mkSynCode tag payload ≠ mkSynCode tag' payload' := by
  intro h
  exact ht ((mkSynCode_inj h).1)

@[simp]
theorem tagOf_codeZero (k : N) :
    tagOf (codeZero k) = tagZero := by
  simp [codeZero]

@[simp]
theorem payloadOf_codeZero (k : N) :
    payloadOf (codeZero k) = k := by
  simp [codeZero]

@[simp]
theorem tagOf_codeConst (k c : N) :
    tagOf (codeConst k c) = tagConst := by
  simp [codeConst]

@[simp]
theorem payloadOf_codeConst (k c : N) :
    payloadOf (codeConst k c) = pair k c := by
  simp [codeConst]

@[simp]
theorem tagOf_codeSucc :
    tagOf codeSucc = tagSucc := by
  simp [codeSucc]

@[simp]
theorem payloadOf_codeSucc :
    payloadOf codeSucc = N.zero := by
  simp [codeSucc]

@[simp]
theorem tagOf_codeProj (k i : N) :
    tagOf (codeProj k i) = tagProj := by
  simp [codeProj]

@[simp]
theorem payloadOf_codeProj (k i : N) :
    payloadOf (codeProj k i) = pair k i := by
  simp [codeProj]

@[simp]
theorem tagOf_codeComp (r h gs : N) :
    tagOf (codeComp r h gs) = tagComp := by
  simp [codeComp]

@[simp]
theorem payloadOf_codeComp (r h gs : N) :
    payloadOf (codeComp r h gs) = pair r (pair h gs) := by
  simp [codeComp]

@[simp]
theorem tagOf_codeRec (g h : N) :
    tagOf (codeRec g h) = tagRec := by
  simp [codeRec]

@[simp]
theorem payloadOf_codeRec (g h : N) :
    payloadOf (codeRec g h) = pair g h := by
  simp [codeRec]

@[simp]
theorem tagOf_codeMu (g : N) :
    tagOf (codeMu g) = tagMu := by
  simp [codeMu]

@[simp]
theorem payloadOf_codeMu (g : N) :
    payloadOf (codeMu g) = g := by
  simp [codeMu]

theorem codeZero_inj {k k' : N}
    (h : codeZero k = codeZero k') :
    k = k' := by
  have hp : payloadOf (codeZero k) = payloadOf (codeZero k') := by
    rw [h]
  simpa using hp

theorem codeConst_inj {k c k' c' : N}
    (h : codeConst k c = codeConst k' c') :
    k = k' ∧ c = c' := by
  have hp : pair k c = pair k' c' := by
    have hpayload :
        payloadOf (codeConst k c) = payloadOf (codeConst k' c') := by
      rw [h]
    simpa using hpayload
  exact pair_inj hp

theorem codeProj_inj {k i k' i' : N}
    (h : codeProj k i = codeProj k' i') :
    k = k' ∧ i = i' := by
  have hp : pair k i = pair k' i' := by
    have hpayload :
        payloadOf (codeProj k i) = payloadOf (codeProj k' i') := by
      rw [h]
    simpa using hpayload
  exact pair_inj hp

theorem codeComp_inj {r h gs r' h' gs' : N}
    (hc : codeComp r h gs = codeComp r' h' gs') :
    r = r' ∧ h = h' ∧ gs = gs' := by
  have hp : pair r (pair h gs) = pair r' (pair h' gs') := by
    have hpayload :
        payloadOf (codeComp r h gs) =
        payloadOf (codeComp r' h' gs') := by
      rw [hc]
    simpa using hpayload
  have htop := pair_inj hp
  have htail := pair_inj htop.2
  constructor
  · exact htop.1
  · constructor
    · exact htail.1
    · exact htail.2

theorem codeRec_inj {g h g' h' : N}
    (hc : codeRec g h = codeRec g' h') :
    g = g' ∧ h = h' := by
  have hp : pair g h = pair g' h' := by
    have hpayload :
        payloadOf (codeRec g h) = payloadOf (codeRec g' h') := by
      rw [hc]
    simpa using hpayload
  exact pair_inj hp

theorem codeMu_inj {g g' : N}
    (h : codeMu g = codeMu g') :
    g = g' := by
  have hp : payloadOf (codeMu g) = payloadOf (codeMu g') := by
    rw [h]
  simpa using hp

/-! ## Payload destructors for common syntax forms -/

def constArityOf (e : N) : N :=
  pairFst (payloadOf e)

def constValueOf (e : N) : N :=
  pairSnd (payloadOf e)

def projArityOf (e : N) : N :=
  pairFst (payloadOf e)

def projIndexOf (e : N) : N :=
  pairSnd (payloadOf e)

def compSourceArityOf (e : N) : N :=
  pairFst (payloadOf e)

def compHeadOf (e : N) : N :=
  pairFst (pairSnd (payloadOf e))

def compArgsOf (e : N) : N :=
  pairSnd (pairSnd (payloadOf e))

def recInitOf (e : N) : N :=
  pairFst (payloadOf e)

def recStepOf (e : N) : N :=
  pairSnd (payloadOf e)

def muBodyOf (e : N) : N :=
  payloadOf e

@[simp]
theorem constArityOf_codeConst (k c : N) :
    constArityOf (codeConst k c) = k := by
  simp [constArityOf]

@[simp]
theorem constValueOf_codeConst (k c : N) :
    constValueOf (codeConst k c) = c := by
  simp [constValueOf]

@[simp]
theorem projArityOf_codeProj (k i : N) :
    projArityOf (codeProj k i) = k := by
  simp [projArityOf]

@[simp]
theorem projIndexOf_codeProj (k i : N) :
    projIndexOf (codeProj k i) = i := by
  simp [projIndexOf]

@[simp]
theorem compSourceArityOf_codeComp (r h gs : N) :
    compSourceArityOf (codeComp r h gs) = r := by
  simp [compSourceArityOf]

@[simp]
theorem compHeadOf_codeComp (r h gs : N) :
    compHeadOf (codeComp r h gs) = h := by
  simp [compHeadOf]

@[simp]
theorem compArgsOf_codeComp (r h gs : N) :
    compArgsOf (codeComp r h gs) = gs := by
  simp [compArgsOf]

@[simp]
theorem recInitOf_codeRec (g h : N) :
    recInitOf (codeRec g h) = g := by
  simp [recInitOf]

@[simp]
theorem recStepOf_codeRec (g h : N) :
    recStepOf (codeRec g h) = h := by
  simp [recStepOf]

@[simp]
theorem muBodyOf_codeMu (g : N) :
    muBodyOf (codeMu g) = g := by
  simp [muBodyOf]

/-! ## Certificate tags and certificate-code constructors -/

def ctZero : N := num0
def ctConst : N := num1
def ctSucc : N := num2
def ctProj : N := num3
def ctComp : N := num4
def ctRecZero : N := num5
def ctRecSucc : N := num6
def ctMu : N := num7

/-
  A raw packed certificate code is nonzero.

  This only says that the number has packed-code shape.  It does not say that
  the certificate tag or payload is semantically valid.
-/

def CertCodeT : N -> Type
  | N.zero =>
      Void
  | N.succ _ =>
      One

def certMk (ctag output payload : N) : N :=
  N.succ (pair ctag (pair output payload))

def certTag (c : N) : N :=
  pairFst (N.pred c)

def certOut (c : N) : N :=
  pairFst (pairSnd (N.pred c))

def certPayload (c : N) : N :=
  pairSnd (pairSnd (N.pred c))

@[simp]
theorem certTag_certMk (ctag output payload : N) :
    certTag (certMk ctag output payload) = ctag := by
  simp [certTag, certMk, N.pred]

@[simp]
theorem certOut_certMk (ctag output payload : N) :
    certOut (certMk ctag output payload) = output := by
  simp [certOut, certMk, N.pred]

@[simp]
theorem certPayload_certMk (ctag output payload : N) :
    certPayload (certMk ctag output payload) = payload := by
  simp [certPayload, certMk, N.pred]

theorem certMk_inj {ctag output payload ctag' output' payload' : N}
    (h :
      certMk ctag output payload =
      certMk ctag' output' payload') :
    ctag = ctag' ∧ output = output' ∧ payload = payload' := by
  have hp :
      pair ctag (pair output payload) =
      pair ctag' (pair output' payload') := by
    have hpred := congrArg N.pred h
    simpa [certMk, N.pred] using hpred

  have htop := pair_inj hp
  have htail := pair_inj htop.2

  constructor
  · exact htop.1
  · constructor
    · exact htail.1
    · exact htail.2

theorem certMk_tag_eq_of_eq
    {ctag output payload ctag' output' payload' : N}
    (h :
      certMk ctag output payload =
      certMk ctag' output' payload') :
    ctag = ctag' := by
  exact (certMk_inj h).1

theorem certMk_output_eq_of_eq
    {ctag output payload ctag' output' payload' : N}
    (h :
      certMk ctag output payload =
      certMk ctag' output' payload') :
    output = output' := by
  exact (certMk_inj h).2.1

theorem certMk_payload_eq_of_eq
    {ctag output payload ctag' output' payload' : N}
    (h :
      certMk ctag output payload =
      certMk ctag' output' payload') :
    payload = payload' := by
  exact (certMk_inj h).2.2

/-
  Certificate constructors.
-/

def certZeroMk (output payload : N) : N :=
  certMk ctZero output payload

def certConstMk (output payload : N) : N :=
  certMk ctConst output payload

def certSuccMk (output payload : N) : N :=
  certMk ctSucc output payload

def certProjMk (output payload : N) : N :=
  certMk ctProj output payload

def certCompMk (output payload : N) : N :=
  certMk ctComp output payload

def certRecZeroMk (output payload : N) : N :=
  certMk ctRecZero output payload

def certRecSuccMk (output payload : N) : N :=
  certMk ctRecSucc output payload

def certMuMk (output payload : N) : N :=
  certMk ctMu output payload

@[simp]
theorem certTag_certZeroMk (output payload : N) :
    certTag (certZeroMk output payload) = ctZero := by
  simp [certZeroMk]

@[simp]
theorem certTag_certConstMk (output payload : N) :
    certTag (certConstMk output payload) = ctConst := by
  simp [certConstMk]

@[simp]
theorem certTag_certSuccMk (output payload : N) :
    certTag (certSuccMk output payload) = ctSucc := by
  simp [certSuccMk]

@[simp]
theorem certTag_certProjMk (output payload : N) :
    certTag (certProjMk output payload) = ctProj := by
  simp [certProjMk]

@[simp]
theorem certTag_certCompMk (output payload : N) :
    certTag (certCompMk output payload) = ctComp := by
  simp [certCompMk]

@[simp]
theorem certTag_certRecZeroMk (output payload : N) :
    certTag (certRecZeroMk output payload) = ctRecZero := by
  simp [certRecZeroMk]

@[simp]
theorem certTag_certRecSuccMk (output payload : N) :
    certTag (certRecSuccMk output payload) = ctRecSucc := by
  simp [certRecSuccMk]

@[simp]
theorem certTag_certMuMk (output payload : N) :
    certTag (certMuMk output payload) = ctMu := by
  simp [certMuMk]

/-! ## Certificate-list output operation -/

/-
  certOutList cs m returns the list

    [certOut (nth cs 0), ..., certOut (nth cs (m - 1))].
-/

def certOutList (cs : N) : N -> N
  | N.zero =>
      nilCode
  | N.succ i =>
      append
        (certOutList cs i)
        (singletonCode (certOut (nth cs i)))

@[simp]
theorem certOutList_zero (cs : N) :
    certOutList cs N.zero = nilCode := by
  rfl

@[simp]
theorem certOutList_succ (cs i : N) :
    certOutList cs (N.succ i)
      =
    append
      (certOutList cs i)
      (singletonCode (certOut (nth cs i))) := by
  rfl

/-! ## Primitive-recursive codes for the arithmetization layer -/

/-
  The definitions above give Lean-level numerical operations.

  The following section gives actual primitive-recursive codes for the
  arithmetization operations needed by the later certificate checker.

  These are code objects in `PrimCode`, not Prop-valued certificates.
-/

/-! ### Small arities and tuple helpers -/

def arity4 : N :=
  N.succ N.three

def ixFourth : Vec.Ix arity4 :=
  Vec.Ix.succ (Vec.Ix.succ (Vec.Ix.succ Vec.Ix.zero))

namespace CodeTuple

def four {k : N}
    (f g h l : PrimCode k) :
    Vec.Ix arity4 -> PrimCode k
  | Vec.Ix.zero =>
      f
  | Vec.Ix.succ Vec.Ix.zero =>
      g
  | Vec.Ix.succ (Vec.Ix.succ Vec.Ix.zero) =>
      h
  | Vec.Ix.succ (Vec.Ix.succ (Vec.Ix.succ Vec.Ix.zero)) =>
      l

end CodeTuple

def proj1_1 : PrimCode N.one :=
  PrimCode.proj Vec.Ix.first

def proj2_1 : PrimCode N.two :=
  PrimCode.proj Vec.Ix.first

def proj2_2 : PrimCode N.two :=
  PrimCode.proj Vec.Ix.second

def proj3_1 : PrimCode N.three :=
  PrimCode.proj Vec.Ix.first

def proj3_2 : PrimCode N.three :=
  PrimCode.proj Vec.Ix.second

def proj3_3 : PrimCode N.three :=
  PrimCode.proj Vec.Ix.third

def proj4_1 : PrimCode arity4 :=
  PrimCode.proj Vec.Ix.first

def proj4_2 : PrimCode arity4 :=
  PrimCode.proj Vec.Ix.second

def proj4_3 : PrimCode arity4 :=
  PrimCode.proj Vec.Ix.third

def proj4_4 : PrimCode arity4 :=
  PrimCode.proj ixFourth

def succOn {k : N} (c : PrimCode k) : PrimCode k :=
  PrimCode.comp
    PrimCode.succ
    (CodeTuple.one c)

/-! ### Boolean/numerical combinators -/

/-
  Boolean conditional on numerical booleans.

  Truth convention:
    0 = false
    1 = true

  boolIfCode(b,t,e) = if b then t else e
  provided b is a numerical boolean.
-/

def boolIfCode : PrimCode N.three :=
  PrimCode.comp
    addCode
    (CodeTuple.two
      (PrimCode.comp
        mulCode
        (CodeTuple.two
          proj3_1
          proj3_2))
      (PrimCode.comp
        mulCode
        (CodeTuple.two
          (PrimCode.comp
            isZeroCode
            (CodeTuple.one proj3_1))
          proj3_3)))

/-! ### Primitive-recursive codes for basic arithmetization numerics -/

/-
  double(0)     = 0
  double(S n)   = S(S(double n))
-/

def doubleStepCode : PrimCode N.two :=
  succOn (succOn proj2_2)

def doubleCode : PrimCode N.one :=
  PrimCode.prec
    (PrimCode.zero N.zero)
    doubleStepCode

/-
  evenN is the numerical version of `isEven`.

    evenN 0       = 1
    evenN (S n)   = isZero(evenN n)

  It returns 1 on even inputs and 0 on odd inputs.
-/

def evenStepCode : PrimCode N.two :=
  PrimCode.comp
    isZeroCode
    (CodeTuple.one proj2_2)

def evenCode : PrimCode N.one :=
  PrimCode.prec
    (constCode (k := N.zero) N.one)
    evenStepCode

/-
  half(0)       = 0
  half(S n)     = half(n) + isZero(evenN n)

  Since evenN n = 0 exactly when n is odd, this increments precisely when
  passing from an odd n to S n.
-/

def halfStepOddCode : PrimCode N.two :=
  PrimCode.comp
    isZeroCode
    (CodeTuple.one
      (PrimCode.comp
        evenCode
        (CodeTuple.one proj2_1)))

def halfStepCode : PrimCode N.two :=
  PrimCode.comp
    addCode
    (CodeTuple.two
      proj2_2
      halfStepOddCode)

def halfCode : PrimCode N.one :=
  PrimCode.prec
    (PrimCode.zero N.zero)
    halfStepCode

/-
  The imported primitive-computable arithmetic codes already give these
  numerical tests.
-/

def leqNCode : PrimCode N.two :=
  leqCode

def ltNCode : PrimCode N.two :=
  ltCode

def eqNCode : PrimCode N.two :=
  eqCode

def neqZeroNCode : PrimCode N.one :=
  sgCode

/-! ### Primitive-recursive code for pairing -/

/-
  pair(0,y)     = double y
  pair(S x,y)   = S(double(pair x y))
-/

def pairStepCode : PrimCode N.three :=
  succOn
    (PrimCode.comp
      doubleCode
      (CodeTuple.one proj3_2))

def pairCode : PrimCode N.two :=
  PrimCode.prec
    doubleCode
    pairStepCode

/-! ### Primitive-recursive codes for pair projections -/

/-
  The Lean-level projections `pairFst` and `pairSnd` follow `half`.
  To produce primitive-recursive code, we use bounded iteration.

  A code `z` is decoded by repeatedly stripping an outer odd layer

      S(double r) ↦ r

  for at most z steps.  The number of stripped layers is the first projection;
  the final even remainder determines the second projection by taking `half`.

  isPairLayer(r) is true precisely when r has the form S(double q).
-/

def isPairLayerCode : PrimCode N.one :=
  PrimCode.comp
    mulCode
    (CodeTuple.two
      (PrimCode.comp
        sgCode
        (CodeTuple.one proj1_1))
      (PrimCode.comp
        evenCode
        (CodeTuple.one
          (PrimCode.comp
            predCode
            (CodeTuple.one proj1_1)))))

/-
  pairRestIter(i,z) is the remainder after stripping at most i outer layers
  from z.
-/

def pairRestStepStrippedCode : PrimCode N.three :=
  PrimCode.comp
    halfCode
    (CodeTuple.one
      (PrimCode.comp
        predCode
        (CodeTuple.one proj3_2)))

def pairRestStepCode : PrimCode N.three :=
  PrimCode.comp
    boolIfCode
    (CodeTuple.three
      (PrimCode.comp
        isPairLayerCode
        (CodeTuple.one proj3_2))
      pairRestStepStrippedCode
      proj3_2)

def pairRestIterCode : PrimCode N.two :=
  PrimCode.prec
    proj1_1
    pairRestStepCode

/-
  pairFstIter(i,z) counts how many layers have been stripped in the first i
  steps.
-/

def pairRestAtStepCode : PrimCode N.three :=
  PrimCode.comp
    pairRestIterCode
    (CodeTuple.two
      proj3_1
      proj3_3)

def pairFstCountStepCode : PrimCode N.three :=
  PrimCode.comp
    boolIfCode
    (CodeTuple.three
      (PrimCode.comp
        isPairLayerCode
        (CodeTuple.one pairRestAtStepCode))
      (succOn proj3_2)
      proj3_2)

def pairFstIterCode : PrimCode N.two :=
  PrimCode.prec
    (PrimCode.zero N.one)
    pairFstCountStepCode

def pairRestCode : PrimCode N.one :=
  PrimCode.comp
    pairRestIterCode
    (CodeTuple.two
      proj1_1
      proj1_1)

def pairFstCode : PrimCode N.one :=
  PrimCode.comp
    pairFstIterCode
    (CodeTuple.two
      proj1_1
      proj1_1)

def pairSndCode : PrimCode N.one :=
  PrimCode.comp
    halfCode
    (CodeTuple.one pairRestCode)

/-! ### Primitive-recursive codes for numerical list operations -/

def nilCodeCode : PrimCode N.zero :=
  constCode (k := N.zero) nilCode

def consCodeCode : PrimCode N.two :=
  succOn pairCode

def singletonCodeCode : PrimCode N.one :=
  PrimCode.comp
    consCodeCode
    (CodeTuple.two
      proj1_1
      (constCode (k := N.one) nilCode))

def isNilCodeCode : PrimCode N.one :=
  isZeroCode

def isConsCodeCode : PrimCode N.one :=
  sgCode

def head0Code : PrimCode N.one :=
  PrimCode.comp
    pairFstCode
    (CodeTuple.one
      (PrimCode.comp
        predCode
        (CodeTuple.one proj1_1)))

def tail0Code : PrimCode N.one :=
  PrimCode.comp
    pairSndCode
    (CodeTuple.one
      (PrimCode.comp
        predCode
        (CodeTuple.one proj1_1)))

/-
  tailIterCode(i,xs) = tail0 iterated i times on xs.
-/

def tailIterStepCode : PrimCode N.three :=
  PrimCode.comp
    tail0Code
    (CodeTuple.one proj3_2)

def tailIterCode : PrimCode N.two :=
  PrimCode.prec
    proj1_1
    tailIterStepCode

/-
  lenIterCode(i,xs) counts how many nonempty tails occur among the first i
  tail-iterations.
-/

def tailAtLenStepCode : PrimCode N.three :=
  PrimCode.comp
    tailIterCode
    (CodeTuple.two
      proj3_1
      proj3_3)

def lenStepCode : PrimCode N.three :=
  PrimCode.comp
    boolIfCode
    (CodeTuple.three
      (PrimCode.comp
        sgCode
        (CodeTuple.one tailAtLenStepCode))
      (succOn proj3_2)
      proj3_2)

def lenIterCode : PrimCode N.two :=
  PrimCode.prec
    (PrimCode.zero N.one)
    lenStepCode

def lenCode : PrimCode N.one :=
  PrimCode.comp
    lenIterCode
    (CodeTuple.two
      proj1_1
      proj1_1)

/-
  nth(xs,i) = head0(tailIter(i,xs)).
-/

def nthTailCode : PrimCode N.two :=
  PrimCode.comp
    tailIterCode
    (CodeTuple.two
      proj2_2
      proj2_1)

def nthCode : PrimCode N.two :=
  PrimCode.comp
    head0Code
    (CodeTuple.one nthTailCode)

/-
  appendCode is built by right-to-left bounded reconstruction.

  appendIter(i,u,v) reconstructs the last i entries of u in front of v.
  At stage i it adds the element at index:

      len(u) dotminus S(i)

  Thus appendIter(len u,u,v) = append u v.
-/

def appendIndexCode : PrimCode arity4 :=
  PrimCode.comp
    tsubCode
    (CodeTuple.two
      (PrimCode.comp
        lenCode
        (CodeTuple.one proj4_3))
      (succOn proj4_1))

def appendElemCode : PrimCode arity4 :=
  PrimCode.comp
    nthCode
    (CodeTuple.two
      proj4_3
      appendIndexCode)

def appendStepCode : PrimCode arity4 :=
  PrimCode.comp
    consCodeCode
    (CodeTuple.two
      appendElemCode
      proj4_2)

def appendIterCode : PrimCode N.three :=
  PrimCode.prec
    proj2_2
    appendStepCode

def appendCode : PrimCode N.two :=
  PrimCode.comp
    appendIterCode
    (CodeTuple.three
      (PrimCode.comp
        lenCode
        (CodeTuple.one proj2_1))
      proj2_1
      proj2_2)

/-! ### Primitive-recursive codes for vector/list conversion helpers -/

/-
  The map `listCode` itself is indexed by the vector length and is structurally
  recursive over Lean vectors, so it is not represented by one fixed numerical
  code.  The numerical operations on list codes needed downstream are the
  fixed-arity codes above: nil, cons, singleton, head0, tail0, len, nth, append.
-/

/-! ### Primitive-recursive codes for syntax-code operations -/

def mkSynCodeCode : PrimCode N.two :=
  consCodeCode

def codeZeroCode : PrimCode N.one :=
  PrimCode.comp
    mkSynCodeCode
    (CodeTuple.two
      (constCode (k := N.one) tagZero)
      proj1_1)

def codeConstCode : PrimCode N.two :=
  PrimCode.comp
    mkSynCodeCode
    (CodeTuple.two
      (constCode (k := N.two) tagConst)
      (PrimCode.comp
        pairCode
        (CodeTuple.two
          proj2_1
          proj2_2)))

def codeSuccCode : PrimCode N.zero :=
  PrimCode.comp
    mkSynCodeCode
    (CodeTuple.two
      (constCode (k := N.zero) tagSucc)
      (constCode (k := N.zero) N.zero))

def codeProjCode : PrimCode N.two :=
  PrimCode.comp
    mkSynCodeCode
    (CodeTuple.two
      (constCode (k := N.two) tagProj)
      (PrimCode.comp
        pairCode
        (CodeTuple.two
          proj2_1
          proj2_2)))

def codeCompPayloadCode : PrimCode N.three :=
  PrimCode.comp
    pairCode
    (CodeTuple.two
      proj3_1
      (PrimCode.comp
        pairCode
        (CodeTuple.two
          proj3_2
          proj3_3)))

def codeCompCode : PrimCode N.three :=
  PrimCode.comp
    mkSynCodeCode
    (CodeTuple.two
      (constCode (k := N.three) tagComp)
      codeCompPayloadCode)

def codeRecCode : PrimCode N.two :=
  PrimCode.comp
    mkSynCodeCode
    (CodeTuple.two
      (constCode (k := N.two) tagRec)
      (PrimCode.comp
        pairCode
        (CodeTuple.two
          proj2_1
          proj2_2)))

def codeMuCode : PrimCode N.one :=
  PrimCode.comp
    mkSynCodeCode
    (CodeTuple.two
      (constCode (k := N.one) tagMu)
      proj1_1)

def tagOfCode : PrimCode N.one :=
  PrimCode.comp
    pairFstCode
    (CodeTuple.one
      (PrimCode.comp
        predCode
        (CodeTuple.one proj1_1)))

def payloadOfCode : PrimCode N.one :=
  PrimCode.comp
    pairSndCode
    (CodeTuple.one
      (PrimCode.comp
        predCode
        (CodeTuple.one proj1_1)))

def constArityOfCode : PrimCode N.one :=
  PrimCode.comp
    pairFstCode
    (CodeTuple.one payloadOfCode)

def constValueOfCode : PrimCode N.one :=
  PrimCode.comp
    pairSndCode
    (CodeTuple.one payloadOfCode)

def projArityOfCode : PrimCode N.one :=
  PrimCode.comp
    pairFstCode
    (CodeTuple.one payloadOfCode)

def projIndexOfCode : PrimCode N.one :=
  PrimCode.comp
    pairSndCode
    (CodeTuple.one payloadOfCode)

def compSourceArityOfCode : PrimCode N.one :=
  PrimCode.comp
    pairFstCode
    (CodeTuple.one payloadOfCode)

def compPayloadTailCode : PrimCode N.one :=
  PrimCode.comp
    pairSndCode
    (CodeTuple.one payloadOfCode)

def compHeadOfCode : PrimCode N.one :=
  PrimCode.comp
    pairFstCode
    (CodeTuple.one compPayloadTailCode)

def compArgsOfCode : PrimCode N.one :=
  PrimCode.comp
    pairSndCode
    (CodeTuple.one compPayloadTailCode)

def recInitOfCode : PrimCode N.one :=
  PrimCode.comp
    pairFstCode
    (CodeTuple.one payloadOfCode)

def recStepOfCode : PrimCode N.one :=
  PrimCode.comp
    pairSndCode
    (CodeTuple.one payloadOfCode)

def muBodyOfCode : PrimCode N.one :=
  payloadOfCode

/-! ### Primitive-recursive codes for certificate-code operations -/

def certMkPayloadCode : PrimCode N.three :=
  PrimCode.comp
    pairCode
    (CodeTuple.two
      proj3_2
      proj3_3)

def certMkCode : PrimCode N.three :=
  PrimCode.comp
    consCodeCode
    (CodeTuple.two
      proj3_1
      certMkPayloadCode)

def certTagCode : PrimCode N.one :=
  PrimCode.comp
    pairFstCode
    (CodeTuple.one
      (PrimCode.comp
        predCode
        (CodeTuple.one proj1_1)))

def certPayloadTailCode : PrimCode N.one :=
  PrimCode.comp
    pairSndCode
    (CodeTuple.one
      (PrimCode.comp
        predCode
        (CodeTuple.one proj1_1)))

def certOutCode : PrimCode N.one :=
  PrimCode.comp
    pairFstCode
    (CodeTuple.one certPayloadTailCode)

def certPayloadCode : PrimCode N.one :=
  PrimCode.comp
    pairSndCode
    (CodeTuple.one certPayloadTailCode)

def certZeroMkCode : PrimCode N.two :=
  PrimCode.comp
    certMkCode
    (CodeTuple.three
      (constCode (k := N.two) ctZero)
      proj2_1
      proj2_2)

def certConstMkCode : PrimCode N.two :=
  PrimCode.comp
    certMkCode
    (CodeTuple.three
      (constCode (k := N.two) ctConst)
      proj2_1
      proj2_2)

def certSuccMkCode : PrimCode N.two :=
  PrimCode.comp
    certMkCode
    (CodeTuple.three
      (constCode (k := N.two) ctSucc)
      proj2_1
      proj2_2)

def certProjMkCode : PrimCode N.two :=
  PrimCode.comp
    certMkCode
    (CodeTuple.three
      (constCode (k := N.two) ctProj)
      proj2_1
      proj2_2)

def certCompMkCode : PrimCode N.two :=
  PrimCode.comp
    certMkCode
    (CodeTuple.three
      (constCode (k := N.two) ctComp)
      proj2_1
      proj2_2)

def certRecZeroMkCode : PrimCode N.two :=
  PrimCode.comp
    certMkCode
    (CodeTuple.three
      (constCode (k := N.two) ctRecZero)
      proj2_1
      proj2_2)

def certRecSuccMkCode : PrimCode N.two :=
  PrimCode.comp
    certMkCode
    (CodeTuple.three
      (constCode (k := N.two) ctRecSucc)
      proj2_1
      proj2_2)

def certMuMkCode : PrimCode N.two :=
  PrimCode.comp
    certMkCode
    (CodeTuple.three
      (constCode (k := N.two) ctMu)
      proj2_1
      proj2_2)

/-! ### Primitive-recursive code for certificate-output lists -/

/-
  certOutListIterCode(m,cs) computes

    [certOut(nth cs 0), ..., certOut(nth cs (m - 1))].
-/

def certOutListStepNthCode : PrimCode N.three :=
  PrimCode.comp
    nthCode
    (CodeTuple.two
      proj3_3
      proj3_1)

def certOutListStepSingletonCode : PrimCode N.three :=
  PrimCode.comp
    singletonCodeCode
    (CodeTuple.one
      (PrimCode.comp
        certOutCode
        (CodeTuple.one certOutListStepNthCode)))

def certOutListStepCode : PrimCode N.three :=
  PrimCode.comp
    appendCode
    (CodeTuple.two
      proj3_2
      certOutListStepSingletonCode)

def certOutListIterCode : PrimCode N.two :=
  PrimCode.prec
    (constCode (k := N.one) nilCode)
    certOutListStepCode

def certOutListCode : PrimCode N.two :=
  PrimCode.comp
    certOutListIterCode
    (CodeTuple.two
      proj2_2
      proj2_1)

end Arithmetization
end Arithmetic
end SyntheticComputability
