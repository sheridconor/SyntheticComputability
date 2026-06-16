namespace SyntheticComputability
namespace PrimitiveComputable

/-
  A bare natural numbers object.

  We deliberately do not use Lean's built-in Nat.
-/

inductive N : Type where
  | zero : N
  | succ : N -> N

namespace N

def one : N :=
  succ zero

def two : N :=
  succ one

def three : N :=
  succ two

/-
  Basic recursive operations on our natural numbers.

  These are not assumed primitive computable. Later we define primitive
  computability structurally and prove the corresponding numerical maps belong
  to that closure class.
-/

def add : N -> N -> N
  | zero, b => b
  | succ a, b => succ (add a b)

def mul : N -> N -> N
  | zero, _ => zero
  | succ a, b => add (mul a b) b

def pred : N -> N
  | zero => zero
  | succ n => n

def tsub : N -> N -> N
  | a, zero => a
  | a, succ b => pred (tsub a b)

def sg : N -> N
  | zero => zero
  | succ _ => one

def isZero : N -> N
  | zero => one
  | succ _ => zero

end N

/-
  Finite powers of N.

  Vec k represents N^k.
-/

inductive Vec : N -> Type where
  | nil : Vec N.zero
  | cons {k : N} : N -> Vec k -> Vec (N.succ k)

namespace Vec

/-
  Finite indices.

  Ix k is the type of coordinate indices for Vec k.
-/

inductive Ix : N -> Type where
  | zero {k : N} : Ix (N.succ k)
  | succ {k : N} : Ix k -> Ix (N.succ k)

namespace Ix

def first {k : N} : Ix (N.succ k) :=
  zero

def second {k : N} : Ix (N.succ (N.succ k)) :=
  succ zero

def third {k : N} : Ix (N.succ (N.succ (N.succ k))) :=
  succ (succ zero)

end Ix

def head {k : N} : Vec (N.succ k) -> N
  | cons n _ => n

def tail {k : N} : Vec (N.succ k) -> Vec k
  | cons _ xs => xs

def get : {k : N} -> Vec k -> Ix k -> N
  | N.zero, _, i => nomatch i
  | N.succ _, cons n _, Ix.zero => n
  | N.succ _, cons _ xs, Ix.succ i => get xs i

def singleton (a : N) : Vec N.one :=
  cons a nil

def pair (a b : N) : Vec N.two :=
  cons a (cons b nil)

def triple (a b c : N) : Vec N.three :=
  cons a (cons b (cons c nil))

/-
  Evaluate a tuple of k-ary numerical functions at one input.

  If gs : Ix m -> Vec k -> N, then mapEval gs xs is the vector
  whose i-th coordinate is gs i xs.
-/

def mapEval {k : N} : {m : N} -> (Ix m -> Vec k -> N) -> Vec k -> Vec m
  | N.zero, _, _ => nil
  | N.succ m, gs, xs =>
      cons
        (gs Ix.zero xs)
        (mapEval (m := m) (fun i => gs (Ix.succ i)) xs)

end Vec

/-
  k-ary numerical functions.
-/

abbrev NumFun (k : N) : Type :=
  Vec k -> N

/-
  Basic numerical function formers.
-/

def zeroFun (k : N) : NumFun k :=
  fun _ => N.zero

def constFun (k : N) (c : N) : NumFun k :=
  fun _ => c

def succFun : NumFun N.one :=
  fun xs => N.succ (Vec.head xs)

def projFun {k : N} (i : Vec.Ix k) : NumFun k :=
  fun xs => Vec.get xs i

def compFun {k m : N}
    (f : NumFun m)
    (gs : Vec.Ix m -> NumFun k) :
    NumFun k :=
  fun xs => f (Vec.mapEval gs xs)

/-
  Primitive recursion.

  Convention:
  primitive recursion is on the first coordinate.

  Thus if g : N^k -> N and h : N^(2+k) -> N, then

    precFun g h : N^(1+k) -> N

  satisfies

    precFun g h (0, xs)     = g xs
    precFun g h (S n, xs)   = h (n, precFun g h (n, xs), xs)

  This is equivalent to the last-coordinate convention in the manuscript,
  but it is more primitive for a cons-based vector representation.
-/

def primrecEval {k : N}
    (g : NumFun k)
    (h : NumFun (N.succ (N.succ k)))
    (xs : Vec k) :
    N -> N
  | N.zero => g xs
  | N.succ n =>
      h (Vec.cons n (Vec.cons (primrecEval g h xs n) xs))

def precFun {k : N}
    (g : NumFun k)
    (h : NumFun (N.succ (N.succ k))) :
    NumFun (N.succ k) :=
  fun xs => primrecEval g h (Vec.tail xs) (Vec.head xs)

/-
  Small tuple constructors for substitution.
-/

namespace Tuple

def one {k : N}
    (f : NumFun k) :
    Vec.Ix N.one -> NumFun k
  | Vec.Ix.zero => f

def two {k : N}
    (f g : NumFun k) :
    Vec.Ix N.two -> NumFun k
  | Vec.Ix.zero => f
  | Vec.Ix.succ Vec.Ix.zero => g

def three {k : N}
    (f g h : NumFun k) :
    Vec.Ix N.three -> NumFun k
  | Vec.Ix.zero => f
  | Vec.Ix.succ Vec.Ix.zero => g
  | Vec.Ix.succ (Vec.Ix.succ Vec.Ix.zero) => h

end Tuple

/-
  Proposition-level primitive-computability.

  Prim f is the structural closure certificate saying that f belongs to the
  primitive-recursive unary-output fragment.
-/

inductive Prim : {k : N} -> NumFun k -> Prop where
  | zero (k : N) :
      Prim (zeroFun k)

  | succ :
      Prim succFun

  | proj {k : N} (i : Vec.Ix k) :
      Prim (projFun i)

  | comp {k m : N}
      {f : NumFun m}
      {gs : Vec.Ix m -> NumFun k}
      (hf : Prim f)
      (hgs : (i : Vec.Ix m) -> Prim (gs i)) :
      Prim (compFun f gs)

  | prec {k : N}
      {g : NumFun k}
      {h : NumFun (N.succ (N.succ k))}
      (hg : Prim g)
      (hh : Prim h) :
      Prim (precFun g h)

/-
  First-class primitive-recursive codes.

  This closes the earlier gap where primitive computability was represented
  only by Prop-valued certificates. A PrimCode k is actual syntax for a
  primitive-recursive numerical map N^k -> N.
-/

inductive PrimCode : N -> Type where
  | zero (k : N) :
      PrimCode k

  | succ :
      PrimCode N.one

  | proj {k : N} :
      Vec.Ix k -> PrimCode k

  | comp {k m : N} :
      PrimCode m ->
      (Vec.Ix m -> PrimCode k) ->
      PrimCode k

  | prec {k : N} :
      PrimCode k ->
      PrimCode (N.succ (N.succ k)) ->
      PrimCode (N.succ k)

namespace PrimCode

def eval : {k : N} -> PrimCode k -> NumFun k
  | _, PrimCode.zero k =>
      zeroFun k
  | _, PrimCode.succ =>
      succFun
  | _, PrimCode.proj i =>
      projFun i
  | _, PrimCode.comp f gs =>
      compFun
        (eval f)
        (fun i => eval (gs i))
  | _, PrimCode.prec g h =>
      precFun
        (eval g)
        (eval h)

def sound : {k : N} -> (c : PrimCode k) -> Prim (eval c)
  | _, PrimCode.zero k =>
      Prim.zero k
  | _, PrimCode.succ =>
      Prim.succ
  | _, PrimCode.proj i =>
      Prim.proj i
  | _, PrimCode.comp f gs =>
      Prim.comp
        (f := eval f)
        (gs := fun i => eval (gs i))
        (sound f)
        (fun i => sound (gs i))
  | _, PrimCode.prec g h =>
      Prim.prec
        (g := eval g)
        (h := eval h)
        (sound g)
        (sound h)

end PrimCode

/-
  A code realises a numerical map when its evaluator is definitionally or
  propositionally equal to that map.
-/

def CodeRealizes {k : N} (c : PrimCode k) (f : NumFun k) : Prop :=
  PrimCode.eval c = f

theorem Prim.of_code {k : N}
    {c : PrimCode k}
    {f : NumFun k}
    (h : CodeRealizes c f) :
    Prim f := by
  rw [← h]
  exact PrimCode.sound c

/-
  Code-level tuple constructors.
-/

namespace CodeTuple

def one {k : N}
    (f : PrimCode k) :
    Vec.Ix N.one -> PrimCode k
  | Vec.Ix.zero => f

def two {k : N}
    (f g : PrimCode k) :
    Vec.Ix N.two -> PrimCode k
  | Vec.Ix.zero => f
  | Vec.Ix.succ Vec.Ix.zero => g

def three {k : N}
    (f g h : PrimCode k) :
    Vec.Ix N.three -> PrimCode k
  | Vec.Ix.zero => f
  | Vec.Ix.succ Vec.Ix.zero => g
  | Vec.Ix.succ (Vec.Ix.succ Vec.Ix.zero) => h

end CodeTuple

/-
  Tuple-valued primitive-recursive maps.

  This is the total numerical category fragment: a map N^k -> N^m is represented
  by m many primitive-recursive coordinate codes.
-/

structure PrimMap (k m : N) : Type where
  code : Vec.Ix m -> PrimCode k

namespace PrimMap

def eval {k m : N} (F : PrimMap k m) : Vec k -> Vec m :=
  Vec.mapEval (fun i => PrimCode.eval (F.code i))

def id (k : N) : PrimMap k k where
  code := fun i => PrimCode.proj i

def comp {k m l : N}
    (F : PrimMap m l)
    (G : PrimMap k m) :
    PrimMap k l where
  code := fun i =>
    PrimCode.comp
      (F.code i)
      G.code

def terminal (k : N) : PrimMap k N.zero where
  code := fun i => nomatch i

def fromCode {k : N} (c : PrimCode k) : PrimMap k N.one where
  code := CodeTuple.one c

def tuple {k m : N}
    (cs : Vec.Ix m -> PrimCode k) :
    PrimMap k m where
  code := cs

end PrimMap

/-
  Primitive constants.

  We give both a code-level construction and the old Prop-level certificate.
-/

def constCode {k : N} : N -> PrimCode k
  | N.zero =>
      PrimCode.zero k
  | N.succ c =>
      PrimCode.comp
        PrimCode.succ
        (CodeTuple.one (constCode c))

def primConst {k : N} : (c : N) -> Prim (constFun k c)
  | N.zero =>
      Prim.zero k
  | N.succ c =>
      Prim.comp
        (f := succFun)
        (gs := Tuple.one (constFun k c))
        Prim.succ
        (fun
          | Vec.Ix.zero => primConst c)

/-
  Addition.

  addFun has arity two and computes

    addFun (n, x) = n + x.

  It is obtained by primitive recursion on n.
-/

def addStepCode : PrimCode N.three :=
  PrimCode.comp
    PrimCode.succ
    (CodeTuple.one
      (PrimCode.proj Vec.Ix.second))

def addCode : PrimCode N.two :=
  PrimCode.prec
    (PrimCode.proj Vec.Ix.first)
    addStepCode

def addStep : NumFun N.three :=
  PrimCode.eval addStepCode

def addFun : NumFun N.two :=
  PrimCode.eval addCode

def prim_addStep : Prim addStep :=
  PrimCode.sound addStepCode

def prim_add : Prim addFun :=
  PrimCode.sound addCode

/-
  Multiplication.

  mulFun has arity two and computes

    mulFun (n, x) = n * x.

  It is obtained by primitive recursion on n:

    0 * x       = 0
    (S n) * x   = (n * x) + x
-/

def mulStepCode : PrimCode N.three :=
  PrimCode.comp
    addCode
    (CodeTuple.two
      (PrimCode.proj Vec.Ix.second)
      (PrimCode.proj Vec.Ix.third))

def mulCode : PrimCode N.two :=
  PrimCode.prec
    (PrimCode.zero N.one)
    mulStepCode

def mulStep : NumFun N.three :=
  PrimCode.eval mulStepCode

def mulFun : NumFun N.two :=
  PrimCode.eval mulCode

def prim_mulStep : Prim mulStep :=
  PrimCode.sound mulStepCode

def prim_mul : Prim mulFun :=
  PrimCode.sound mulCode

/-
  Predecessor.

    predFun 0       = 0
    predFun (S n)   = n
-/

def predStepCode : PrimCode N.two :=
  PrimCode.proj Vec.Ix.first

def predCode : PrimCode N.one :=
  PrimCode.prec
    (PrimCode.zero N.zero)
    predStepCode

def predStep : NumFun N.two :=
  PrimCode.eval predStepCode

def predFun : NumFun N.one :=
  PrimCode.eval predCode

def prim_predStep : Prim predStep :=
  PrimCode.sound predStepCode

def prim_pred : Prim predFun :=
  PrimCode.sound predCode

/-
  Truncated subtraction.

  Because primitive recursion is on the first coordinate, it is convenient to
  first define

    subFromFun (n, m) = m dotminus n.

  Then the usual ordering

    tsubFun (m, n) = m dotminus n

  is obtained by substitution/swap.
-/

def subFromStepCode : PrimCode N.three :=
  PrimCode.comp
    predCode
    (CodeTuple.one
      (PrimCode.proj Vec.Ix.second))

def subFromCode : PrimCode N.two :=
  PrimCode.prec
    (PrimCode.proj Vec.Ix.first)
    subFromStepCode

def tsubCode : PrimCode N.two :=
  PrimCode.comp
    subFromCode
    (CodeTuple.two
      (PrimCode.proj Vec.Ix.second)
      (PrimCode.proj Vec.Ix.first))

def subFromStep : NumFun N.three :=
  PrimCode.eval subFromStepCode

def subFromFun : NumFun N.two :=
  PrimCode.eval subFromCode

def tsubFun : NumFun N.two :=
  PrimCode.eval tsubCode

def prim_subFromStep : Prim subFromStep :=
  PrimCode.sound subFromStepCode

def prim_subFrom : Prim subFromFun :=
  PrimCode.sound subFromCode

def prim_tsub : Prim tsubFun :=
  PrimCode.sound tsubCode

/-
  Sign and zero-test.

    sg 0       = 0
    sg (S n)   = 1

    isZero 0       = 1
    isZero (S n)   = 0
-/

def sgStepCode : PrimCode N.two :=
  constCode N.one

def sgCode : PrimCode N.one :=
  PrimCode.prec
    (PrimCode.zero N.zero)
    sgStepCode

def isZeroStepCode : PrimCode N.two :=
  PrimCode.zero N.two

def isZeroCode : PrimCode N.one :=
  PrimCode.prec
    (constCode N.one)
    isZeroStepCode

def sgStep : NumFun N.two :=
  PrimCode.eval sgStepCode

def sgFun : NumFun N.one :=
  PrimCode.eval sgCode

def isZeroStep : NumFun N.two :=
  PrimCode.eval isZeroStepCode

def isZeroFun : NumFun N.one :=
  PrimCode.eval isZeroCode

def prim_sgStep : Prim sgStep :=
  PrimCode.sound sgStepCode

def prim_sg : Prim sgFun :=
  PrimCode.sound sgCode

def prim_isZeroStep : Prim isZeroStep :=
  PrimCode.sound isZeroStepCode

def prim_isZero : Prim isZeroFun :=
  PrimCode.sound isZeroCode

/-
  Numerical characteristic maps for order and equality.

  Truth is represented by 1 and falsity by 0.

    leqFun (m, n) = isZero (m dotminus n)
    ltFun  (m, n) = leqFun (S m, n)
    eqFun  (m, n) = leqFun (m, n) * leqFun (n, m)
-/

def leqCode : PrimCode N.two :=
  PrimCode.comp
    isZeroCode
    (CodeTuple.one tsubCode)

def succFirstCode : PrimCode N.two :=
  PrimCode.comp
    PrimCode.succ
    (CodeTuple.one
      (PrimCode.proj Vec.Ix.first))

def ltCode : PrimCode N.two :=
  PrimCode.comp
    leqCode
    (CodeTuple.two
      succFirstCode
      (PrimCode.proj Vec.Ix.second))

def leqSwappedCode : PrimCode N.two :=
  PrimCode.comp
    leqCode
    (CodeTuple.two
      (PrimCode.proj Vec.Ix.second)
      (PrimCode.proj Vec.Ix.first))

def eqCode : PrimCode N.two :=
  PrimCode.comp
    mulCode
    (CodeTuple.two
      leqCode
      leqSwappedCode)

def leqFun : NumFun N.two :=
  PrimCode.eval leqCode

def succFirstFun : NumFun N.two :=
  PrimCode.eval succFirstCode

def ltFun : NumFun N.two :=
  PrimCode.eval ltCode

def leqSwappedFun : NumFun N.two :=
  PrimCode.eval leqSwappedCode

def eqFun : NumFun N.two :=
  PrimCode.eval eqCode

def prim_leq : Prim leqFun :=
  PrimCode.sound leqCode

def prim_succFirst : Prim succFirstFun :=
  PrimCode.sound succFirstCode

def prim_lt : Prim ltFun :=
  PrimCode.sound ltCode

def prim_leqSwapped : Prim leqSwappedFun :=
  PrimCode.sound leqSwappedCode

def prim_eq : Prim eqFun :=
  PrimCode.sound eqCode

/-
  Semantic correctness of the primitive-computable representatives.

  These lemmas connect the structurally primitive-computable functions
  addFun, mulFun, predFun, tsubFun, sgFun, isZeroFun, leqFun, ltFun, eqFun
  with the concrete operations previously defined on N.
-/

@[simp]
theorem addFun_pair (n x : N) :
    addFun (Vec.pair n x) = N.add n x := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change N.succ (addFun (Vec.pair n x)) = N.succ (N.add n x)
      rw [ih]

@[simp]
theorem mulFun_pair (n x : N) :
    mulFun (Vec.pair n x) = N.mul n x := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        addFun (Vec.pair (mulFun (Vec.pair n x)) x)
          =
        N.add (N.mul n x) x
      rw [ih, addFun_pair]

@[simp]
theorem predFun_singleton (n : N) :
    predFun (Vec.singleton n) = N.pred n := by
  cases n with
  | zero =>
      rfl
  | succ n =>
      rfl

@[simp]
theorem subFromFun_pair (n m : N) :
    subFromFun (Vec.pair n m) = N.tsub m n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        predFun (Vec.singleton (subFromFun (Vec.pair n m)))
          =
        N.pred (N.tsub m n)
      rw [ih, predFun_singleton]

@[simp]
theorem tsubFun_pair (m n : N) :
    tsubFun (Vec.pair m n) = N.tsub m n := by
  change subFromFun (Vec.pair n m) = N.tsub m n
  exact subFromFun_pair n m

@[simp]
theorem sgFun_singleton (n : N) :
    sgFun (Vec.singleton n) = N.sg n := by
  cases n with
  | zero =>
      rfl
  | succ n =>
      rfl

@[simp]
theorem isZeroFun_singleton (n : N) :
    isZeroFun (Vec.singleton n) = N.isZero n := by
  cases n with
  | zero =>
      rfl
  | succ n =>
      rfl

@[simp]
theorem succFirstFun_pair (m n : N) :
    succFirstFun (Vec.pair m n) = N.succ m := by
  rfl

@[simp]
theorem leqFun_pair (m n : N) :
    leqFun (Vec.pair m n) = N.isZero (N.tsub m n) := by
  change
    isZeroFun (Vec.singleton (tsubFun (Vec.pair m n)))
      =
    N.isZero (N.tsub m n)
  rw [tsubFun_pair, isZeroFun_singleton]

@[simp]
theorem ltFun_pair (m n : N) :
    ltFun (Vec.pair m n) = N.isZero (N.tsub (N.succ m) n) := by
  change
    leqFun (Vec.pair (succFirstFun (Vec.pair m n)) n)
      =
    N.isZero (N.tsub (N.succ m) n)
  rw [succFirstFun_pair, leqFun_pair]

@[simp]
theorem leqSwappedFun_pair (m n : N) :
    leqSwappedFun (Vec.pair m n) = N.isZero (N.tsub n m) := by
  change leqFun (Vec.pair n m) = N.isZero (N.tsub n m)
  exact leqFun_pair n m

@[simp]
theorem eqFun_pair (m n : N) :
    eqFun (Vec.pair m n)
      =
    N.mul
      (N.isZero (N.tsub m n))
      (N.isZero (N.tsub n m)) := by
  change
    mulFun
      (Vec.pair
        (leqFun (Vec.pair m n))
        (leqSwappedFun (Vec.pair m n)))
      =
    N.mul
      (N.isZero (N.tsub m n))
      (N.isZero (N.tsub n m))
  rw [leqFun_pair, leqSwappedFun_pair, mulFun_pair]

end PrimitiveComputable
end SyntheticComputability
