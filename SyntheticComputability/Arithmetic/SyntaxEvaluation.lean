import SyntheticComputability.Arithmetic.Arithmetization

namespace SyntheticComputability
namespace Arithmetic
namespace SyntaxEvaluation

open PrimitiveComputable
open PartialComputable
open Arithmetization

/-!
# Syntax and Evaluation: flat-trace replacement

The old tree-shaped semantic evaluator has been replaced by a numerical
flat-trace checker.  A trace is a numerical list of nodes.  Each node records
one local evaluation judgment

    expression-code `e` evaluates on list-coded input `xs` with output `out`.

Subcomputations are referenced by earlier node indices.  Therefore validation
of a trace is a bounded primitive-recursive scan over node positions.

The universal evaluator `U` is obtained by minimization over traces accepted by
this primitive-recursive checker, followed by primitive-recursive extraction of
the final node output.
-/

/-! ## Non-reducing equality and basic Prop-level relations -/

inductive EqN : N -> N -> Prop where
  | refl (a : N) : EqN a a

namespace EqN

theorem to_eq {a b : N} : EqN a b -> a = b
  | EqN.refl _ => rfl

theorem of_eq {a b : N} (h : a = b) : EqN a b := by
  cases h
  exact EqN.refl a

theorem symm {a b : N} (h : EqN a b) : EqN b a := by
  cases h
  exact EqN.refl a

theorem trans {a b c : N} (h₁ : EqN a b) (h₂ : EqN b c) : EqN a c := by
  cases h₁
  exact h₂

end EqN

structure EqNT (a b : N) : Type where
  proof : EqN a b

inductive LtN : N -> N -> Prop where
  | zeroSucc (b : N) : LtN N.zero (N.succ b)
  | succ {a b : N} (h : LtN a b) : LtN (N.succ a) (N.succ b)

namespace LtN

theorem not_lt_zero (a : N) : ¬ LtN a N.zero := by
  intro h
  cases h

theorem succ_inj {a b : N} (h : LtN (N.succ a) (N.succ b)) : LtN a b := by
  cases h with
  | succ h' => exact h'

theorem irrefl : (a : N) -> ¬ LtN a a
  | N.zero => by
      intro h
      cases h
  | N.succ a => by
      intro h
      exact irrefl a (succ_inj h)

theorem lt_succ_cases :
    {q m : N} -> LtN q (N.succ m) -> q = m ∨ LtN q m
  | N.zero, N.zero, _ => Or.inl rfl
  | N.zero, N.succ m, _ => Or.inr (LtN.zeroSucc m)
  | N.succ q, N.zero, h => by
      cases h with
      | succ h' => exact False.elim (not_lt_zero q h')
  | N.succ q, N.succ m, h => by
      cases h with
      | succ h' =>
          cases lt_succ_cases (q := q) (m := m) h' with
          | inl heq => exact Or.inl (congrArg N.succ heq)
          | inr hlt => exact Or.inr (LtN.succ hlt)

end LtN

inductive ZeroN : N -> Prop where
  | intro : ZeroN N.zero

inductive NonzeroN : N -> Prop where
  | succ (a : N) : NonzeroN (N.succ a)

/-! ## Evaluation input-code helpers -/

def twoListCode (a b : N) : N :=
  consCode a (singletonCode b)

def recInputCode (n as : N) : N :=
  consCode n as

def recStepInputCode (n y as : N) : N :=
  consCode n (consCode y as)

def muBodyInputCode (n xs : N) : N :=
  consCode n xs

def twoListCodeCode : PrimCode N.two :=
  PrimCode.comp
    consCodeCode
    (CodeTuple.two
      proj2_1
      (PrimCode.comp singletonCodeCode (CodeTuple.one proj2_2)))

def recInputCodeCode : PrimCode N.two :=
  consCodeCode

def recStepInputCodeCode : PrimCode N.three :=
  PrimCode.comp
    consCodeCode
    (CodeTuple.two
      proj3_1
      (PrimCode.comp
        consCodeCode
        (CodeTuple.two proj3_2 proj3_3)))

def muBodyInputCodeCode : PrimCode N.two :=
  consCodeCode

/-! ## Additional arities and projections -/

def arity5 : N :=
  N.succ arity4

def arity6 : N :=
  N.succ arity5

def arity7 : N :=
  N.succ arity6

def ixFourth5 : Vec.Ix arity5 :=
  Vec.Ix.succ (Vec.Ix.succ (Vec.Ix.succ Vec.Ix.zero))

def ixFifth : Vec.Ix arity5 :=
  Vec.Ix.succ ixFourth

def ixFourth6 : Vec.Ix arity6 :=
  Vec.Ix.succ (Vec.Ix.succ (Vec.Ix.succ Vec.Ix.zero))

def ixFifth6 : Vec.Ix arity6 :=
  Vec.Ix.succ ixFourth5

def ixSixth : Vec.Ix arity6 :=
  Vec.Ix.succ ixFifth

def ixFourth7 : Vec.Ix arity7 :=
  Vec.Ix.succ (Vec.Ix.succ (Vec.Ix.succ Vec.Ix.zero))

def ixFifth7 : Vec.Ix arity7 :=
  Vec.Ix.succ ixFourth6

def ixSixth7 : Vec.Ix arity7 :=
  Vec.Ix.succ ixFifth6

def ixSeventh : Vec.Ix arity7 :=
  Vec.Ix.succ ixSixth

def proj5_1 : PrimCode arity5 := PrimCode.proj Vec.Ix.first
def proj5_2 : PrimCode arity5 := PrimCode.proj Vec.Ix.second
def proj5_3 : PrimCode arity5 := PrimCode.proj Vec.Ix.third
def proj5_4 : PrimCode arity5 := PrimCode.proj ixFourth5
def proj5_5 : PrimCode arity5 := PrimCode.proj ixFifth

def proj6_1 : PrimCode arity6 := PrimCode.proj Vec.Ix.first
def proj6_2 : PrimCode arity6 := PrimCode.proj Vec.Ix.second
def proj6_3 : PrimCode arity6 := PrimCode.proj Vec.Ix.third
def proj6_4 : PrimCode arity6 := PrimCode.proj ixFourth6
def proj6_5 : PrimCode arity6 := PrimCode.proj ixFifth6
def proj6_6 : PrimCode arity6 := PrimCode.proj ixSixth

def proj7_1 : PrimCode arity7 := PrimCode.proj Vec.Ix.first
def proj7_2 : PrimCode arity7 := PrimCode.proj Vec.Ix.second
def proj7_3 : PrimCode arity7 := PrimCode.proj Vec.Ix.third
def proj7_4 : PrimCode arity7 := PrimCode.proj ixFourth7
def proj7_5 : PrimCode arity7 := PrimCode.proj ixFifth7
def proj7_6 : PrimCode arity7 := PrimCode.proj ixSixth7
def proj7_7 : PrimCode arity7 := PrimCode.proj ixSeventh

namespace CodeTuple

/--
Given step arguments `(i, acc, x₀, ..., xₖ₋₁)`, build the tuple
`(i, x₀, ..., xₖ₋₁)`, dropping the accumulator coordinate.  This is the tuple
transform needed for bounded primitive-recursive products.
-/
def dropSecond {k : N} :
    Vec.Ix (N.succ k) -> PrimCode (N.succ (N.succ k))
  | Vec.Ix.zero => PrimCode.proj Vec.Ix.first
  | Vec.Ix.succ i => PrimCode.proj (Vec.Ix.succ (Vec.Ix.succ i))

end CodeTuple

/-! ## Generic code combinators -/

namespace C

def unary {k : N} (f : PrimCode N.one) (a : PrimCode k) : PrimCode k :=
  PrimCode.comp f (CodeTuple.one a)

def binary {k : N} (f : PrimCode N.two) (a b : PrimCode k) : PrimCode k :=
  PrimCode.comp f (CodeTuple.two a b)

def ternary {k : N}
    (f : PrimCode N.three) (a b c : PrimCode k) : PrimCode k :=
  PrimCode.comp f (CodeTuple.three a b c)

def fst {k : N} (a : PrimCode k) : PrimCode k :=
  unary pairFstCode a

def snd {k : N} (a : PrimCode k) : PrimCode k :=
  unary pairSndCode a

def pred {k : N} (a : PrimCode k) : PrimCode k :=
  unary predCode a

def succ {k : N} (a : PrimCode k) : PrimCode k :=
  PrimCode.comp PrimCode.succ (CodeTuple.one a)

def pair {k : N} (a b : PrimCode k) : PrimCode k :=
  binary pairCode a b

def cons {k : N} (a b : PrimCode k) : PrimCode k :=
  binary consCodeCode a b

def singleton {k : N} (a : PrimCode k) : PrimCode k :=
  unary singletonCodeCode a

def append {k : N} (a b : PrimCode k) : PrimCode k :=
  binary appendCode a b

def nth {k : N} (xs i : PrimCode k) : PrimCode k :=
  binary nthCode xs i

def len {k : N} (xs : PrimCode k) : PrimCode k :=
  unary lenCode xs

def eq {k : N} (a b : PrimCode k) : PrimCode k :=
  binary eqNCode a b

def lt {k : N} (a b : PrimCode k) : PrimCode k :=
  binary ltNCode a b

def nz {k : N} (a : PrimCode k) : PrimCode k :=
  unary neqZeroNCode a

def isz {k : N} (a : PrimCode k) : PrimCode k :=
  unary isZeroCode a

def and {k : N} (a b : PrimCode k) : PrimCode k :=
  binary mulCode a b

def or {k : N} (a b : PrimCode k) : PrimCode k :=
  unary sgCode (binary addCode a b)

def not {k : N} (a : PrimCode k) : PrimCode k :=
  unary isZeroCode a

def and3 {k : N} (a b c : PrimCode k) : PrimCode k :=
  and (and a b) c

def and4 {k : N} (a b c d : PrimCode k) : PrimCode k :=
  and (and3 a b c) d

def and5 {k : N} (a b c d e : PrimCode k) : PrimCode k :=
  and (and4 a b c d) e

def and6 {k : N} (a b c d e f : PrimCode k) : PrimCode k :=
  and (and5 a b c d e) f

def and7 {k : N} (a b c d e f g : PrimCode k) : PrimCode k :=
  and (and6 a b c d e f) g

def and8 {k : N} (a b c d e f g h : PrimCode k) : PrimCode k :=
  and (and7 a b c d e f g) h

def and9 {k : N} (a b c d e f g h i : PrimCode k) : PrimCode k :=
  and (and8 a b c d e f g h) i

def or3 {k : N} (a b c : PrimCode k) : PrimCode k :=
  or (or a b) c

def or4 {k : N} (a b c d : PrimCode k) : PrimCode k :=
  or (or3 a b c) d

def or5 {k : N} (a b c d e : PrimCode k) : PrimCode k :=
  or (or4 a b c d) e

def or6 {k : N} (a b c d e f : PrimCode k) : PrimCode k :=
  or (or5 a b c d e) f

def or7 {k : N} (a b c d e f g : PrimCode k) : PrimCode k :=
  or (or6 a b c d e f) g

def or8 {k : N} (a b c d e f g h : PrimCode k) : PrimCode k :=
  or (or7 a b c d e f g) h

end C

/-! ## Bounded primitive-recursive conjunction -/

/--
`boundedAllCode p` computes the bounded product

    Π_{i < n} p(i, params).

The input arity is `(n, params)`.  The predicate code `p` has input arity
`(i, params)`.
-/
def boundedAllCode {k : N} (p : PrimCode (N.succ k)) : PrimCode (N.succ k) :=
  PrimCode.prec
    (constCode (k := k) N.one)
    (C.and
      (PrimCode.proj Vec.Ix.second)
      (PrimCode.comp p CodeTuple.dropSecond))

/-! ## Flat trace node coding -/

def ntZero : N := num0
def ntConst : N := num1
def ntSucc : N := num2
def ntProj : N := num3
def ntComp : N := num4
def ntRecZero : N := num5
def ntRecSucc : N := num6
def ntMu : N := num7

def nodeMk (kind e xs out payload : N) : N :=
  pair kind (pair e (pair xs (pair out payload)))

def nodeKind (z : N) : N :=
  pairFst z

def nodeExpr (z : N) : N :=
  pairFst (pairSnd z)

def nodeInput (z : N) : N :=
  pairFst (pairSnd (pairSnd z))

def nodeOut (z : N) : N :=
  pairFst (pairSnd (pairSnd (pairSnd z)))

def nodePayload (z : N) : N :=
  pairSnd (pairSnd (pairSnd (pairSnd z)))

@[simp]
theorem nodeKind_nodeMk (kind e xs out payload : N) :
    nodeKind (nodeMk kind e xs out payload) = kind := by
  simp [nodeKind, nodeMk]

@[simp]
theorem nodeExpr_nodeMk (kind e xs out payload : N) :
    nodeExpr (nodeMk kind e xs out payload) = e := by
  simp [nodeExpr, nodeMk]

@[simp]
theorem nodeInput_nodeMk (kind e xs out payload : N) :
    nodeInput (nodeMk kind e xs out payload) = xs := by
  simp [nodeInput, nodeMk]

@[simp]
theorem nodeOut_nodeMk (kind e xs out payload : N) :
    nodeOut (nodeMk kind e xs out payload) = out := by
  simp [nodeOut, nodeMk]

@[simp]
theorem nodePayload_nodeMk (kind e xs out payload : N) :
    nodePayload (nodeMk kind e xs out payload) = payload := by
  simp [nodePayload, nodeMk]

def nodeMkCode : PrimCode arity5 :=
  C.pair
    proj5_1
    (C.pair
      proj5_2
      (C.pair
        proj5_3
        (C.pair proj5_4 proj5_5)))

def nodeKindCode : PrimCode N.one :=
  pairFstCode

def nodeExprCode : PrimCode N.one :=
  C.fst (C.snd proj1_1)

def nodeInputCode : PrimCode N.one :=
  C.fst (C.snd (C.snd proj1_1))

def nodeOutCode : PrimCode N.one :=
  C.fst (C.snd (C.snd (C.snd proj1_1)))

def nodePayloadCode : PrimCode N.one :=
  C.snd (C.snd (C.snd (C.snd proj1_1)))

/-! ## Node-field pullbacks -/

def nodeAtCode {k : N} (tr j : PrimCode k) : PrimCode k :=
  C.nth tr j

def nodeKindAtCode {k : N} (tr j : PrimCode k) : PrimCode k :=
  C.unary nodeKindCode (nodeAtCode tr j)

def nodeExprAtCode {k : N} (tr j : PrimCode k) : PrimCode k :=
  C.unary nodeExprCode (nodeAtCode tr j)

def nodeInputAtCode {k : N} (tr j : PrimCode k) : PrimCode k :=
  C.unary nodeInputCode (nodeAtCode tr j)

def nodeOutAtCode {k : N} (tr j : PrimCode k) : PrimCode k :=
  C.unary nodeOutCode (nodeAtCode tr j)

def nodePayloadAtCode {k : N} (tr j : PrimCode k) : PrimCode k :=
  C.unary nodePayloadCode (nodeAtCode tr j)

/-! ## Payload destructors as code expressions -/

def payload0 {k : N} (p : PrimCode k) : PrimCode k := p

def payloadFst {k : N} (p : PrimCode k) : PrimCode k := C.fst p
def payloadSnd {k : N} (p : PrimCode k) : PrimCode k := C.snd p

/-! ## Node-output lists for flat traces -/

/--
`nodeOutList tr js m` is the list

    [nodeOut(nth tr (nth js 0)), ..., nodeOut(nth tr (nth js (m-1)))].
-/
def nodeOutList (tr js : N) : N -> N
  | N.zero => nilCode
  | N.succ i =>
      append
        (nodeOutList tr js i)
        (singletonCode (nodeOut (nth tr (nth js i))))

/-- Step code for `nodeOutList`: arguments are `(i, acc, tr, js)`. -/
def nodeOutListStepCode : PrimCode arity4 :=
  C.append
    proj4_2
    (C.singleton
      (C.unary nodeOutCode
        (C.nth
          proj4_3
          (C.nth proj4_4 proj4_1))))

/-- Input convention: `(m, tr, js)`. -/
def nodeOutListIterCode : PrimCode N.three :=
  PrimCode.prec
    (constCode (k := N.two) nilCode)
    nodeOutListStepCode

/-- Input convention: `(tr, js, m)`. -/
def nodeOutListCode : PrimCode N.three :=
  PrimCode.comp
    nodeOutListIterCode
    (CodeTuple.three proj3_3 proj3_1 proj3_2)

/-! ## Local bounded-reference checkers -/

/--
Argument-reference predicate for composition.

Input convention: `(i, tr, j, gs, xs, js)`.
-/
def compArgRefPredCode : PrimCode arity6 :=
  let i := proj6_1
  let tr := proj6_2
  let j := proj6_3
  let gs := proj6_4
  let xs := proj6_5
  let js := proj6_6
  let ji := C.nth js i
  C.and3
    (C.lt ji j)
    (C.eq (nodeExprAtCode tr ji) (C.nth gs i))
    (C.eq (nodeInputAtCode tr ji) xs)

/-- Input convention: `(m, tr, j, gs, xs, js)`. -/
def compArgsOKCode : PrimCode arity6 :=
  boundedAllCode compArgRefPredCode

/--
Minimization-prefix predicate.

Input convention: `(q, tr, j, g, xs, js)`.
-/
def muPrefixPredCode : PrimCode arity6 :=
  let q := proj6_1
  let tr := proj6_2
  let j := proj6_3
  let g := proj6_4
  let xs := proj6_5
  let js := proj6_6
  let jq := C.nth js q
  C.and4
    (C.lt jq j)
    (C.eq (nodeExprAtCode tr jq) g)
    (C.eq (nodeInputAtCode tr jq) (C.cons q xs))
    (C.nz (nodeOutAtCode tr jq))

/-- Input convention: `(n, tr, j, g, xs, js)`. -/
def muPrefixOKCode : PrimCode arity6 :=
  boundedAllCode muPrefixPredCode

/-! ## Local node checker -/

/--
`traceNodeOKCode(tr,j) = 1` means the `j`-th node of `tr` is locally valid
relative to earlier nodes of `tr`.
-/
def traceNodeOKCode : PrimCode N.two :=
  let tr := proj2_1
  let j := proj2_2
  let z := nodeAtCode tr j
  let kind := C.unary nodeKindCode z
  let e := C.unary nodeExprCode z
  let xs := C.unary nodeInputCode z
  let out := C.unary nodeOutCode z
  let p := C.unary nodePayloadCode z

  let zeroK := p
  let zeroCase : PrimCode N.two :=
    C.and4
      (C.eq kind (constCode (k := N.two) ntZero))
      (C.eq e (C.unary codeZeroCode zeroK))
      (C.eq (C.len xs) zeroK)
      (C.eq out (constCode (k := N.two) N.zero))

  let constK := C.fst p
  let constA := C.snd p
  let constCase : PrimCode N.two :=
    C.and4
      (C.eq kind (constCode (k := N.two) ntConst))
      (C.eq e (C.binary codeConstCode constK constA))
      (C.eq (C.len xs) constK)
      (C.eq out constA)

  let succCase : PrimCode N.two :=
    C.and4
      (C.eq kind (constCode (k := N.two) ntSucc))
      (C.eq e (constCode (k := N.two) codeSucc))
      (C.eq (C.len xs) (constCode (k := N.two) N.one))
      (C.eq out (C.succ (C.nth xs (constCode (k := N.two) N.zero))))

  let projK := C.fst p
  let projI := C.snd p
  let projCase : PrimCode N.two :=
    C.and5
      (C.eq kind (constCode (k := N.two) ntProj))
      (C.eq e (C.binary codeProjCode projK projI))
      (C.eq (C.len xs) projK)
      (C.lt projI projK)
      (C.eq out (C.nth xs projI))

  let compR := C.fst p
  let compTail1 := C.snd p
  let compH := C.fst compTail1
  let compTail2 := C.snd compTail1
  let compGs := C.fst compTail2
  let compTail3 := C.snd compTail2
  let compJs := C.fst compTail3
  let compJd := C.snd compTail3
  let compM := C.len compGs
  let compHeadInput := C.ternary nodeOutListCode tr compJs compM
  let compArgsCheck : PrimCode N.two :=
    PrimCode.comp
      compArgsOKCode
      (fun
        | Vec.Ix.zero => compM
        | Vec.Ix.succ Vec.Ix.zero => tr
        | Vec.Ix.succ (Vec.Ix.succ Vec.Ix.zero) => j
        | Vec.Ix.succ (Vec.Ix.succ (Vec.Ix.succ Vec.Ix.zero)) => compGs
        | Vec.Ix.succ (Vec.Ix.succ (Vec.Ix.succ (Vec.Ix.succ Vec.Ix.zero))) => xs
        | Vec.Ix.succ (Vec.Ix.succ (Vec.Ix.succ (Vec.Ix.succ (Vec.Ix.succ Vec.Ix.zero)))) => compJs)
  let compCase : PrimCode N.two :=
    C.and9
      (C.eq kind (constCode (k := N.two) ntComp))
      (C.eq e (C.ternary codeCompCode compR compH compGs))
      (C.eq (C.len xs) compR)
      (C.eq (C.len compJs) compM)
      compArgsCheck
      (C.lt compJd j)
      (C.eq (nodeExprAtCode tr compJd) compH)
      (C.eq (nodeInputAtCode tr compJd) compHeadInput)
      (C.eq out (nodeOutAtCode tr compJd))

  let rzG := C.fst p
  let rzTail1 := C.snd p
  let rzH := C.fst rzTail1
  let rzTail2 := C.snd rzTail1
  let rzAs := C.fst rzTail2
  let rzJd := C.snd rzTail2
  let recZeroCase : PrimCode N.two :=
    C.and7
      (C.eq kind (constCode (k := N.two) ntRecZero))
      (C.eq e (C.binary codeRecCode rzG rzH))
      (C.eq xs (C.cons (constCode (k := N.two) N.zero) rzAs))
      (C.lt rzJd j)
      (C.eq (nodeExprAtCode tr rzJd) rzG)
      (C.eq (nodeInputAtCode tr rzJd) rzAs)
      (C.eq out (nodeOutAtCode tr rzJd))

  let rsG := C.fst p
  let rsTail1 := C.snd p
  let rsH := C.fst rsTail1
  let rsTail2 := C.snd rsTail1
  let rsAs := C.fst rsTail2
  let rsTail3 := C.snd rsTail2
  let rsN := C.fst rsTail3
  let rsTail4 := C.snd rsTail3
  let rsJrec := C.fst rsTail4
  let rsJstep := C.snd rsTail4
  let rsE := C.binary codeRecCode rsG rsH
  let recSuccCase : PrimCode N.two :=
    C.and9
      (C.eq kind (constCode (k := N.two) ntRecSucc))
      (C.eq e rsE)
      (C.eq xs (C.cons (C.succ rsN) rsAs))
      (C.lt rsJrec j)
      (C.eq (nodeExprAtCode tr rsJrec) rsE)
      (C.eq (nodeInputAtCode tr rsJrec) (C.cons rsN rsAs))
      (C.lt rsJstep j)
      (C.eq (nodeExprAtCode tr rsJstep) rsH)
      (C.and
        (C.eq
          (nodeInputAtCode tr rsJstep)
          (C.ternary recStepInputCodeCode rsN (nodeOutAtCode tr rsJrec) rsAs))
        (C.eq out (nodeOutAtCode tr rsJstep)))

  let muG := C.fst p
  let muTail1 := C.snd p
  let muN := C.fst muTail1
  let muJs := C.snd muTail1
  let muJz := C.nth muJs muN
  let muPrefixCheck : PrimCode N.two :=
    PrimCode.comp
      muPrefixOKCode
      (fun
        | Vec.Ix.zero => muN
        | Vec.Ix.succ Vec.Ix.zero => tr
        | Vec.Ix.succ (Vec.Ix.succ Vec.Ix.zero) => j
        | Vec.Ix.succ (Vec.Ix.succ (Vec.Ix.succ Vec.Ix.zero)) => muG
        | Vec.Ix.succ (Vec.Ix.succ (Vec.Ix.succ (Vec.Ix.succ Vec.Ix.zero))) => xs
        | Vec.Ix.succ (Vec.Ix.succ (Vec.Ix.succ (Vec.Ix.succ (Vec.Ix.succ Vec.Ix.zero)))) => muJs)
  let muCase : PrimCode N.two :=
    C.and9
      (C.eq kind (constCode (k := N.two) ntMu))
      (C.eq e (C.unary codeMuCode muG))
      (C.eq out muN)
      (C.eq (C.len muJs) (C.succ muN))
      muPrefixCheck
      (C.lt muJz j)
      (C.eq (nodeExprAtCode tr muJz) muG)
      (C.eq (nodeInputAtCode tr muJz) (C.cons muN xs))
      (C.isz (nodeOutAtCode tr muJz))

  let allCases : PrimCode N.two :=
    C.or
      (C.or
        (C.or
          (C.or zeroCase constCase)
          (C.or succCase projCase))
        (C.or
          (C.or compCase recZeroCase)
          recSuccCase))
      muCase
  allCases

/-! ## Whole-trace checker -/

/-- Predicate input convention: `(j, tr)`. -/
def traceNodeOKFlippedCode : PrimCode N.two :=
  PrimCode.comp
    traceNodeOKCode
    (CodeTuple.two proj2_2 proj2_1)

/--
`traceOKCode(tr) = 1` iff `tr` is nonempty and every node below `len tr` is
locally valid.
-/
def traceOKCode : PrimCode N.one :=
  C.and
    (C.nz (C.len proj1_1))
    (PrimCode.comp
      (boundedAllCode traceNodeOKFlippedCode)
      (CodeTuple.two
        (C.len proj1_1)
        proj1_1))

def traceFinalIndexCode : PrimCode N.one :=
  C.pred (C.len proj1_1)

def traceFinalNodeCode : PrimCode N.one :=
  C.nth proj1_1 traceFinalIndexCode

def traceFinalExprCode : PrimCode N.one :=
  C.unary nodeExprCode traceFinalNodeCode

def traceFinalInputCode : PrimCode N.one :=
  C.unary nodeInputCode traceFinalNodeCode

def traceFinalOutCode : PrimCode N.one :=
  C.unary nodeOutCode traceFinalNodeCode

/-- Input convention: `(tr, e, xs)`. -/
def traceAcceptCode : PrimCode N.three :=
  C.and3
    (C.unary traceOKCode proj3_1)
    (C.eq (C.unary traceFinalExprCode proj3_1) proj3_2)
    (C.eq (C.unary traceFinalInputCode proj3_1) proj3_3)

/--
Search body for minimization.  Input convention: `(tr, e, xs)`.  The output is
zero exactly when the trace is accepted.
-/
def certBadCode : PrimCode N.three :=
  C.not traceAcceptCode

/-! ## Computable universal evaluator -/

def certBadFun : NumFun N.three :=
  PrimCode.eval certBadCode

def certBadPart : PartFun N.three :=
  totalNum certBadFun

/--
The least accepted trace for `(e,xs)`, obtained by strict unbounded
minimization over the first coordinate of `certBadPart`.
-/
def leastTrace : PartFun N.two :=
  partMu certBadPart

def traceFinalOutFun : NumFun N.one :=
  PrimCode.eval traceFinalOutCode

def traceFinalOutPart : PartFun N.one :=
  totalNum traceFinalOutFun

/--
The universal evaluator.  It is partial because `leastTrace` is partial.
When a trace is found, the value is the output field of the final node.
-/
def U : PartFun N.two :=
  subst
    traceFinalOutPart
    (fun
      | Vec.Ix.zero => leastTrace)

theorem certBadPart_partComp :
    PartComp certBadPart :=
  PartComp.totalPrim (PrimCode.sound certBadCode)

theorem leastTrace_partComp :
    PartComp leastTrace :=
  PartComp.mu certBadPart_partComp

theorem traceFinalOutPart_partComp :
    PartComp traceFinalOutPart :=
  PartComp.totalPrim (PrimCode.sound traceFinalOutCode)

theorem U_partComp :
    PartComp U :=
  PartComp.subst
    traceFinalOutPart_partComp
    (fun
      | Vec.Ix.zero => leastTrace_partComp)

/-! ## Public evaluator interface -/

def UInput (e xs : N) : Vec N.two :=
  Vec.pair e xs

def UDom (e xs : N) : Type :=
  U.Dom (UInput e xs)

def UVal (e xs : N) (h : UDom e xs) : N :=
  U.val (UInput e xs) h

def Eval (e xs y : N) : Type :=
  Sigma fun h : UDom e xs => EqNT (UVal e xs h) y

def EvalOnVec {k : N} (e : N) (args : Vec k) (y : N) : Type :=
  Eval e (listCode args) y

def UOnVec {k : N} (e : N) (args : Vec k) : PartFun N.zero where
  Dom := fun _ => UDom e (listCode args)
  val := fun _ h => UVal e (listCode args) h
  val_ext := by
    intro x y p h₁ h₂
    cases p
    exact U.val_ext rfl h₁ h₂

def UVecDom {k : N} (e : N) (args : Vec k) : Type :=
  UDom e (listCode args)

def UVecVal {k : N} (e : N) (args : Vec k) (h : UVecDom e args) : N :=
  UVal e (listCode args) h

end SyntaxEvaluation
end Arithmetic
end SyntheticComputability
