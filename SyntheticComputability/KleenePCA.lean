import SyntheticComputability.Arithmetic.SyntaxEvaluation

namespace SyntheticComputability
namespace Arithmetic
namespace KleenePCA

open PrimitiveComputable
open PartialComputable
open Arithmetization
open SyntaxEvaluation

/-!
# Kleene PCA: semantic relations, quotation infrastructure, and application

This file contains only completed definitions and closed proofs.

It develops:

* semantic accessors for flat traces;
* semantic flat-trace correctness relations;
* semantic evaluation relations;
* basic order infrastructure for `LtN`;
* numerical coding of finite vector indices;
* basic facts about `listCode`;
* structural quotation of `PrimCode` into the raw numerical syntax consumed by
  the universal evaluator;
* a constructive domain witness for strict minimization over total bodies;
* partial application on natural numbers;
* structures for the applicative/PCA layers.

No unproved theorem declarations are used.

Important correction:

In the `PrimCode.comp` quotation case,

    PrimCode.comp {k m : N} : PrimCode m -> (Vec.Ix m -> PrimCode k) -> PrimCode k

is quoted as

    codeComp k qf qgs

not as `codeComp m qf qgs`.  The first numerical field of `codeComp` is the
source/input arity of the composite, i.e. `k`.
-/

/-! ## Semantic accessors mirroring the flat-trace checker -/

def traceNode (tr j : N) : N :=
  nth tr j

def traceFinalIndex (tr : N) : N :=
  N.pred (len tr)

def traceFinalNode (tr : N) : N :=
  nth tr (traceFinalIndex tr)

def traceFinalExpr (tr : N) : N :=
  nodeExpr (traceFinalNode tr)

def traceFinalInput (tr : N) : N :=
  nodeInput (traceFinalNode tr)

def traceFinalOut (tr : N) : N :=
  nodeOut (traceFinalNode tr)

/-! ## Elementary order and arithmetic infrastructure -/

theorem succ_inj_N {a b : N} :
    N.succ a = N.succ b -> a = b := by
  intro h
  cases h
  rfl

theorem add_zero_right : (n : N) -> N.add n N.zero = n
  | N.zero =>
      rfl
  | N.succ n => by
      change N.succ (N.add n N.zero) = N.succ n
      rw [add_zero_right n]

theorem add_one_right : (n : N) -> N.add n N.one = N.succ n
  | N.zero =>
      rfl
  | N.succ n => by
      change N.succ (N.add n N.one) = N.succ (N.succ n)
      rw [add_one_right n]

theorem ltN_trans {a b c : N} :
    LtN a b -> LtN b c -> LtN a c := by
  intro hab hbc
  induction hbc generalizing a with
  | zeroSucc b =>
      cases hab
  | succ hbc ih =>
      cases hab with
      | zeroSucc b =>
          exact LtN.zeroSucc _
      | succ hab' =>
          exact LtN.succ (ih hab')

theorem ltN_zero_lt_succ (n : N) :
    LtN N.zero (N.succ n) :=
  LtN.zeroSucc n

theorem ltN_succ_lt_succ {a b : N}
    (h : LtN a b) :
    LtN (N.succ a) (N.succ b) :=
  LtN.succ h

theorem lt_self_succ : (n : N) -> LtN n (N.succ n)
  | N.zero =>
      LtN.zeroSucc N.zero
  | N.succ n =>
      LtN.succ (lt_self_succ n)

theorem pred_lt_of_nonzero :
    {n : N} -> NonzeroN n -> LtN (N.pred n) n
  | N.zero, h => by
      cases h
  | N.succ n, _ => by
      change LtN n (N.succ n)
      exact lt_self_succ n

/-! ## Semantic flat-trace correctness relations -/

mutual

inductive FlatNodeOK : N -> N -> Prop where

  | zero
      (tr j k : N)
      (hkind :
        EqN (nodeKind (traceNode tr j)) ntZero)
      (hexpr :
        EqN (nodeExpr (traceNode tr j)) (codeZero k))
      (hinputLen :
        EqN (len (nodeInput (traceNode tr j))) k)
      (hout :
        EqN (nodeOut (traceNode tr j)) N.zero) :
      FlatNodeOK tr j

  | const
      (tr j k a : N)
      (hkind :
        EqN (nodeKind (traceNode tr j)) ntConst)
      (hexpr :
        EqN (nodeExpr (traceNode tr j)) (codeConst k a))
      (hinputLen :
        EqN (len (nodeInput (traceNode tr j))) k)
      (hout :
        EqN (nodeOut (traceNode tr j)) a) :
      FlatNodeOK tr j

  | succ
      (tr j xs out : N)
      (hkind :
        EqN (nodeKind (traceNode tr j)) ntSucc)
      (hexpr :
        EqN (nodeExpr (traceNode tr j)) codeSucc)
      (hinput :
        EqN xs (nodeInput (traceNode tr j)))
      (hlen :
        EqN (len xs) N.one)
      (hout :
        EqN out (N.succ (nth xs N.zero)))
      (houtNode :
        EqN (nodeOut (traceNode tr j)) out) :
      FlatNodeOK tr j

  | proj
      (tr j k i xs out : N)
      (hkind :
        EqN (nodeKind (traceNode tr j)) ntProj)
      (hexpr :
        EqN (nodeExpr (traceNode tr j)) (codeProj k i))
      (hinput :
        EqN xs (nodeInput (traceNode tr j)))
      (hlen :
        EqN (len xs) k)
      (hi :
        LtN i k)
      (hout :
        EqN out (nth xs i))
      (houtNode :
        EqN (nodeOut (traceNode tr j)) out) :
      FlatNodeOK tr j

  | comp
      (tr j r h gs xs out js jd m : N)
      (hkind :
        EqN (nodeKind (traceNode tr j)) ntComp)
      (hexpr :
        EqN (nodeExpr (traceNode tr j)) (codeComp r h gs))
      (hinput :
        EqN (nodeInput (traceNode tr j)) xs)
      (hlenXs :
        EqN (len xs) r)
      (hm :
        EqN m (len gs))
      (hlenJs :
        EqN (len js) m)
      (hargs :
        FlatArgRefs tr j gs xs js m)
      (hjdLt :
        LtN jd j)
      (hjdExpr :
        EqN (nodeExpr (traceNode tr jd)) h)
      (hjdInput :
        EqN (nodeInput (traceNode tr jd)) (nodeOutList tr js m))
      (hout :
        EqN (nodeOut (traceNode tr j)) (nodeOut (traceNode tr jd))) :
      FlatNodeOK tr j

  | recZero
      (tr j g h as jd : N)
      (hkind :
        EqN (nodeKind (traceNode tr j)) ntRecZero)
      (hexpr :
        EqN (nodeExpr (traceNode tr j)) (codeRec g h))
      (hinput :
        EqN (nodeInput (traceNode tr j)) (recInputCode N.zero as))
      (hjdLt :
        LtN jd j)
      (hjdExpr :
        EqN (nodeExpr (traceNode tr jd)) g)
      (hjdInput :
        EqN (nodeInput (traceNode tr jd)) as)
      (hout :
        EqN (nodeOut (traceNode tr j)) (nodeOut (traceNode tr jd))) :
      FlatNodeOK tr j

  | recSucc
      (tr j g h as n jrec jstep : N)
      (hkind :
        EqN (nodeKind (traceNode tr j)) ntRecSucc)
      (hexpr :
        EqN (nodeExpr (traceNode tr j)) (codeRec g h))
      (hinput :
        EqN (nodeInput (traceNode tr j)) (recInputCode (N.succ n) as))
      (hjrecLt :
        LtN jrec j)
      (hjrecExpr :
        EqN (nodeExpr (traceNode tr jrec)) (codeRec g h))
      (hjrecInput :
        EqN (nodeInput (traceNode tr jrec)) (recInputCode n as))
      (hjstepLt :
        LtN jstep j)
      (hjstepExpr :
        EqN (nodeExpr (traceNode tr jstep)) h)
      (hjstepInput :
        EqN
          (nodeInput (traceNode tr jstep))
          (recStepInputCode n (nodeOut (traceNode tr jrec)) as))
      (hout :
        EqN (nodeOut (traceNode tr j)) (nodeOut (traceNode tr jstep))) :
      FlatNodeOK tr j

  | mu
      (tr j g xs n js jz : N)
      (hkind :
        EqN (nodeKind (traceNode tr j)) ntMu)
      (hexpr :
        EqN (nodeExpr (traceNode tr j)) (codeMu g))
      (hinput :
        EqN (nodeInput (traceNode tr j)) xs)
      (hout :
        EqN (nodeOut (traceNode tr j)) n)
      (hlenJs :
        EqN (len js) (N.succ n))
      (hprefix :
        FlatMuPrefixRefs tr j g xs js n)
      (hjz :
        EqN jz (nth js n))
      (hjzLt :
        LtN jz j)
      (hjzExpr :
        EqN (nodeExpr (traceNode tr jz)) g)
      (hjzInput :
        EqN (nodeInput (traceNode tr jz)) (muBodyInputCode n xs))
      (hjzZero :
        ZeroN (nodeOut (traceNode tr jz))) :
      FlatNodeOK tr j

inductive FlatArgRefs : N -> N -> N -> N -> N -> N -> Prop where

  | nil
      (tr j gs xs js : N) :
      FlatArgRefs tr j gs xs js N.zero

  | snoc
      {tr j gs xs js m ji : N}
      (prev :
        FlatArgRefs tr j gs xs js m)
      (hji :
        EqN ji (nth js m))
      (hlt :
        LtN ji j)
      (hexpr :
        EqN (nodeExpr (traceNode tr ji)) (nth gs m))
      (hinput :
        EqN (nodeInput (traceNode tr ji)) xs) :
      FlatArgRefs tr j gs xs js (N.succ m)

inductive FlatMuPrefixRefs : N -> N -> N -> N -> N -> N -> Prop where

  | nil
      (tr j g xs js : N) :
      FlatMuPrefixRefs tr j g xs js N.zero

  | snoc
      {tr j g xs js m jq : N}
      (prev :
        FlatMuPrefixRefs tr j g xs js m)
      (hjq :
        EqN jq (nth js m))
      (hlt :
        LtN jq j)
      (hexpr :
        EqN (nodeExpr (traceNode tr jq)) g)
      (hinput :
        EqN (nodeInput (traceNode tr jq)) (muBodyInputCode m xs))
      (hnz :
        NonzeroN (nodeOut (traceNode tr jq))) :
      FlatMuPrefixRefs tr j g xs js (N.succ m)

end

def FlatTraceOK (tr : N) : Prop :=
  NonzeroN (len tr) ∧
  ∀ j : N, LtN j (len tr) -> FlatNodeOK tr j

def FlatAccept (tr e xs y : N) : Prop :=
  FlatTraceOK tr ∧
  EqN (traceFinalExpr tr) e ∧
  EqN (traceFinalInput tr) xs ∧
  EqN (traceFinalOut tr) y

/-! ## Semantic evaluation relation -/

mutual

inductive EvalRel : N -> N -> N -> Prop where

  | zero
      (e xs k : N)
      (he : EqN e (codeZero k))
      (hlen : EqN (len xs) k) :
      EvalRel e xs N.zero

  | const
      (e xs k a : N)
      (he : EqN e (codeConst k a))
      (hlen : EqN (len xs) k) :
      EvalRel e xs a

  | succ
      (e xs out : N)
      (he : EqN e codeSucc)
      (hlen : EqN (len xs) N.one)
      (hout : EqN out (N.succ (nth xs N.zero))) :
      EvalRel e xs out

  | proj
      (e xs k i out : N)
      (he : EqN e (codeProj k i))
      (hlen : EqN (len xs) k)
      (hi : LtN i k)
      (hout : EqN out (nth xs i)) :
      EvalRel e xs out

  | comp
      (e xs r h gs m ys out : N)
      (he : EqN e (codeComp r h gs))
      (hm : EqN m (len gs))
      (hlen : EqN (len xs) r)
      (hargs : EvalArgs gs xs m ys)
      (hh : EvalRel h ys out) :
      EvalRel e xs out

  | recZero
      (e xs g h as out : N)
      (he : EqN e (codeRec g h))
      (hxs : EqN xs (recInputCode N.zero as))
      (hg : EvalRel g as out) :
      EvalRel e xs out

  | recSucc
      (e xs g h as n prev out : N)
      (he : EqN e (codeRec g h))
      (hxs : EqN xs (recInputCode (N.succ n) as))
      (hprev :
        EvalRel e (recInputCode n as) prev)
      (hstep :
        EvalRel h (recStepInputCode n prev as) out) :
      EvalRel e xs out

  | mu
      (e xs g n : N)
      (he : EqN e (codeMu g))
      (hprefix : EvalMuPrefix g xs n)
      (hzero : EvalRel g (muBodyInputCode n xs) N.zero) :
      EvalRel e xs n

inductive EvalArgs : N -> N -> N -> N -> Prop where

  | nil
      (gs xs : N) :
      EvalArgs gs xs N.zero nilCode

  | snoc
      {gs xs m ys e out : N}
      (prev : EvalArgs gs xs m ys)
      (he : EqN e (nth gs m))
      (h : EvalRel e xs out) :
      EvalArgs gs xs (N.succ m) (append ys (singletonCode out))

inductive EvalMuPrefix : N -> N -> N -> Prop where

  | nil
      (g xs : N) :
      EvalMuPrefix g xs N.zero

  | snoc
      {g xs m out : N}
      (prev : EvalMuPrefix g xs m)
      (h : EvalRel g (muBodyInputCode m xs) out)
      (hnz : NonzeroN out) :
      EvalMuPrefix g xs (N.succ m)

end

/-! ## Numerical coding of finite indices -/

def ixCode : {k : N} -> Vec.Ix k -> N
  | N.zero, i =>
      nomatch i
  | N.succ _, Vec.Ix.zero =>
      N.zero
  | N.succ _, Vec.Ix.succ i =>
      N.succ (ixCode i)

def ixCode_lt :
    {k : N} -> (i : Vec.Ix k) -> LtN (ixCode i) k
  | N.zero, i =>
      nomatch i
  | N.succ k, Vec.Ix.zero =>
      LtN.zeroSucc k
  | N.succ _, Vec.Ix.succ i =>
      LtN.succ (ixCode_lt i)

/--
Weaken a finite index into a one-larger finite type.
-/
def ixWeaken :
    {m : N} -> Vec.Ix m -> Vec.Ix (N.succ m)
  | N.zero, i =>
      nomatch i
  | N.succ _, Vec.Ix.zero =>
      Vec.Ix.zero
  | N.succ _, Vec.Ix.succ i =>
      Vec.Ix.succ (ixWeaken i)

/--
The final index of a nonempty finite type.
-/
def ixLast : (m : N) -> Vec.Ix (N.succ m)
  | N.zero =>
      Vec.Ix.zero
  | N.succ m =>
      Vec.Ix.succ (ixLast m)

theorem ixCode_ixWeaken :
    {m : N} -> (i : Vec.Ix m) ->
      ixCode (ixWeaken i) = ixCode i
  | N.zero, i =>
      nomatch i
  | N.succ m, Vec.Ix.zero =>
      rfl
  | N.succ m, Vec.Ix.succ i => by
      change N.succ (ixCode (ixWeaken i)) = N.succ (ixCode i)
      rw [ixCode_ixWeaken i]

theorem ixCode_ixLast :
    (m : N) -> ixCode (ixLast m) = m
  | N.zero =>
      rfl
  | N.succ m => by
      change N.succ (ixCode (ixLast m)) = N.succ m
      rw [ixCode_ixLast m]

/-! ## Basic facts about `listCode` and append -/

@[simp]
theorem len_listCode :
    {k : N} -> (xs : Vec k) -> len (listCode xs) = k
  | N.zero, Vec.nil => by
      simp [listCode, nilCode, len]

  | N.succ k, Vec.cons x xs => by
      change len (consCode x (listCode xs)) = N.succ k
      rw [len_consCode]
      rw [len_listCode xs]

@[simp]
theorem nth_listCode_ixCode :
    {k : N} -> (xs : Vec k) -> (i : Vec.Ix k) ->
      nth (listCode xs) (ixCode i) = Vec.get xs i
  | N.zero, _, i =>
      nomatch i

  | N.succ k, Vec.cons x xs, Vec.Ix.zero => by
      change nth (consCode x (listCode xs)) N.zero = x
      rw [nth_zero_consCode]

  | N.succ k, Vec.cons x xs, Vec.Ix.succ i => by
      change
        nth (consCode x (listCode xs)) (N.succ (ixCode i))
        =
        Vec.get xs i
      rw [nth_succ_consCode]
      exact nth_listCode_ixCode xs i

theorem len_append :
    (xs ys : N) ->
      len (append xs ys) = N.add (len xs) (len ys)
  | N.zero, ys => by
      simp [append, len, N.add]

  | N.succ m, ys => by
      calc
        len (append (N.succ m) ys)
            = len (consCode (pairFst m) (append (pairSnd m) ys)) := by
                simp [append]
        _ = N.succ (len (append (pairSnd m) ys)) := by
                rw [len_consCode]
        _ = N.succ (N.add (len (pairSnd m)) (len ys)) := by
                rw [len_append (pairSnd m) ys]
        _ = N.add (len (N.succ m)) (len ys) := by
                simp [len, N.add]
termination_by xs _ => toNat xs
decreasing_by
  simpa [toNat] using pairSnd_lt_succ m

@[simp]
theorem len_singletonCode (x : N) :
    len (singletonCode x) = N.one := by
  change len (consCode x nilCode) = N.one
  rw [len_consCode]
  rw [len_nilCode]
  rfl

theorem len_append_singleton (xs x : N) :
    len (append xs (singletonCode x)) = N.succ (len xs) := by
  rw [len_append]
  rw [len_singletonCode]
  exact add_one_right (len xs)

theorem nth_append_singleton_at_len :
    (xs x : N) ->
      nth (append xs (singletonCode x)) (len xs) = x
  | N.zero, x => by
      simp [append, singletonCode, nilCode, len]

  | N.succ m, x => by
      calc
        nth (append (N.succ m) (singletonCode x)) (len (N.succ m))
            =
        nth
          (consCode
            (pairFst m)
            (append (pairSnd m) (singletonCode x)))
          (N.succ (len (pairSnd m))) := by
            simp [append, len]
        _ =
        nth (append (pairSnd m) (singletonCode x)) (len (pairSnd m)) := by
            rw [nth_succ_consCode]
        _ = x := by
            exact nth_append_singleton_at_len (pairSnd m) x
termination_by xs _ => toNat xs
decreasing_by
  simpa [toNat] using pairSnd_lt_succ m

theorem nth_append_singleton_before :
    (xs x q : N) ->
      LtN q (len xs) ->
      nth (append xs (singletonCode x)) q = nth xs q
  | N.zero, x, q, h => by
      have h' : LtN q N.zero := by
        simpa [len, nilCode] using h
      exact False.elim (LtN.not_lt_zero q h')

  | N.succ m, x, q, h => by
      cases q with
      | zero =>
          calc
            nth (append (N.succ m) (singletonCode x)) N.zero
                =
            nth
              (consCode
                (pairFst m)
                (append (pairSnd m) (singletonCode x)))
              N.zero := by
                simp [append]
            _ = pairFst m := by
                rw [nth_zero_consCode]
            _ = nth (N.succ m) N.zero := by
                simp [nth, head0]

      | succ q =>
          have hq : LtN q (len (pairSnd m)) := by
            apply LtN.succ_inj
            simpa [len] using h

          calc
            nth (append (N.succ m) (singletonCode x)) (N.succ q)
                =
            nth
              (consCode
                (pairFst m)
                (append (pairSnd m) (singletonCode x)))
              (N.succ q) := by
                simp [append]
            _ =
            nth (append (pairSnd m) (singletonCode x)) q := by
                rw [nth_succ_consCode]
            _ =
            nth (pairSnd m) q := by
                exact nth_append_singleton_before (pairSnd m) x q hq
            _ =
            nth (N.succ m) (N.succ q) := by
                simp [nth, tail0]
termination_by xs _ q _ => toNat xs
decreasing_by
  simpa [toNat] using pairSnd_lt_succ m

/-! ## Raw quotation of first-class primitive-recursive codes -/

/--
Build a numerical list from a finite family of already-quoted codes.

This version is snoc-style:

    [q₀, ..., qₘ₋₁]

is constructed by first quoting the weakened family of length `m`, then appending
the final entry.  This matches `EvalArgs.snoc`, `FlatArgRefs.snoc`, and
`nodeOutList`.
-/
def quotePrimArgsValues :
    {m : N} -> (Vec.Ix m -> N) -> N
  | N.zero, _ =>
      nilCode

  | N.succ m, qs =>
      append
        (quotePrimArgsValues (fun i => qs (ixWeaken i)))
        (singletonCode (qs (ixLast m)))

@[simp]
theorem len_quotePrimArgsValues :
    {m : N} -> (qs : Vec.Ix m -> N) ->
      len (quotePrimArgsValues qs) = m
  | N.zero, _ => by
      simp [quotePrimArgsValues, nilCode, len]

  | N.succ m, qs => by
      change
        len
          (append
            (quotePrimArgsValues (fun i => qs (ixWeaken i)))
            (singletonCode (qs (ixLast m))))
        =
        N.succ m
      rw [len_append_singleton]
      rw [len_quotePrimArgsValues (fun i => qs (ixWeaken i))]

/--
Quote a first-class `PrimCode k` as the raw numerical syntax code consumed by
`SyntaxEvaluation.U`.

In the `comp` case, the first argument of `codeComp` is the source arity `k`,
not the intermediate arity `m`.
-/
def quotePrimCode : {k : N} -> PrimCode k -> N
  | k, PrimCode.zero _ =>
      codeZero k

  | _, PrimCode.succ =>
      codeSucc

  | k, PrimCode.proj i =>
      codeProj k (ixCode i)

  | k, PrimCode.comp (m := m) f gs =>
      let qf : N :=
        quotePrimCode f
      let qgs : Vec.Ix m -> N :=
        fun i => quotePrimCode (gs i)
      codeComp k qf (quotePrimArgsValues qgs)

  | _, PrimCode.prec g h =>
      let qg : N :=
        quotePrimCode g
      let qh : N :=
        quotePrimCode h
      codeRec qg qh

/--
Quote a finite tuple of argument codes as a numerical list of raw codes.
-/
def quotePrimArgs {k : N} :
    {m : N} -> (Vec.Ix m -> PrimCode k) -> N
  | _, gs =>
      quotePrimArgsValues (fun i => quotePrimCode (gs i))

@[simp]
theorem len_quotePrimArgs {k : N} :
    {m : N} -> (gs : Vec.Ix m -> PrimCode k) ->
      len (quotePrimArgs gs) = m
  | m, gs => by
      unfold quotePrimArgs
      exact
        len_quotePrimArgsValues
          (fun i => quotePrimCode (gs i))

/-! ## Finite search for total minimization bodies -/

/--
A scan up to `n` for a total minimization body has either already found a valid
`muDom` witness, or has verified that all candidates below `n` are nonzero.
-/
inductive TotalMuScan {k : N}
    (g : NumFun (N.succ k))
    (xs : Vec k)
    (n : N) : Type where
  | found
      (d : muDom (totalNum g) xs) :
      TotalMuScan g xs n
  | before
      (b : MuBefore (totalNum g) xs n) :
      TotalMuScan g xs n

/-- The empty prefix condition for total minimization. -/
def totalMuBeforeZero {k : N}
    (g : NumFun (N.succ k))
    (xs : Vec k) :
    MuBefore (totalNum g) xs N.zero := by
  change One
  exact One.star

/-- Extend a total minimization prefix by one checked nonzero value. -/
def totalMuBeforeSucc {k : N}
    (g : NumFun (N.succ k))
    (xs : Vec k)
    {n : N}
    (b : MuBefore (totalNum g) xs n)
    (hnz : IsNonzeroT (g (Vec.cons n xs))) :
    MuBefore (totalNum g) xs (N.succ n) := by
  change
    Sigma
      (fun hn : (totalNum g).Dom (Vec.cons n xs) =>
        Sigma
          (fun _hnz :
            IsNonzeroT ((totalNum g).val (Vec.cons n xs) hn) =>
            MuBefore (totalNum g) xs n))
  refine ⟨One.star, ?_⟩
  refine ⟨?_, b⟩
  change IsNonzeroT (g (Vec.cons n xs))
  exact hnz

/-- A zero value of a total body gives an `IsZeroValue` witness. -/
def totalIsZeroValue {k : N}
    (g : NumFun (N.succ k))
    (xs : Vec k)
    {n : N}
    (hz : IsZeroT (g (Vec.cons n xs))) :
    IsZeroValue (totalNum g) xs n := by
  change
    Sigma
      (fun hn : (totalNum g).Dom (Vec.cons n xs) =>
        IsZeroT ((totalNum g).val (Vec.cons n xs) hn))
  refine ⟨One.star, ?_⟩
  change IsZeroT (g (Vec.cons n xs))
  exact hz

def totalMuScan {k : N}
    (g : NumFun (N.succ k))
    (xs : Vec k) :
    (n : N) -> TotalMuScan g xs n
  | N.zero =>
      TotalMuScan.before (totalMuBeforeZero g xs)

  | N.succ n =>
      match totalMuScan g xs n with
      | TotalMuScan.found d =>
          TotalMuScan.found d

      | TotalMuScan.before b =>
          match hval : g (Vec.cons n xs) with
          | N.zero =>
              TotalMuScan.found
                ⟨n, ⟨b,
                  totalIsZeroValue g xs
                    (n := n)
                    (by
                      change IsZeroT (g (Vec.cons n xs))
                      rw [hval]
                      exact One.star)⟩⟩

          | N.succ a =>
              TotalMuScan.before
                (totalMuBeforeSucc g xs b
                  (by
                    change IsNonzeroT (g (Vec.cons n xs))
                    rw [hval]
                    exact One.star))

/--
For a total search body, a zero value at candidate `n` constructively gives a
valid strict-minimization domain witness. The witness may be an earlier zero
found by the finite scan, which is exactly what `partMu` requires.
-/
def totalMuDomOfZeroAt {k : N}
    (g : NumFun (N.succ k))
    (xs : Vec k)
    (n : N)
    (hz : IsZeroT (g (Vec.cons n xs))) :
    muDom (totalNum g) xs :=
  match totalMuScan g xs n with
  | TotalMuScan.found d =>
      d
  | TotalMuScan.before b =>
      ⟨n, ⟨b, totalIsZeroValue g xs (n := n) hz⟩⟩

/-- Specialized domain constructor for the universal evaluator search body. -/
def leastTraceDomOfCertBadZero
    (tr e xs : N)
    (hz : IsZeroT (certBadFun (Vec.triple tr e xs))) :
    leastTrace.Dom (Vec.pair e xs) :=
  totalMuDomOfZeroAt certBadFun (Vec.pair e xs) tr hz

/-! ## Partial application on natural numbers -/

def unaryInputList (x : N) : N :=
  singletonCode x

def appArgCode : PrimCode N.two :=
  C.singleton proj2_2

def appFirstPart : PartFun N.two :=
  totalNum (PrimCode.eval proj2_1)

def appSecondPart : PartFun N.two :=
  totalNum (PrimCode.eval appArgCode)

def App : PartFun N.two :=
  subst
    U
    (fun
      | Vec.Ix.zero =>
          appFirstPart
      | Vec.Ix.succ Vec.Ix.zero =>
          appSecondPart)

theorem appFirstPart_partComp :
    PartComp appFirstPart :=
  PartComp.totalPrim (PrimCode.sound proj2_1)

theorem appSecondPart_partComp :
    PartComp appSecondPart :=
  PartComp.totalPrim (PrimCode.sound appArgCode)

theorem App_partComp :
    PartComp App :=
  PartComp.subst
    U_partComp
    (fun
      | Vec.Ix.zero =>
          appFirstPart_partComp
      | Vec.Ix.succ Vec.Ix.zero =>
          appSecondPart_partComp)

def AppInput (a b : N) : Vec N.two :=
  Vec.pair a b

/-
Do not let routine type-checking unfold the universal evaluator through `App`.

This is not hiding content or adding an axiom.  `App` remains the same closed
definition.  This only tells the elaborator not to unfold it automatically
during definitional equality / WHNF checks.
-/
attribute [irreducible] App

/--
Domain witness for the concrete application `App a b`.

This is intentionally a structure wrapper, not a transparent alias:

    def AppDom (a b) := App.Dom ...

The transparent alias is what causes Lean to unfold the universal evaluator
during ordinary type comparison.
-/
structure AppDom (a b : N) : Type where
  raw :
    App.Dom (AppInput a b)

/--
Value of the concrete application at a wrapped domain witness.
-/
def AppVal (a b : N) (h : AppDom a b) : N :=
  App.val (AppInput a b) h.raw

/--
The actual application relation for the partial evaluator.

This is intentionally a structure wrapper.  It contains exactly the same data as
the old Sigma presentation:

    Sigma fun h : AppDom a b =>
      EqNT (AppVal a b h) c

but avoids exposing the evaluator during WHNF/isDefEq.
-/
structure AppRel (a b c : N) : Type where
  dom :
    AppDom a b
  val_eq :
    EqNT (AppVal a b dom) c

namespace AppRel

/--
Constructor from a raw `App.Dom` witness.
-/
def mkRaw {a b c : N}
    (h : App.Dom (AppInput a b))
    (hv : EqNT (App.val (AppInput a b) h) c) :
    AppRel a b c :=
  { dom := ⟨h⟩
    val_eq := by
      change EqNT (App.val (AppInput a b) h) c
      exact hv }

/--
Recover the raw domain witness.
-/
def rawDom {a b c : N}
    (h : AppRel a b c) :
    App.Dom (AppInput a b) :=
  h.dom.raw

/--
Recover the raw value equality.
-/
def rawValEq {a b c : N}
    (h : AppRel a b c) :
    EqNT (App.val (AppInput a b) h.dom.raw) c := by
  change EqNT (AppVal a b h.dom) c
  exact h.val_eq

end AppRel

/-! ## Semantic application relation using `EvalRel` -/

/--
Type-valued wrapper around the Prop-valued semantic evaluation relation.

The PCA specifications below use `Sigma` and `×`, so the relation should live
in `Type`, not merely in `Prop`.
-/
structure EvalRelT (e xs y : N) : Type where
  proof : EvalRel e xs y

def SemAppRel (a b c : N) : Type :=
  EvalRelT a (singletonCode b) c

/-! ## Structures for the applicative and combinatory algebra layers -/

structure PartialApplicativeStructureN where
  app : PartFun N.two
  app_partComp : PartComp app

def NatPAS : PartialApplicativeStructureN where
  app := App
  app_partComp := App_partComp

structure SemanticPartialCombinatoryAlgebraN where
  K : N
  S : N
  K_spec :
    ∀ x y : N,
      Sigma fun kx : N =>
        Prod
          (SemAppRel K x kx)
          (SemAppRel kx y x)
  S_spec :
    ∀ x y z xz yz r : N,
      SemAppRel x z xz ->
      SemAppRel y z yz ->
      SemAppRel xz yz r ->
      Sigma fun sx : N =>
      Sigma fun sxy : N =>
        Prod
          (SemAppRel S x sx)
          (Prod
            (SemAppRel sx y sxy)
            (SemAppRel sxy z r))

structure PartialCombinatoryAlgebraN where
  app : PartFun N.two
  app_partComp : PartComp app
  K : N
  S : N
  K_spec :
    ∀ x y : N,
      Sigma fun kx : N =>
        Prod
          (AppRel K x kx)
          (AppRel kx y x)
  S_spec :
    ∀ x y z xz yz r : N,
      AppRel x z xz ->
      AppRel y z yz ->
      AppRel xz yz r ->
      Sigma fun sx : N =>
      Sigma fun sxy : N =>
        Prod
          (AppRel S x sx)
          (Prod
            (AppRel sx y sxy)
            (AppRel sxy z r))

end KleenePCA
end Arithmetic
end SyntheticComputability
