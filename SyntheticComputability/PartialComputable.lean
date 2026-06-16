import SyntheticComputability.PrimitiveComputable

namespace SyntheticComputability
namespace PartialComputable

open PrimitiveComputable

/-
  A one-point type and an empty type.

  These are included here so that the file does not rely on Lean's standard
  Unit or Empty types.
-/

inductive One : Type where
  | star : One

inductive Void : Type

/-
  Type-valued zero and nonzero tests.

  These live in Type, not Prop, so they can appear inside Sigma domains.
-/

def IsZeroT : N -> Type
  | N.zero => One
  | N.succ _ => Void

def IsNonzeroT : N -> Type
  | N.zero => Void
  | N.succ _ => One

/-
  Logical nonzeroness.

  The minimization domain below uses IsNonzeroT because it computes by cases,
  but NotZero is often useful as a logical formulation.
-/

def NotZero (n : N) : Type :=
  n = N.zero -> Void

def isNonzeroT_to_NotZero :
    {n : N} -> IsNonzeroT n -> NotZero n
  | N.zero, h => by
      cases h
  | N.succ n, _ => by
      intro h
      cases h

def notZero_to_IsNonzeroT :
    {n : N} -> NotZero n -> IsNonzeroT n
  | N.zero, h => by
      exact h rfl
  | N.succ n, _ => by
      exact One.star

def isZero_nonzero_absurd :
    {n : N} -> IsZeroT n -> IsNonzeroT n -> Void
  | N.zero, _hz, hnz =>
      nomatch hnz
  | N.succ _n, hz, _hnz =>
      nomatch hz

/-
  Functional partial maps.

  For x : α, the type f.Dom x is the type of evidence that f is defined at x.
  Given h : f.Dom x, the value is f.val x h.

  The field val_ext says that the value is independent of the particular
  domain witness. Thus PFun represents genuine partial functions, not merely
  witness-sensitive realizers.
-/

structure PFun (α β : Type) : Type 1 where
  Dom : α -> Type
  val : (x : α) -> Dom x -> β
  val_ext :
    {x y : α} ->
    x = y ->
    (hx : Dom x) ->
    (hy : Dom y) ->
    val x hx = val y hy

namespace PFun

/-
  Definedness predicate/type.
-/

def defined {α β : Type} (f : PFun α β) (x : α) : Type :=
  f.Dom x

/-
  Total maps as partial maps.

  The domain of definition is everywhere inhabited by One.star.
-/

def total {α β : Type} (f : α -> β) : PFun α β where
  Dom := fun _ => One
  val := fun x _ => f x
  val_ext := by
    intro x y p hx hy
    cases p
    rfl

/-
  Strict composition of partial maps.

  The composite g ∘ f is defined at x exactly when f is defined at x and
  g is defined at the resulting value.
-/

def comp {α β γ : Type}
    (g : PFun β γ)
    (f : PFun α β) :
    PFun α γ where
  Dom := fun x =>
    Sigma fun hf : f.Dom x =>
      g.Dom (f.val x hf)
  val := fun x h =>
    g.val (f.val x h.1) h.2
  val_ext := by
    intro x y p h₁ h₂
    cases h₁ with
    | mk hf₁ hg₁ =>
      cases h₂ with
      | mk hf₂ hg₂ =>
        exact g.val_ext (f.val_ext p hf₁ hf₂) hg₁ hg₂

end PFun

/-
  Numerical partial maps.

  PartFun k represents a partial numerical map

      N^k ⇀ N.

  In the bare development, N^k is represented by Vec k.
-/

abbrev PartFun (k : N) : Type 1 :=
  PFun (Vec k) N

/-
  Embedding total numerical functions into partial numerical functions.
-/

def totalNum {k : N} (f : NumFun k) : PartFun k :=
  PFun.total f

/-
  Strict finite tupling.

  Given a family

      fs : Vec.Ix m -> PartFun k,

  strictTuple fs is the partial map

      Vec k ⇀ Vec m

  defined exactly when every component fs i is defined.
-/

def tupleDom {k : N} :
    {m : N} ->
    (Vec.Ix m -> PartFun k) ->
    Vec k ->
    Type
  | N.zero, _, _ =>
      One
  | N.succ m, fs, x =>
      Sigma fun _ : (fs Vec.Ix.zero).Dom x =>
        tupleDom
          (m := m)
          (fun i => fs (Vec.Ix.succ i))
          x

def tupleVal {k : N} :
    {m : N} ->
    (fs : Vec.Ix m -> PartFun k) ->
    (x : Vec k) ->
    tupleDom (m := m) fs x ->
    Vec m
  | N.zero, _, _, _ =>
      Vec.nil
  | N.succ m, fs, x, h =>
      Vec.cons
        ((fs Vec.Ix.zero).val x h.1)
        (tupleVal
          (m := m)
          (fun i => fs (Vec.Ix.succ i))
          x
          h.2)

theorem tupleVal_ext {k : N} :
    {m : N} ->
    (fs : Vec.Ix m -> PartFun k) ->
    (x : Vec k) ->
    (h₁ h₂ : tupleDom (m := m) fs x) ->
    tupleVal (m := m) fs x h₁ =
    tupleVal (m := m) fs x h₂
  | N.zero, fs, x, h₁, h₂ => by
      cases h₁
      cases h₂
      rfl
  | N.succ m, fs, x, h₁, h₂ => by
      cases h₁ with
      | mk hf₁ ht₁ =>
        cases h₂ with
        | mk hf₂ ht₂ =>
          exact
            Eq.trans
              (congrArg
                (fun a => Vec.cons (k := m) a
                  (tupleVal
                    (m := m)
                    (fun i => fs (Vec.Ix.succ i))
                    x
                    ht₁))
                ((fs Vec.Ix.zero).val_ext rfl hf₁ hf₂))
              (congrArg
                (fun t => Vec.cons (k := m)
                  ((fs Vec.Ix.zero).val x hf₂)
                  t)
                (tupleVal_ext
                  (m := m)
                  (fun i => fs (Vec.Ix.succ i))
                  x
                  ht₁
                  ht₂))

def strictTuple {k m : N}
    (fs : Vec.Ix m -> PartFun k) :
    PFun (Vec k) (Vec m) where
  Dom := fun x =>
    tupleDom (m := m) fs x
  val := fun x h =>
    tupleVal (m := m) fs x h
  val_ext := by
    intro x y p h₁ h₂
    cases p
    exact tupleVal_ext (m := m) fs x h₁ h₂

/-
  Strict simultaneous substitution.

  Given

      h  : N^m ⇀ N
      gs : m many maps N^k ⇀ N,

  the composite h(g_1, ..., g_m) is defined exactly when all g_i are
  defined and h is defined at the resulting vector of values.
-/

def subst {k m : N}
    (h : PartFun m)
    (gs : Vec.Ix m -> PartFun k) :
    PartFun k :=
  PFun.comp h (strictTuple gs)

/-
  Strict primitive recursion for partial numerical maps.

  Rather than defining recDom and recVal mutually, we define a computation
  trace carrying both the input stage and the resulting value.

  RecTrace g h xs n a means:

      the strict recursive computation at stage n with parameters xs
      is defined and has value a.
-/

inductive RecTrace {k : N}
    (g : PartFun k)
    (h : PartFun (N.succ (N.succ k)))
    (xs : Vec k) :
    N -> N -> Type where

  | zero
      (hg : g.Dom xs) :
      RecTrace g h xs N.zero (g.val xs hg)

  | succ
      {n a : N}
      (prev : RecTrace g h xs n a)
      (hh : h.Dom (Vec.cons n (Vec.cons a xs))) :
      RecTrace g h xs
        (N.succ n)
        (h.val (Vec.cons n (Vec.cons a xs)) hh)

namespace RecTrace

theorem value_unique {k : N}
    {g : PartFun k}
    {h : PartFun (N.succ (N.succ k))}
    {xs : Vec k} :
    {n a b : N} ->
    RecTrace g h xs n a ->
    RecTrace g h xs n b ->
    a = b
  | N.zero, _a, _b, ta, tb => by
      cases ta with
      | zero hg =>
        cases tb with
        | zero hg' =>
          exact g.val_ext rfl hg hg'

  | N.succ n, _a, _b, ta, tb => by
      cases ta with
      | succ prev hh =>
        cases tb with
        | succ prev' hh' =>
          have hp := value_unique prev prev'
          exact
            h.val_ext
              (by
                cases hp
                rfl)
              hh
              hh'

end RecTrace

/-
  The domain of the recursive computation at stage n is the type of pairs
  consisting of a value a and a trace showing that the computation returns a.
-/

def recDom {k : N}
    (g : PartFun k)
    (h : PartFun (N.succ (N.succ k)))
    (xs : Vec k)
    (n : N) :
    Type :=
  Sigma fun a : N =>
    RecTrace g h xs n a

/-
  The value extracted from a recursive computation witness.
-/

def recVal {k : N}
    (g : PartFun k)
    (h : PartFun (N.succ (N.succ k)))
    (xs : Vec k)
    (n : N)
    (d : recDom g h xs n) :
    N :=
  d.1

def partPrec {k : N}
    (g : PartFun k)
    (h : PartFun (N.succ (N.succ k))) :
    PartFun (N.succ k) where
  Dom := fun xs =>
    recDom g h (Vec.tail xs) (Vec.head xs)
  val := fun xs hxs =>
    recVal g h (Vec.tail xs) (Vec.head xs) hxs
  val_ext := by
    intro xs ys p d₁ d₂
    cases p
    exact RecTrace.value_unique d₁.2 d₂.2

def partPrec_trace {k : N}
    (g : PartFun k)
    (h : PartFun (N.succ (N.succ k)))
    {xs : Vec k}
    {n : N}
    (d : (partPrec g h).Dom (Vec.cons n xs)) :
    RecTrace g h xs n ((partPrec g h).val (Vec.cons n xs) d) := by
  exact d.2

/-
  A minimal internal strict-order predicate for minimization.

  Before m n means m is one of the earlier stages checked before n.
  This is the order relation naturally matched to MuBefore.
-/

inductive Before : N -> N -> Type where
  | here {n : N} :
      Before n (N.succ n)
  | earlier {m n : N} :
      Before m n -> Before m (N.succ n)

namespace Before

def zero_succ : (n : N) -> Before N.zero (N.succ n)
  | N.zero =>
      Before.here
  | N.succ n =>
      Before.earlier (zero_succ n)

def succ_succ :
    {m n : N} -> Before m n -> Before (N.succ m) (N.succ n)
  | _, _, Before.here =>
      Before.here
  | _, _, Before.earlier h =>
      Before.earlier (succ_succ h)

end Before

/-
  Trichotomy for the minimal internal order.
-/

inductive NCompare (m n : N) : Type where
  | eq : m = n -> NCompare m n
  | lt : Before m n -> NCompare m n
  | gt : Before n m -> NCompare m n

def compareN : (m n : N) -> NCompare m n
  | N.zero, N.zero =>
      NCompare.eq rfl
  | N.zero, N.succ n =>
      NCompare.lt (Before.zero_succ n)
  | N.succ m, N.zero =>
      NCompare.gt (Before.zero_succ m)
  | N.succ m, N.succ n =>
      match compareN m n with
      | NCompare.eq h =>
          by
            cases h
            exact NCompare.eq rfl
      | NCompare.lt h =>
          NCompare.lt (Before.succ_succ h)
      | NCompare.gt h =>
          NCompare.gt (Before.succ_succ h)

/-
  Strict unbounded minimization.

  Given

      g : N^(1+k) ⇀ N,

  partMu g : N^k ⇀ N returns the least n such that

      g(n, xs) is defined and equals 0,

  provided all earlier values g(m, xs), m < n, are defined and nonzero.

  The "all earlier values" condition is encoded recursively by MuBefore.
-/

def MuBefore {k : N}
    (g : PartFun (N.succ k))
    (xs : Vec k) :
    N -> Type
  | N.zero =>
      One
  | N.succ n =>
      Sigma fun hn : g.Dom (Vec.cons n xs) =>
        Sigma fun _hnz : IsNonzeroT (g.val (Vec.cons n xs) hn) =>
          MuBefore g xs n

def IsZeroValue {k : N}
    (g : PartFun (N.succ k))
    (xs : Vec k)
    (n : N) :
    Type :=
  Sigma fun hn : g.Dom (Vec.cons n xs) =>
    IsZeroT (g.val (Vec.cons n xs) hn)

def muDom {k : N}
    (g : PartFun (N.succ k))
    (xs : Vec k) :
    Type :=
  Sigma fun n : N =>
    Sigma fun _before : MuBefore g xs n =>
      IsZeroValue g xs n

def muBefore_lookup {k : N}
    {g : PartFun (N.succ k)}
    {xs : Vec k} :
    {m n : N} ->
    Before m n ->
    MuBefore g xs n ->
    Sigma fun hm : g.Dom (Vec.cons m xs) =>
      IsNonzeroT (g.val (Vec.cons m xs) hm)
  | _, _, Before.here, hb =>
      Sigma.mk hb.1 hb.2.1
  | _, _, Before.earlier h, hb =>
      muBefore_lookup h hb.2.2

def isZero_nonzero_absurd_eq :
    {a b : N} ->
    a = b ->
    IsZeroT a ->
    IsNonzeroT b ->
    Void
  | N.zero, N.zero, _p, _hz, hnz =>
      nomatch hnz
  | N.zero, N.succ _b, p, _hz, _hnz =>
      nomatch p
  | N.succ _a, N.zero, p, _hz, _hnz =>
      nomatch p
  | N.succ _a, N.succ _b, _p, hz, _hnz =>
      nomatch hz

def zeroValue_nonzero_absurd {k : N}
    {g : PartFun (N.succ k)}
    {xs : Vec k}
    {n : N}
    (hz : IsZeroValue g xs n)
    (hnz :
      Sigma fun hn : g.Dom (Vec.cons n xs) =>
        IsNonzeroT (g.val (Vec.cons n xs) hn)) :
    Void := by
  cases hz with
  | mk hzdom hzval =>
    cases hnz with
    | mk hnzdom hnzval =>
      exact
        isZero_nonzero_absurd_eq
          (g.val_ext rfl hzdom hnzdom)
          hzval
          hnzval

theorem mu_unique {k : N}
    {g : PartFun (N.succ k)}
    {xs : Vec k}
    (d₁ d₂ : muDom g xs) :
    d₁.1 = d₂.1 := by
  cases d₁ with
  | mk n rest₁ =>
    cases rest₁ with
    | mk before₁ zero₁ =>
      cases d₂ with
      | mk m rest₂ =>
        cases rest₂ with
        | mk before₂ zero₂ =>
          cases compareN n m with
          | eq h =>
              exact h
          | lt hlt =>
              cases zeroValue_nonzero_absurd
                zero₁
                (muBefore_lookup hlt before₂)
          | gt hgt =>
              cases zeroValue_nonzero_absurd
                zero₂
                (muBefore_lookup hgt before₁)

def partMu {k : N}
    (g : PartFun (N.succ k)) :
    PartFun k where
  Dom := fun xs =>
    muDom g xs
  val := fun _ h =>
    h.1
  val_ext := by
    intro xs ys p d₁ d₂
    cases p
    exact mu_unique d₁ d₂

def partMu_before {k : N}
    {g : PartFun (N.succ k)}
    {xs : Vec k}
    (d : (partMu g).Dom xs) :
    MuBefore g xs ((partMu g).val xs d) := by
  exact d.2.1

def partMu_zero_value {k : N}
    {g : PartFun (N.succ k)}
    {xs : Vec k}
    (d : (partMu g).Dom xs) :
    IsZeroValue g xs ((partMu g).val xs d) := by
  exact d.2.2

def partMu_checked_nonzero {k : N}
    {g : PartFun (N.succ k)}
    {xs : Vec k}
    {m : N}
    (d : (partMu g).Dom xs)
    (hm : Before m ((partMu g).val xs d)) :
    Sigma fun hd : g.Dom (Vec.cons m xs) =>
      IsNonzeroT (g.val (Vec.cons m xs) hd) := by
  exact muBefore_lookup hm (partMu_before d)

/-
  Partial-computable numerical maps.

  This is the structural closure class corresponding to the manuscript's
  partial recursive numerical maps, expressed directly on unary-output
  numerical partial maps.
-/

inductive PartComp : {k : N} -> PartFun k -> Prop where

  /-
    Every primitive-computable total numerical map is partial computable.
  -/
  | totalPrim {k : N}
      {f : NumFun k}
      (hf : Prim f) :
      PartComp (totalNum f)

  /-
    Closure under strict simultaneous substitution.
  -/
  | subst {k m : N}
      {h : PartFun m}
      {gs : Vec.Ix m -> PartFun k}
      (hh : PartComp h)
      (hgs : (i : Vec.Ix m) -> PartComp (gs i)) :
      PartComp (subst h gs)

  /-
    Closure under strict primitive recursion.
  -/
  | prec {k : N}
      {g : PartFun k}
      {h : PartFun (N.succ (N.succ k))}
      (hg : PartComp g)
      (hh : PartComp h) :
      PartComp (partPrec g h)

  /-
    Closure under strict unbounded minimization.
  -/
  | mu {k : N}
      {g : PartFun (N.succ k)}
      (hg : PartComp g) :
      PartComp (partMu g)

/-
  Convenience constructors for the total initial maps inherited from the
  primitive-computable structure.
-/

def partComp_total {k : N}
    {f : NumFun k}
    (hf : Prim f) :
    PartComp (totalNum f) :=
  PartComp.totalPrim hf

def partComp_zero (k : N) :
    PartComp (totalNum (zeroFun k)) :=
  PartComp.totalPrim (Prim.zero k)

def partComp_succ :
    PartComp (totalNum succFun) :=
  PartComp.totalPrim Prim.succ

def partComp_proj {k : N}
    (i : Vec.Ix k) :
    PartComp (totalNum (projFun i)) :=
  PartComp.totalPrim (Prim.proj i)

/-
  Optional notation-level aliases.

  These keep the later files closer to the prose:
    total numerical map -> partial numerical map,
    strict substitution,
    strict primitive recursion,
    strict minimization.
-/

def J {k : N} (f : NumFun k) : PartFun k :=
  totalNum f

def strictSubst {k m : N}
    (h : PartFun m)
    (gs : Vec.Ix m -> PartFun k) :
    PartFun k :=
  subst h gs

def strictPrec {k : N}
    (g : PartFun k)
    (h : PartFun (N.succ (N.succ k))) :
    PartFun (N.succ k) :=
  partPrec g h

def strictMu {k : N}
    (g : PartFun (N.succ k)) :
    PartFun k :=
  partMu g

end PartialComputable
end SyntheticComputability
