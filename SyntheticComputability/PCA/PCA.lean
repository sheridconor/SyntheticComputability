/-
PCA/PCA.lean

This file packages the SK trace/application relation from `PCA.Machine`
as a partial applicative structure, and then proves that it is a PCA.

No external libraries are used.
-/

import SyntheticComputability.PCA.Machine

namespace PCADev

open Code

/--
A partial applicative structure on a type `α`.

The field `app a b c` means that applying `a` to `b` is defined
and has value `c`.
-/
structure PartialApplicative (α : Type u) where
  app : α → α → α → Prop
  functional :
    ∀ {a b c d : α}, app a b c → app a b d → c = d

/--
Definedness for a partial applicative structure.
-/
def Defined {α : Type u} (A : PartialApplicative α) (a b : α) : Prop :=
  ∃ c : α, A.app a b c

/--
A partial combinatory algebra.

The combinators `k` and `s` satisfy the usual relational forms of the
K and S laws.

For `S`, the statement is phrased extensionally:

If

  x z ↦ xz,
  y z ↦ yz,
  xz yz ↦ r,

then

  ((s x) y) z ↦ r.
-/
structure PCA (α : Type u) extends PartialApplicative α where
  k : α
  s : α

  k_spec :
    ∀ x y : α, ∃ kx : α,
      app k x kx ∧
      app kx y x

  s_defined_one :
    ∀ x : α, ∃ sx : α,
      app s x sx

  s_defined_two :
    ∀ x y : α, ∃ sx sxy : α,
      app s x sx ∧
      app sx y sxy

  s_spec :
    ∀ x y z xz yz r : α,
      app x z xz →
      app y z yz →
      app xz yz r →
      ∃ sx sxy : α,
        app s x sx ∧
        app sx y sxy ∧
        app sxy z r

/--
The partial applicative structure on `N` induced by the SK trace relation.
-/
def natPartialApplicative : PartialApplicative N where
  app := App
  functional := App.functional

/--
The `K` combinator law for the coded SK application relation.
-/
theorem nat_k_spec :
    ∀ x y : N, ∃ kx : N,
      App K x kx ∧
      App kx y x := by
  intro x y
  refine ⟨K1 x, ?_, ?_⟩
  · exact ⟨1, Trace.k⟩
  · exact ⟨1, Trace.k1⟩

/--
First definedness law for `S`.
-/
theorem nat_s_defined_one :
    ∀ x : N, ∃ sx : N,
      App S x sx := by
  intro x
  exact ⟨S1 x, ⟨1, Trace.s⟩⟩

/--
Second definedness law for `S`.
-/
theorem nat_s_defined_two :
    ∀ x y : N, ∃ sx sxy : N,
      App S x sx ∧
      App sx y sxy := by
  intro x y
  refine ⟨S1 x, S2 x y, ?_, ?_⟩
  · exact ⟨1, Trace.s⟩
  · exact ⟨1, Trace.s1⟩

/--
The `S` combinator law for the coded SK application relation.
-/
theorem nat_s_spec :
    ∀ x y z xz yz r : N,
      App x z xz →
      App y z yz →
      App xz yz r →
      ∃ sx sxy : N,
        App S x sx ∧
        App sx y sxy ∧
        App sxy z r := by
  intro x y z xz yz r hxz hyz hr
  cases hxz with
  | intro fx hxz_trace =>
      cases hyz with
      | intro fy hyz_trace =>
          cases hr with
          | intro fr hr_trace =>
              refine ⟨S1 x, S2 x y, ?_, ?_, ?_⟩
              · exact ⟨1, Trace.s⟩
              · exact ⟨1, Trace.s1⟩
              · exact ⟨fx + fy + fr + 1,
                  Trace.s2 hxz_trace hyz_trace hr_trace⟩

/--
The natural numbers carry a partial combinatory algebra structure.
-/
def natPCA : PCA N where
  app := App
  functional := App.functional
  k := K
  s := S
  k_spec := nat_k_spec
  s_defined_one := nat_s_defined_one
  s_defined_two := nat_s_defined_two
  s_spec := nat_s_spec

end PCADev
