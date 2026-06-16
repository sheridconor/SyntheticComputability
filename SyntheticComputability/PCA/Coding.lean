/-
PCA/Coding.lean

This file defines the natural-number codes needed for the SK-based PCA.

We need five families of codes:

  K
  S
  K1 x
  S1 x
  S2 x y

The rest of the development should use only these constructors and the
no-confusion / injectivity lemmas proved here.

This file deliberately avoids importing Std or using arithmetic tactics.
-/

import SyntheticComputability.PCA.NNO

namespace PCADev
namespace Code

/-
A very small amount of coding machinery.

We define:

  double 0       = 0
  double (n + 1) = double n + 2

This lets us separate even-shaped and odd-shaped codes without using
division, modulo, or arithmetic automation.
-/
def double : N → N
  | Nat.zero => Nat.zero
  | Nat.succ n => Nat.succ (Nat.succ (double n))

/-- Successor is injective. Local helper to avoid relying on library lemmas. -/
theorem succ_inj {a b : N}
    (h : Nat.succ a = Nat.succ b) :
    a = b := by
  cases h
  rfl

/-- The `double` function is injective. -/
theorem double_inj :
    ∀ {a b : N}, double a = double b → a = b := by
  intro a
  induction a with
  | zero =>
      intro b h
      cases b with
      | zero =>
          rfl
      | succ b =>
          change (0 : N) = Nat.succ (Nat.succ (double b)) at h
          cases h
  | succ a ih =>
      intro b h
      cases b with
      | zero =>
          change Nat.succ (Nat.succ (double a)) = (0 : N) at h
          cases h
      | succ b =>
          change Nat.succ (Nat.succ (double a)) =
            Nat.succ (Nat.succ (double b)) at h
          have h₁ : Nat.succ (double a) = Nat.succ (double b) :=
            succ_inj h
          have h₂ : double a = double b :=
            succ_inj h₁
          exact congrArg Nat.succ (ih h₂)

/-- No doubled number is the successor of a doubled number. -/
theorem double_ne_succ_double :
    ∀ a b : N, double a ≠ Nat.succ (double b) := by
  intro a
  induction a with
  | zero =>
      intro b h
      cases b with
      | zero =>
          change (0 : N) = Nat.succ 0 at h
          cases h
      | succ b =>
          change (0 : N) =
            Nat.succ (Nat.succ (Nat.succ (double b))) at h
          cases h
  | succ a ih =>
      intro b h
      cases b with
      | zero =>
          change Nat.succ (Nat.succ (double a)) = Nat.succ 0 at h
          have h₁ : Nat.succ (double a) = 0 :=
            succ_inj h
          cases h₁
      | succ b =>
          change Nat.succ (Nat.succ (double a)) =
            Nat.succ (Nat.succ (Nat.succ (double b))) at h
          have h₁ :
              Nat.succ (double a) =
                Nat.succ (Nat.succ (double b)) :=
            succ_inj h
          have h₂ :
              double a = Nat.succ (double b) :=
            succ_inj h₁
          exact ih b h₂

/-
A pairing function.

  pair 0       y = double y
  pair (x + 1) y = succ (double (pair x y))

The first coordinate is encoded by iterating the odd/even separation.
This is not efficient, but it is easy to prove injective from scratch.
-/
def pair : N → N → N
  | Nat.zero, y => double y
  | Nat.succ x, y => Nat.succ (double (pair x y))

/-- The pairing function is injective. -/
theorem pair_inj :
    ∀ {x y x' y' : N},
      pair x y = pair x' y' → x = x' ∧ y = y' := by
  intro x
  induction x with
  | zero =>
      intro y x' y' h
      cases x' with
      | zero =>
          constructor
          · rfl
          · exact double_inj h
      | succ x' =>
          change double y =
            Nat.succ (double (pair x' y')) at h
          exact False.elim
            ((double_ne_succ_double y (pair x' y')) h)
  | succ x ih =>
      intro y x' y' h
      cases x' with
      | zero =>
          change Nat.succ (double (pair x y)) =
            double y' at h
          have h' : double y' =
              Nat.succ (double (pair x y)) :=
            h.symm
          exact False.elim
            ((double_ne_succ_double y' (pair x y)) h')
      | succ x' =>
          change Nat.succ (double (pair x y)) =
            Nat.succ (double (pair x' y')) at h
          have h₁ : double (pair x y) =
              double (pair x' y') :=
            succ_inj h
          have h₂ : pair x y = pair x' y' :=
            double_inj h₁
          have h₃ : x = x' ∧ y = y' :=
            ih h₂
          constructor
          · exact congrArg Nat.succ h₃.left
          · exact h₃.right

/-- Tagged payloads. -/
def tag (t payload : N) : N :=
  pair t payload

/-- Injectivity of tagged payloads. -/
theorem tag_inj {t payload t' payload' : N}
    (h : tag t payload = tag t' payload') :
    t = t' ∧ payload = payload' :=
  pair_inj h

/-- Code for the combinator `K`. -/
def K : N :=
  tag 0 0

/-- Code for the combinator `S`. -/
def S : N :=
  tag 1 0

/-- Code for the partially applied combinator `K x`. -/
def K1 (x : N) : N :=
  tag 2 x

/-- Code for the partially applied combinator `S x`. -/
def S1 (x : N) : N :=
  tag 3 x

/-- Code for the twice partially applied combinator `S x y`. -/
def S2 (x y : N) : N :=
  tag 4 (pair x y)

/-
No-confusion lemmas for the five code forms.
-/

theorem K_ne_S :
    K ≠ S := by
  intro h
  have ht : (0 : N) = 1 := (tag_inj h).left
  cases ht

theorem K_ne_K1 (x : N) :
    K ≠ K1 x := by
  intro h
  have ht : (0 : N) = 2 := (tag_inj h).left
  cases ht

theorem K_ne_S1 (x : N) :
    K ≠ S1 x := by
  intro h
  have ht : (0 : N) = 3 := (tag_inj h).left
  cases ht

theorem K_ne_S2 (x y : N) :
    K ≠ S2 x y := by
  intro h
  have ht : (0 : N) = 4 := (tag_inj h).left
  cases ht

theorem S_ne_K1 (x : N) :
    S ≠ K1 x := by
  intro h
  have ht : (1 : N) = 2 := (tag_inj h).left
  cases ht

theorem S_ne_S1 (x : N) :
    S ≠ S1 x := by
  intro h
  have ht : (1 : N) = 3 := (tag_inj h).left
  cases ht

theorem S_ne_S2 (x y : N) :
    S ≠ S2 x y := by
  intro h
  have ht : (1 : N) = 4 := (tag_inj h).left
  cases ht

theorem K1_ne_S1 (x y : N) :
    K1 x ≠ S1 y := by
  intro h
  have ht : (2 : N) = 3 := (tag_inj h).left
  cases ht

theorem K1_ne_S2 (x y z : N) :
    K1 x ≠ S2 y z := by
  intro h
  have ht : (2 : N) = 4 := (tag_inj h).left
  cases ht

theorem S1_ne_S2 (x y z : N) :
    S1 x ≠ S2 y z := by
  intro h
  have ht : (3 : N) = 4 := (tag_inj h).left
  cases ht

/-
Injectivity lemmas for the parameterized code families.
-/

theorem K1_inj {x y : N}
    (h : K1 x = K1 y) :
    x = y :=
  (tag_inj h).right

theorem S1_inj {x y : N}
    (h : S1 x = S1 y) :
    x = y :=
  (tag_inj h).right

theorem S2_inj {x y x' y' : N}
    (h : S2 x y = S2 x' y') :
    x = x' ∧ y = y' := by
  have hp : pair x y = pair x' y' :=
    (tag_inj h).right
  exact pair_inj hp

end Code
end PCADev
