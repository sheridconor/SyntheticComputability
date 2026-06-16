/-
PCA/NNO.lean

This file fixes the natural-number object for the development.

For the first version of the project, we use Lean's built-in `Nat`
as the natural-number object. Later files should import this file and
work with `PCADev.N` rather than mentioning `Nat` everywhere directly.
-/

namespace PCADev

/-- The natural-number object for this development. -/
abbrev N : Type :=
  Nat

namespace N

/-- Zero of the natural-number object. -/
def zero : N :=
  Nat.zero

/-- Successor on the natural-number object. -/
def succ : N → N :=
  Nat.succ

/--
Dependent recursion/induction for the natural-number object.

This is just Lean's primitive recursor for `Nat`, re-exported under the
local name `N.rec` so later files can conceptually treat `N` as the NNO.
-/
def rec {motive : N → Sort u}
    (zero : motive zero)
    (succ : ∀ n : N, motive n → motive (Nat.succ n)) :
    ∀ n : N, motive n :=
  Nat.rec zero succ

/-- Computation rule for `N.rec` at zero. -/
theorem rec_zero {motive : N → Sort u}
    (z : motive zero)
    (s : ∀ n : N, motive n → motive (Nat.succ n)) :
    rec z s zero = z :=
  rfl

/-- Computation rule for `N.rec` at successor. -/
theorem rec_succ {motive : N → Sort u}
    (z : motive zero)
    (s : ∀ n : N, motive n → motive (Nat.succ n))
    (n : N) :
    rec z s (succ n) = s n (rec z s n) :=
  rfl

end N

end PCADev
