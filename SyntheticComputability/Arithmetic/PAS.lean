import SyntheticComputability.Arithmetic.Parameterization

namespace SyntheticComputability
namespace Arithmetic
namespace PAS

open PrimitiveComputable
open PartialComputable
open Arithmetization
open SyntaxEvaluation
open Parameterization

/-!
# Kleene PCA

This file defines the final partial applicative structure on the bare
natural numbers.

The application operation is:

    a · b  ≃  U(a, [b])

where `[b]` is the singleton numerical list code.

This file is definition-first.  It defines:

* the Kleene application partial map;
* nested application domains and values;
* K/S law specifications;
* the partial applicative structure on `N`;
* a PCA-witness specification to be proved later.

The actual K/S correctness proofs require the adequacy and parameterization
theorems developed in the preceding files.
-/

/-! ## Raw Kleene application -/

/-
  Application input for the universal evaluator.

  The universal evaluator expects a pair:

      (program code, list-coded input)

  so the application a · b is evaluated by feeding U the pair

      (a, [b]).
-/

def appInput (a b : N) : Vec N.two :=
  Vec.pair a (singletonCode b)

/-
  Domain of Kleene application.
-/

def appDom (a b : N) : Type :=
  U.Dom (appInput a b)

/-
  Value of Kleene application.
-/

def appVal (a b : N) (h : appDom a b) : N :=
  U.val (appInput a b) h

/-
  The binary partial application map.

  As a `PartFun N.two`, this has input a two-vector `[a,b]` and returns
  the value of `a · b`, if defined.
-/

def kleeneApp : PartFun N.two where
  Dom := fun input =>
    appDom (firstOfTwo input) (secondOfTwo input)
  val := fun input h =>
    appVal (firstOfTwo input) (secondOfTwo input) h

/-! ## Application relation and nested application -/

/-
  `AppEq a b y` says that `a · b` is defined and equal to `y`.
-/

def AppEq (a b y : N) : Type :=
  Sigma fun h : appDom a b =>
    EqNT (appVal a b h) y

/-
  Domain of `(a · b) · c`.
-/

def app2Dom (a b c : N) : Type :=
  Sigma fun h₀ : appDom a b =>
    appDom (appVal a b h₀) c

/-
  Value of `(a · b) · c`.
-/

def app2Val (a b c : N) (h : app2Dom a b c) : N :=
  appVal (appVal a b h.1) c h.2

/-
  `App2Eq a b c y` says that `(a · b) · c` is defined and equal to `y`.
-/

def App2Eq (a b c y : N) : Type :=
  Sigma fun h : app2Dom a b c =>
    EqNT (app2Val a b c h) y

/-
  Domain of `((a · b) · c) · d`.
-/

def app3Dom (a b c d : N) : Type :=
  Sigma fun h₀ : app2Dom a b c =>
    appDom (app2Val a b c h₀) d

/-
  Value of `((a · b) · c) · d`.
-/

def app3Val (a b c d : N) (h : app3Dom a b c d) : N :=
  appVal (app2Val a b c h.1) d h.2

/-
  `App3Eq a b c d y` says that `((a · b) · c) · d`
  is defined and equal to `y`.
-/

def App3Eq (a b c d y : N) : Type :=
  Sigma fun h : app3Dom a b c d =>
    EqNT (app3Val a b c d h) y

/-! ## K combinator codes and specification -/

/-
  The binary projection code used for the K combinator.

  Semantically:

      KProjectionCode(x,y) = x.
-/

def KProjectionCode : N :=
  codeProj N.two N.zero

/-
  The residual unary code obtained by specializing the first argument of the
  binary projection code.

  Semantically:

      KResidualCode x

  is intended to be the unary constant function

      y ↦ x.
-/

def KResidualCode (x : N) : N :=
  paropWithResidual KProjectionCode N.one (singletonCode x)

/-
  Specification saying that a code `k` computes the map

      x ↦ KResidualCode x.

  This is a code-level precursor to the PCA K-law.
-/

def KElementBuildsResiduals (k : N) : Type :=
  (x : N) ->
    AppEq k x (KResidualCode x)

/-
  PCA K-law for the Kleene application operation.

      k · x · y = x.
-/

def KLaw (k : N) : Type :=
  (x y : N) ->
    App2Eq k x y x

/-! ## S combinator specification -/

/-
  Domain of the right-hand side of the S-law:

      x · z · (y · z)

  More explicitly:

  * `x · z` is defined;
  * `y · z` is defined;
  * `(x · z) · (y · z)` is defined.
-/

def sRhsDom (x y z : N) : Type :=
  Sigma fun hxz : appDom x z =>
    Sigma fun hyz : appDom y z =>
      appDom (appVal x z hxz) (appVal y z hyz)

/-
  Value of the right-hand side of the S-law:

      x · z · (y · z).
-/

def sRhsVal (x y z : N) (h : sRhsDom x y z) : N :=
  appVal
    (appVal x z h.1)
    (appVal y z h.2.1)
    h.2.2

/-
  One direction of the S-law:

  if the right-hand side is defined, then

      s · x · y · z

  is defined with the same value.
-/

def SForwardLaw (s x y z : N) : Type :=
  (hrhs : sRhsDom x y z) ->
    Sigma fun hlhs : app3Dom s x y z =>
      EqNT
        (app3Val s x y z hlhs)
        (sRhsVal x y z hrhs)

/-
  Converse direction of the S-law:

  if

      s · x · y · z

  is defined, then the right-hand side

      x · z · (y · z)

  is defined with the same value.
-/

def SBackwardLaw (s x y z : N) : Type :=
  (hlhs : app3Dom s x y z) ->
    Sigma fun hrhs : sRhsDom x y z =>
      EqNT
        (app3Val s x y z hlhs)
        (sRhsVal x y z hrhs)

/-
  Symmetric S-law.

      s · x · y · z ≃ x · z · (y · z).
-/

def SLaw (s : N) : Type :=
  (x y z : N) ->
    Sigma fun _forward : SForwardLaw s x y z =>
      SBackwardLaw s x y z

/-! ## Partial applicative structure -/

/-
  A partial applicative structure on the natural numbers consists of a binary
  partial operation.
-/

structure PartialApplicativeStructure where
  app : PartFun N.two

/-
  The Kleene partial applicative structure on `N`.

  Its application operation is

      a · b ≃ U(a, [b]).
-/

def KleenePartialApplicativeStructure : PartialApplicativeStructure where
  app := kleeneApp

/-! ## PCA witness specification -/

/-
  A witness specification for the Kleene PCA.

  This packages possible K and S combinators together with their laws.

  The actual construction/proof of inhabitants of this structure should come
  after the arithmetized adequacy, parameter theorem, and evaluator
  determinism results are available.
-/

structure KleenePCAWitnesses where
  k : N
  s : N
  k_law : KLaw k
  s_law : SLaw s

/-
  The proposition/type that the Kleene application structure is combinatorially
  complete in the K/S sense.
-/

def KleenePCARealized : Type :=
  KleenePCAWitnesses

/-! ## Convenient aliases -/

/-
  Infix-style named application domain.
-/

def Applies (a b : N) : Type :=
  appDom a b

/-
  Infix-style named application value.
-/

def Apply (a b : N) (h : Applies a b) : N :=
  appVal a b h

/-
  Definedness and equality for one application.
-/

def AppliesTo (a b y : N) : Type :=
  AppEq a b y

/-
  Definedness and equality for two applications.
-/

def Applies₂To (a b c y : N) : Type :=
  App2Eq a b c y

/-
  Definedness and equality for three applications.
-/

def Applies₃To (a b c d y : N) : Type :=
  App3Eq a b c d y

end PAS
end Arithmetic
end SyntheticComputability
