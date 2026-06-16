import SyntheticComputability.KleenePCA

namespace SyntheticComputability
namespace Arithmetic
namespace PCA

open PrimitiveComputable
open PartialComputable
open Arithmetization
open SyntaxEvaluation
open KleenePCA

/-!
# Kleene PCA

This file contains the PCA-facing construction.

It defines the raw program numerals for the combinators `K` and `S`, and
constructs the partial combinatory algebra once the semantic/universal evaluator
correctness package is supplied.

The foundational material — semantic evaluation relations, corrected quotation,
finite index coding, append/list lemmas, total minimization domain construction,
and partial application — lives in `KleenePCA`.
-/

/-! ## Raw expression constructors used by K and S -/

def unaryProjExpr : N :=
  codeProj N.one N.zero

def singletonExpr : N :=
  quotePrimCode singletonCodeCode

def certBadExpr : N :=
  quotePrimCode certBadCode

def leastTraceExpr : N :=
  codeMu certBadExpr

def traceFinalOutExpr : N :=
  quotePrimCode traceFinalOutCode

/--
A raw expression for the universal evaluator:

    UExpr(e, xs) = traceFinalOut(leastTrace(e, xs)).
-/
def UExpr : N :=
  codeComp
    N.two
    traceFinalOutExpr
    (singletonCode leastTraceExpr)

/--
Raw unary composition expression constructor:

    unaryCompExpr h a = code for z ↦ h(a(z)).
-/
def unaryCompExpr (h a : N) : N :=
  codeComp
    N.one
    h
    (singletonCode a)

/--
Raw unary singleton expression constructor:

    unarySingletonExpr a = code for z ↦ [a(z)].
-/
def unarySingletonExpr (a : N) : N :=
  unaryCompExpr singletonExpr a

/--
Raw unary application expression constructor:

    unaryAppExpr f a = code for z ↦ UExpr(f(z), [a(z)]).
-/
def unaryAppExpr (f a : N) : N :=
  codeComp
    N.one
    UExpr
    (twoListCode f (unarySingletonExpr a))

/-! ## Primitive-recursive builders for the raw expression constructors -/

/--
Builder for:

    (h, a) ↦ codeComp 1 h [a].
-/
def unaryCompCode : PrimCode N.two :=
  C.ternary
    codeCompCode
    (constCode (k := N.two) N.one)
    proj2_1
    (C.singleton proj2_2)

/--
Builder for:

    (f, a) ↦ codeComp 1 UExpr [f, codeComp 1 singletonExpr [a]].
-/
def unaryAppCode : PrimCode N.two :=
  let singletonA : PrimCode N.two :=
    C.binary
      unaryCompCode
      (constCode (k := N.two) singletonExpr)
      proj2_2

  let args : PrimCode N.two :=
    C.binary
      twoListCodeCode
      proj2_1
      singletonA

  C.ternary
    codeCompCode
    (constCode (k := N.two) N.one)
    (constCode (k := N.two) UExpr)
    args

/-! ## K combinator -/

/--
The body of K:

    x ↦ codeConst 1 x.
-/
def KBodyCode : PrimCode N.one :=
  C.binary
    codeConstCode
    (constCode (k := N.one) N.one)
    proj1_1

def KComb : N :=
  quotePrimCode KBodyCode

/-! ## S combinator -/

/--
For parameters `(x,y)`, build the unary code

    z ↦ x z.
-/
def xAtZCodeBuilder : PrimCode N.two :=
  C.binary
    unaryCompCode
    proj2_1
    (constCode (k := N.two) unaryProjExpr)

/--
For parameters `(x,y)`, build the unary code

    z ↦ y z.
-/
def yAtZCodeBuilder : PrimCode N.two :=
  C.binary
    unaryCompCode
    proj2_2
    (constCode (k := N.two) unaryProjExpr)

/--
For parameters `(x,y)`, build the unary code

    z ↦ x z (y z).
-/
def SxyBodyCode : PrimCode N.two :=
  C.binary
    unaryAppCode
    xAtZCodeBuilder
    yAtZCodeBuilder

def SxyBodyExpr : N :=
  quotePrimCode SxyBodyCode

/--
For parameter `x`, build the unary code

    y ↦ code for z ↦ x z (y z).
-/
def SxBodyCode : PrimCode N.one :=
  let constX : PrimCode N.one :=
    KBodyCode

  let argList : PrimCode N.one :=
    C.binary
      twoListCodeCode
      constX
      (constCode (k := N.one) unaryProjExpr)

  C.ternary
    codeCompCode
    (constCode (k := N.one) N.one)
    (constCode (k := N.one) SxyBodyExpr)
    argList

def SComb : N :=
  quotePrimCode SxBodyCode

/-! ## Semantic application wrapper -/

abbrev SemAppRelPCA (a b c : N) : Type :=
  SemAppRel a b c

/-! ## Type-level product specifications -/

/--
Semantic K specification, written with `Prod` rather than `×`.

This avoids forcing Lean to infer overloaded product notation over
`Type`-valued relations.
-/
def KSemSpec : Type :=
  ∀ x y : N,
    Sigma fun kx : N =>
      Prod
        (SemAppRelPCA KComb x kx)
        (SemAppRelPCA kx y x)

/--
Semantic S specification, written with explicit nested `Prod`.
-/
def SSemSpec : Type :=
  ∀ x y z xz yz r : N,
    SemAppRelPCA x z xz ->
    SemAppRelPCA y z yz ->
    SemAppRelPCA xz yz r ->
    Sigma fun sx : N =>
    Sigma fun sxy : N =>
      Prod
        (SemAppRelPCA SComb x sx)
        (Prod
          (SemAppRelPCA sx y sxy)
          (SemAppRelPCA sxy z r))

/--
Real K specification for `AppRel`, again written with explicit `Prod`.
-/
def KAppSpec : Type :=
  ∀ x y : N,
    Sigma fun kx : N =>
      Prod
        (AppRel KComb x kx)
        (AppRel kx y x)

/--
Real S specification for `AppRel`, again written with explicit nested `Prod`.
-/
def SAppSpec : Type :=
  ∀ x y z xz yz r : N,
    AppRel x z xz ->
    AppRel y z yz ->
    AppRel xz yz r ->
    Sigma fun sx : N =>
    Sigma fun sxy : N =>
      Prod
        (AppRel SComb x sx)
        (Prod
          (AppRel sx y sxy)
          (AppRel sxy z r))

/-! ## Correctness package required to instantiate the PCA -/

/--
The proof-heavy content required to close the PCA construction.

The package supplies semantic correctness and the bridge between semantic
application and the actual partial application relation.  The final `AppRel`
K/S laws are then constructed below, not assumed as fields.
-/
structure PCACorrectness where

  /-- Semantic application implies real application. -/
  sem_to_app :
    ∀ {a b c : N},
      SemAppRelPCA a b c ->
      AppRel a b c

  /-- Real application implies semantic application. -/
  app_to_sem :
    ∀ {a b c : N},
      AppRel a b c ->
      SemAppRelPCA a b c

  /-- Semantic K law for the concrete numeral `KComb`. -/
  K_sem_spec :
    KSemSpec

  /-- Semantic S law for the concrete numeral `SComb`. -/
  S_sem_spec :
    SSemSpec

namespace PCACorrectness

/-! ## Real K specification -/

/--
The real `AppRel` K law, constructed from the semantic K law and the
semantic-to-real bridge.
-/
def K_app_spec (H : PCACorrectness) : KAppSpec :=
  fun x y =>
    match PCACorrectness.K_sem_spec H x y with
    | Sigma.mk kx hpair =>
        let hkxSem : SemAppRelPCA KComb x kx :=
          Prod.fst hpair

        let hxySem : SemAppRelPCA kx y x :=
          Prod.snd hpair

        let hkxApp : AppRel KComb x kx :=
          @PCACorrectness.sem_to_app H KComb x kx hkxSem

        let hxyApp : AppRel kx y x :=
          @PCACorrectness.sem_to_app H kx y x hxySem

        Sigma.mk kx
          (Prod.mk hkxApp hxyApp)

/-! ## Real S specification -/

/--
The real `AppRel` S law, constructed from the semantic S law, the real-to-semantic
bridge for the hypotheses, and the semantic-to-real bridge for the conclusions.
-/
def S_app_spec (H : PCACorrectness) : SAppSpec :=
  fun x y z xz yz r hx hy hxy =>
    let hxSem : SemAppRelPCA x z xz :=
      @PCACorrectness.app_to_sem H x z xz hx

    let hySem : SemAppRelPCA y z yz :=
      @PCACorrectness.app_to_sem H y z yz hy

    let hxySem : SemAppRelPCA xz yz r :=
      @PCACorrectness.app_to_sem H xz yz r hxy

    match PCACorrectness.S_sem_spec H x y z xz yz r hxSem hySem hxySem with
    | Sigma.mk sx rest =>
        match rest with
        | Sigma.mk sxy htriple =>
            let hSxSem : SemAppRelPCA SComb x sx :=
              Prod.fst htriple

            let htailSem :
                Prod
                  (SemAppRelPCA sx y sxy)
                  (SemAppRelPCA sxy z r) :=
              Prod.snd htriple

            let hSxySem : SemAppRelPCA sx y sxy :=
              Prod.fst htailSem

            let hbodySem : SemAppRelPCA sxy z r :=
              Prod.snd htailSem

            let hSxApp : AppRel SComb x sx :=
              @PCACorrectness.sem_to_app H SComb x sx hSxSem

            let hSxyApp : AppRel sx y sxy :=
              @PCACorrectness.sem_to_app H sx y sxy hSxySem

            let hbodyApp : AppRel sxy z r :=
              @PCACorrectness.sem_to_app H sxy z r hbodySem

            Sigma.mk sx
              (Sigma.mk sxy
                (Prod.mk hSxApp
                  (Prod.mk hSxyApp hbodyApp)))

end PCACorrectness

/-! ## Final partial combinatory algebra -/

/--
The natural-number partial combinatory algebra generated by a closed
`PCACorrectness` package.
-/
def NatPCA (H : PCACorrectness) : PartialCombinatoryAlgebraN where
  app :=
    App
  app_partComp :=
    App_partComp
  K :=
    KComb
  S :=
    SComb
  K_spec :=
    PCACorrectness.K_app_spec H
  S_spec :=
    PCACorrectness.S_app_spec H
