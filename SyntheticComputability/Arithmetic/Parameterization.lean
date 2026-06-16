import SyntheticComputability.Arithmetic.SyntaxEvaluation

namespace SyntheticComputability
namespace Arithmetic
namespace Parameterization

open PrimitiveComputable
open PartialComputable
open Arithmetization
open SyntaxEvaluation

/-!
# Parameterization

This file contains the syntactic code-building layer needed for the
parameter theorem and, later, for the construction of the Kleene PCA.

It defines:

* numerical conversion of finite indices;
* code lists of constants and projections;
* divergence codes;
* parameterized composition-code builders;
* a first explicit parameterization operation with a known residual arity.

The main parameter theorem is intentionally not proved here.  Later files
should prove that the parameterized code has the expected behavior under the
universal evaluator.
-/

/-! ## Numerical indices -/

/-
  Convert a vector index into its numerical position.

  This is useful when passing from semantic projections indexed by Vec.Ix k
  to syntax projections coded by a numerical index.
-/

def ixToN : {k : N} -> Vec.Ix k -> N
  | N.zero, i =>
      nomatch i
  | N.succ _, Vec.Ix.zero =>
      N.zero
  | N.succ _, Vec.Ix.succ i =>
      N.succ (ixToN i)

/-! ## Short list-code builders -/

/-
  A three-element list code [a,b,c].
-/

def threeListCode (a b c : N) : N :=
  consCode a (consCode b (singletonCode c))

/-
  A four-element list code [a,b,c,d].
-/

def fourListCode (a b c d : N) : N :=
  consCode a (consCode b (consCode c (singletonCode d)))

/-
  Append a singleton to a list-code.
-/

def snocCode (xs x : N) : N :=
  append xs (singletonCode x)

/-! ## Syntax-code list builders -/

/-
  constCodesAux r as m builds the list

    [codeConst r (nth as 0), ..., codeConst r (nth as (m-1))].

  In particular,

    constCodes r as

  builds a list of constant-code functions, one for each entry of as.
-/

def constCodesAux (r as : N) : N -> N
  | N.zero =>
      nilCode
  | N.succ m =>
      snocCode
        (constCodesAux r as m)
        (codeConst r (nth as m))

def constCodes (r as : N) : N :=
  constCodesAux r as (len as)

/-
  projCodesAux r m builds the list

    [codeProj r 0, ..., codeProj r (m-1)].

  In particular,

    projCodes r

  builds the list of all r projection codes of source arity r.
-/

def projCodesAux (r : N) : N -> N
  | N.zero =>
      nilCode
  | N.succ m =>
      snocCode
        (projCodesAux r m)
        (codeProj r m)

def projCodes (r : N) : N :=
  projCodesAux r r

/-
  paramArgCodes r as is the list of argument codes used to specialize a code
  by the parameter list as while leaving r runtime arguments.

  It is:

    constCodes r as ++ projCodes r.

  Semantically, if as = [a_0, ..., a_{m-1}], then this list represents

    constant a_0,
    ...,
    constant a_{m-1},
    projection 0,
    ...,
    projection r-1.

  Therefore composing a code e with this argument list implements:

    xs ↦ e(as ++ xs),

  provided e has arity len(as) + r.
-/

def paramArgCodes (r as : N) : N :=
  append (constCodes r as) (projCodes r)

/-! ## Basic syntax-code combinators -/

/-
  Unary composition code.

    codeComp1 r h g

  represents h(g(-)) at source arity r.
-/

def codeComp1 (r h g : N) : N :=
  codeComp r h (singletonCode g)

/-
  Binary composition code.

    codeComp2 r h g0 g1

  represents h(g0(-), g1(-)) at source arity r.
-/

def codeComp2 (r h g0 g1 : N) : N :=
  codeComp r h (twoListCode g0 g1)

/-
  Ternary composition code.

    codeComp3 r h g0 g1 g2

  represents h(g0(-), g1(-), g2(-)) at source arity r.
-/

def codeComp3 (r h g0 g1 g2 : N) : N :=
  codeComp r h (threeListCode g0 g1 g2)

/-! ## Divergence codes -/

/-
  A syntactic divergence code of arity k.

  It is obtained by minimizing the constantly-one function of arity k+1.
  Since the body never returns zero, the minimization never terminates.
-/

def divCode (k : N) : N :=
  codeMu (codeConst (N.succ k) N.one)

/-! ## Parameterization code builders -/

/-
  residualArity total as is the number of runtime arguments left after
  supplying the parameter list as to a code of arity total.

  This is the truncated subtraction

    total dotminus len(as).

  In later correctness statements, the useful case is when len(as) <= total.
-/

def residualArity (total as : N) : N :=
  N.tsub total (len as)

/-
  paropWithResidual e r as builds the code obtained by feeding the parameter
  list as into e and leaving r runtime arguments.

  It does not try to infer the arity of e.  Instead, the caller supplies the
  intended residual arity r.

  The intended meaning is:

    U(paropWithResidual e r as, xs)
      ≃
    U(e, append as xs)

  when e is well formed of arity len(as) + r.
-/

def paropWithResidual (e r as : N) : N :=
  codeComp r e (paramArgCodes r as)

/-
  paropWithArity e total as computes the residual arity from the supplied
  total arity.

  This is a useful intermediate form before introducing a default arity
  function arity0.
-/

def paropWithArity (e total as : N) : N :=
  paropWithResidual e (residualArity total as) as

/-
  A guarded parameterization operation.

  If the supplied total arity is large enough to absorb the parameter list,
  this should behave like paropWithArity.  Since we are still keeping this file
  definition-first and proof-light, we use the numerical test leqN only to
  select between the intended parameterized code and a divergence code.

  The residual arity is total dotminus len(as), so if len(as) > total, this
  falls back to divergence at arity 0.
-/

def guardedParopWithArity (e total as : N) : N :=
  let r := residualArity total as
  let good := leqN (len as) total
  let goodCode := paropWithResidual e r as
  let badCode := divCode N.zero
  N.add
    (N.mul good goodCode)
    (N.mul (N.tsub N.one good) badCode)

/-! ## Evaluation-facing interfaces -/

/-
  The input list used for unary application later:

    [x]
-/

def unaryInputList (x : N) : N :=
  singletonCode x

/-
  The input list used for binary application later:

    [x,y]
-/

def binaryInputList (x y : N) : N :=
  twoListCode x y

/-
  The input list used for ternary application later:

    [x,y,z]
-/

def ternaryInputList (x y z : N) : N :=
  threeListCode x y z

/-
  Evaluate a code on a raw list-code input.

  This is just a naming alias for the universal evaluator interface from the
  previous file.
-/

def EvalCodeDom (e xs : N) : Type :=
  UDom e xs

def EvalCodeVal (e xs : N) (h : EvalCodeDom e xs) : N :=
  UVal e xs h

/-
  Evaluate a code on a unary input.
-/

def EvalUnaryDom (e x : N) : Type :=
  EvalCodeDom e (unaryInputList x)

def EvalUnaryVal (e x : N) (h : EvalUnaryDom e x) : N :=
  EvalCodeVal e (unaryInputList x) h

/-
  Evaluate a code on a binary input.
-/

def EvalBinaryDom (e x y : N) : Type :=
  EvalCodeDom e (binaryInputList x y)

def EvalBinaryVal (e x y : N) (h : EvalBinaryDom e x y) : N :=
  EvalCodeVal e (binaryInputList x y) h

/-
  Evaluate a code on a ternary input.
-/

def EvalTernaryDom (e x y z : N) : Type :=
  EvalCodeDom e (ternaryInputList x y z)

def EvalTernaryVal (e x y z : N) (h : EvalTernaryDom e x y z) : N :=
  EvalCodeVal e (ternaryInputList x y z) h

/-! ## Statements to be proved later -/

/-
  A one-sided evaluator implication.

  Later, after determinism and correctness of the certificate clauses are
  developed, this kind of relation will be used to state the parameter theorem.

  It says: whenever the left computation is defined, the right computation is
  defined with the same value.
-/

def EvalImplies
    (e₀ xs₀ e₁ xs₁ : N) :
    Type :=
  (h₀ : EvalCodeDom e₀ xs₀) ->
    Sigma fun h₁ : EvalCodeDom e₁ xs₁ =>
      EqNT
        (EvalCodeVal e₀ xs₀ h₀)
        (EvalCodeVal e₁ xs₁ h₁)

/-
  Symmetric evaluator equivalence.

  This is not yet proved for parameterization, but this type is convenient for
  later theorem statements.
-/

def EvalEquiv
    (e₀ xs₀ e₁ xs₁ : N) :
    Type :=
  Sigma
    (fun _forward : EvalImplies e₀ xs₀ e₁ xs₁ =>
      EvalImplies e₁ xs₁ e₀ xs₀)

/-
  The intended statement of the residual-arity parameter theorem.

  This is only a type-level specification for now.

  Later theorem:

    parameterTheoremWithResidual :
      ParameterSpecWithResidual e r as

  under the hypothesis that e is well formed of arity len(as)+r.
-/

def ParameterSpecWithResidual
    (e r as : N) :
    Type :=
  (xs : N) ->
    EvalEquiv
      (paropWithResidual e r as)
      xs
      e
      (append as xs)

/-
  The intended statement of the known-total-arity parameter theorem.

  Later theorem:

    parameterTheoremWithArity :
      SynWf e total ->
      ParameterSpecWithArity e total as

  with side conditions ensuring that len(as) <= total when needed.
-/

def ParameterSpecWithArity
    (e total as : N) :
    Type :=
  ParameterSpecWithResidual e (residualArity total as) as

end Parameterization
end Arithmetic
end SyntheticComputability
