# Lean formalization blueprint

## 1. What is checked, and what remains

`FiniteCore.lean` was checked with Lean 4.32.0, commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`, using only the bundled `Std`
library. The successful compiler output is in `build.log`.

The file proves finite arithmetic and algebra in **host Lean**. It does not
formalize the complete implicit function theorem, construct an object-level
iPRA derivation, or assert that every Lean proof belongs to iPRA.

| Component | Status |
| --- | --- |
| Finite weighted error budget | Checked Lean theorem |
| Closed half-contraction bound after clearing denominators | Checked Lean theorem |
| Boolean finite-trace certificate implies final error bound | Checked Lean theorem |
| Concatenation of finite iterations | Checked Lean theorem |
| Finite vector Neumann residual identity | Checked Lean theorem |
| Rational/vector evaluator implementation | Defined mathematically in the report; to port |
| Complete Cauchy-name construction and its error estimates | Human-readable proof; to port |
| Differentiability and continuity of the derivative | Human-readable proof; to port |
| Full object-iPRA derivation | Not completed; integration plan below |

There are no `sorry` placeholders or user-declared axioms in the checked file.
The compiler's axiom audit reports `propext` and, for the arithmetic proofs,
`Quot.sound`; it does not report `Classical.choice`. These are host Lean
dependencies, not new axioms proposed for iPRA.

## 2. Data representation

Fix positive dimensions `n,m` outside the object theory: the parameter
has dimension `n` and the implicit value has dimension `m`, as in the
manuscript. All matrices have these fixed finite shapes. Use signed
rational arithmetic throughout.

* A natural number is represented directly.
* A signed integer can be represented by a pair of naturals; normalize or use
  cross-difference equality.
* A rational is a signed numerator and a positive natural denominator.
  Comparisons and equality are decided by cross multiplication. Reduction to
  lowest terms is optional. Every denominator created by the algorithms is
  explicitly positive.
* `QVec n := Fin n -> Rat` is a convenient host-Lean interface. Its object
  representation is a coded list of length `n`.
* `QMat n m := Fin n -> Fin m -> Rat` is a convenient host interface. Its
  object representation is a coded rectangular list.
* Vector norm is `max_i abs(v_i)`. Matrix norm is `max_i sum_j abs(A_ij)`.
  All maxima are finite bounded folds. The matrix norm is the induced
  infinity norm, not the maximum entry norm.
* `dyad k := 1 / 2^k`. Exponentiation, finite list coding, bounded maximum,
  bounded sum, and integer division with remainder are primitive recursive.
* A rational box has rational center `b`, positive rational radius `r`, and
  membership predicate `supNorm(y-b) <= r`.
* `clip` replaces each coordinate by `max(b_i-r,min(b_i+r,y_i))`. Prove by
  the finite rational order cases that it maps into the box and is
  nonexpansive in the infinity norm.

A name is a fixed primitive recursive family of rational vectors `a(k)`
with an explicit Cauchy bound. One useful host interface is

```lean
structure RegularName (d : Nat) where
  sample : Nat -> QVec d
  regular : forall k l,
    supNorm (sample k - sample l) <= dyad k + dyad l
```

This is an interface specification, not code in the checked target: vector
subtraction and the norm are the bounded operations just defined. Object
iPRA quantifies over natural numbers and uses the particular PR symbol for
`sample`; it does not quantify over arbitrary functions of type `Nat -> Rat`.

Comparison of named vectors always means a family of finite rational
comparisons with a stated precision shift. Use the manuscript's equality
interface `Eq(a,b) := forall k, supNorm(a(k)-b(k)) <= 2*dyad k`.
Regularity proves that this relation agrees with equality of the represented
values. Transitivity and extensionality are proved by comparing with
arbitrarily finer rational samples and applying the rational squeezing
lemma; transitivity is not an immediate same-precision triangle inequality.
Do not infer equality by deciding whether a real number is zero.

## 3. Fixed evaluator and analytic certificates

The main theorem is stated for a normalized map `H`. To recover an original
equation `F=0`, take `H=AF` with a certified rational preconditioner.
For each instance, fix primitive recursive evaluators for `H`, its full
Jacobian `J=[U V]`, and the precision moduli `mu,nu`. Here `U=DxH`
and `V=DyH`. Their correctness assumptions
are explicit arithmetic statements with universally quantified natural
precision variables. An evaluator at rational arguments and precision `p`
returns a rational vector or matrix with norm error at most `2^-p`.

The interface must include the following data and proofs.

1. Rational centers and rational positive radii. For the original-equation
   corollary, rational square matrices `A,B` with `AB=BA=I` certify the
   passage from `H=AF=0` to `F=0`.
2. Coherence of all evaluator answers and extensionality in the arguments.
3. A joint Taylor remainder modulus for `H`:
   `||H(z+h)-H(z)-DH(z)h|| <= 2^-p ||h||` whenever
   `||h|| <= 2^-mu(p)` and both points are in the chosen domain.
4. A derivative continuity modulus. This can be supplied directly; it is
   not extracted from a bare qualitative assertion of continuous
   differentiability.
5. The local row-norm certificates
   `||I - V|| <= 1/2` and `||U|| <= M`.
6. The base residual and radius inequalities used in the report to prove
   that `T_x(y)=y-H(x,y)` maps the closed `y`-box into itself.

The concrete raw certificates R0--R4 and the safe modulus enlargements
`mu(p)=mu_0(p+1)+1`, `nu(p)=nu_0(p+1)+1` are given in
`paper/sections/06_arithmetic.tex`. Those formulas specify the first-order
input interface; this blueprint does not replace them by qualitative
analytic assumptions.

Universal analytic validity is an assumption to be established for each
particular input, not something decided by a finite test of sampled values.
A numerical verifier can validate a finite trace or an interval certificate;
it cannot certify an arbitrary evaluator's universal correctness by testing
a few points.

The local derivative inequalities imply the needed Lipschitz inequalities
using the report's finite subdivision argument. Each coordinate is a finite
telescoping sum. The Taylor remainder bound controls the sum of local
errors. There is no use of a point selected by the classical mean-value
theorem, compactness without data, or an unbounded stopping search.

## 4. The output algorithm and finite contraction proof

For a rational parameter `x`, precision `k`, and fixed integer `s` with
`2r <= 2^s`, use

* `epsilon(k) = 2^(-(k+4))`,
* `N(k) = k+s+4`,
* `y_0=b`,
* `y_(i+1)=clip(R_(k+5)(y_i-H_hat((x,y_i),k+5)))`,
* `g_k(x)=y_(N(k))`.

Here `R_p` is coordinatewise rounding down to a multiple of `2^-p`,
including for negative coordinates. The evaluator error and rounding error
are each at most `2^(-(k+5))`, so their sum is `epsilon(k)`. Projection is
nonexpansive and fixes the exact image in the box. When `H` is obtained
from `F`, the precision loss from multiplication by `A` has already been
included in the evaluator for `H`. The number of calls is specified before
the run begins. These are precisely the schedule and rounded program in
`paper/sections/03_construction.tex`.

For two finite trajectories aligned at their last `N(k)` steps, let
`d_i` be their distance and let `e=epsilon(k)+epsilon(l)`. The one-step
inequality is

`2 d_(i+1) <= d_i + 2 e`.

Choose the product of the finitely many positive rational denominators as
a common denominator `D`. The quantities `D d_i` and `D e` are
nonnegative integers. `ConstructiveIFT.checked_half_contraction_budget` then
checks the denominator-cleared recurrence. Its closed form is

`2^N d_N + 2e <= d_0 + 2^(N+1)e`.

Dropping the nonnegative term `2e` gives

`d_N <= 2^-N d_0 + 2e`.

The omitted sharper term is not needed for the Cauchy estimates. No real
inequality is decided during this process: every actual checked comparison
is between rationals.

The correspondence to the checked Lean declarations is:

| Mathematical role | Lean declaration |
| --- | --- |
| Finite sum of scaled local errors | `errorBudget` |
| Exact geometric identity | `errorBudget_closed` |
| Trace with `N` specified steps | `half_contraction_budget_finite` |
| PR Boolean prefix checker | `checkSteps` |
| Checker implication / QF invariant | `checked_half_contraction_budget` |
| Iteration-depth schedule | `steps` |
| Alignment of terminal trajectory portions | `iterate_add` |

## 5. The specific iPRA induction obligation

The host theorem with hypothesis `forall i, step(i)` should not be cited as
an object-iPRA theorem merely because it compiled. Instead use the Boolean
version and make the finite trace a natural-number code `t`.

Let `d(t,i)` be a PR projection, `CheckedPrefix(t,N)` the PR Boolean fold
over the first `N` inequalities, and `Budget(t,N)` its explicit integer
budget. The induction invariant is

`CheckedPrefix(t,N)=1 -> 2^N*d(t,N) <= Budget(t,N)`.

After replacing rational arithmetic by signed natural pairs and clearing
positive denominators, this invariant is quantifier-free. Its successor
step is exactly the calculation in `checked_half_contraction_budget`.

For a vector trace, fold the coordinate checks into one Boolean. A bounded
quantifier is notation for that Boolean computation, not a new induction
principle. For trace-generation correctness use a second QF invariant
asserting the evaluator-call transcript, box membership, and prefix budget
checks. Universal evaluator correctness assumptions may be instantiated at
the finitely requested arguments in its successor proof; they need not
appear inside the induction formula.

There must be no induction on an invariant of the form "this sequence is
Cauchy", "this real lies in the box", or "all precisions satisfy the
analytic inequality". Freeze the target precision, carry its finite error
budget, perform QF induction, and universally generalize the precision only
after the derivation is complete.

## 6. Derivative producer and remaining analytic lemmas

Use the notation of `paper/sections/04_derivative.tex`. At a point on the
implicit graph write

`U=DxH`, `V=DyH`, `E=I-V`.

The certificates give `||E||<=1/2` and `||U||<=M`. Define the derivative
name by finite sums approximating

`L = -sum_(j>=0) E^j U`.

`ConstructiveIFT.neumann_residual` proves the finite vector identity

`z_N + E^N v = E z_N + v`.

Apply this to each column, or prove the matrix version by finite coordinate
algebra. It gives the residual needed for `V L=-U`; a separate geometric
tail estimate supplies convergence. The compiled identity alone does not
prove convergence.

The manuscript uses the following explicit allocation. Let `lg(t)` denote
its bounded integer logarithmic shift, and put

`c_D=max(3,lg(8+20M))`, `q=p+c_D`, `N=q`, `j=nu(q+1)`.

Compute `y=g_hat(x,j)` and evaluate `J_hat((x,y),q+1)`. Split the latter
into `U_tilde,V_tilde` and set `E_tilde=I-V_tilde`. The graph
approximation changes the Jacobian by at most `2^(-(q+1))`, and the
Jacobian evaluation contributes the same amount. Thus each coefficient
error is at most `delta=2^-q`. Since `q>=3`, `delta<=1/4` and
`||E_tilde||<=3/4`. Return

`D_hat(x,p)=-sum_(i<q) E_tilde^i U_tilde`.

The finite perturbation identity

`E_tilde^j-E^j = sum_(a+b=j-1) E_tilde^a (E_tilde-E) E^b`

gives, without any limiting argument,

`||sum_(j<N) E_tilde^j U_tilde - sum_(j<N) E^j U|| <= (8M+4)delta`.

Indeed, the finite double geometric sum is at most `2*4=8`, and the
geometric sum for the error in `U` is at most `4`. The tail of the true
series is at most `2M*2^-N`. With `N=q`, the total error is at most
`(4+10M)*2^(-(p+c_D)) <= 2^(-(p+1))`. This is the same fixed-length PR
derivative algorithm and accuracy bound as the manuscript.

The remaining proof modules should proceed in this order.

1. **`RationalBoxes`**: exact arithmetic, max norm, row norm,
   submultiplicativity, clipping, and finite telescoping.
2. **`NamedEvaluators`**: coherence, extensionality, evaluation at a named
   point using a supplied continuity modulus, composition, and rational
   perturbation budgets.
3. **`FiniteMeanValue`**: subdivision proof that the certified derivative
   bounds imply half contraction and parameter Lipschitz continuity.
4. **`InexactContraction`**: compare finite clipped traces using the checked
   recurrence; establish the Cauchy estimate, zero residual, uniqueness,
   and parameter Lipschitz estimate `||g(x)-g(x')||<=2M||x-x'||`.
5. **`FiniteNeumann`**: finite inverse residual, geometric bounds, and the
   derivative producer above.
6. **`ImplicitDerivative`**: Taylor-expand `H(x+h,g(x+h))=H(x,g(x))=0`,
   subtract `V L=-U`, and multiply by the inverse bound `2` to obtain
   the derivative remainder. With `C=max(1,2M)` and `c=lg(C)`, the
   output modulus is `mu_g(p)=mu(p+c+1)+c`. The derivative is asserted
   on the interior of the parameter box; the same Taylor bound holds for
   all increments whose two endpoints remain in that box.
7. **`DerivativeContinuity`**: the finite resolvent identity yields
   `||L-L'|| <= 2||U-U'||+4M||V-V'||`. Compose the derivative input
   modulus with the graph modulus. With `d=lg(2+4M)`, the output modulus
   is `nu_g(p)=nu(p+d)+c`.
8. **`ObjectIPRAAdapter`**: turn each finite arithmetic estimate into a
   `Prf PRAAx` derivation, with trace length an internal numerical term.
   Compile the QF induction invariants described above.

Different harmless precision padding may be chosen when these modules are
implemented. Each change should be checked against the stated output
accuracy; padding must never hide an unbounded search.

## 7. Reusing the ProveIt object-theory layer

The repository inspection in the parent report is pinned to commit
`d36b35eed5bd01af4ade66bf539622495813ccc8` of
`VladimirReshetnikov/ProveIt`. Relevant source modules are:

* `IPRADerivations.Analysis.FeedbackInexact`: denominator-cleared inexact
  iteration budgets and finite Neumann producers.
* `IPRADerivations.Analysis.HalfContractionTail`: internal-index geometric
  contraction reasoning.
* `IPRADerivations.Foundations.ContractionTrace`: coded traces and explicit
  uses of `PRA.qfInd`.
* `IPRADerivations.Analysis.DyadicCauchy`: dyadic Cauchy estimates.
* `IPRADerivations.Analysis.FiniteFTC`: finite calculus estimates.
* `IPRADerivations.Foundations.NeumannCorrection`: finite matrix geometric
  identities.

The distinction between an external index schema and an internal theorem is
essential. `FeedbackInexact.inexact_budget` and
`NeumannCorrection.geometric_left/geometric_right` generate object-theory
proofs separately for each external Lean natural index. That alone is not a
single internal theorem with an arbitrary natural index. The internal trace
and half-contraction modules provide the more appropriate starting point
for the uniform algorithm; inspect their exact hypotheses before reuse.

This package does not vendor, import, or recompile that repository's full
dependency closure. The checked standalone core is independent of it.
Integration should pin the repository commit, import the object syntax and
arithmetic definitions, port the finite certificate lemmas, and then build
the transitive dependency closure. Report successful compilation only after
that build succeeds.

## 8. Completion criteria

The full Lean formalization is complete only when all of the following
artifacts exist and pass the kernel:

* code for the fixed input evaluator interfaces and their arithmetic
  correctness assumptions;
* a PR output evaluator and derivative evaluator with explicit bounds;
* proofs of Cauchy coherence, the implicit equation, local uniqueness,
  Lipschitz continuity, differentiability, and derivative continuity;
* a precise object-language formulation using natural-number variables;
* `Prf PRAAx` terms for that formulation, with every required induction
  shown to be QF and every loop bound an internal term;
* an axiom audit, the pinned dependency versions, and a clean build log.

There is no total primitive recursive universal evaluator for arbitrary
primitive recursive program codes. Keep the theorem as a schema for each
fixed collection of evaluators, or use an explicitly bounded interpreter
whose input includes a computation bound. Neither option permits silently
replacing a fixed evaluator by an unrestricted code interpreter.
