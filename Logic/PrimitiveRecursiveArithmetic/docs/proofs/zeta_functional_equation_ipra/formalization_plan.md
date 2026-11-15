# Foundations audit and a concrete Lean plan

## Scope and checked source provenance

The source snapshot consulted through the GitHub connector is ProveIt commit
`c5093c20b5bffb0333fd42915b7bc858d5aa45cc` (main when inspected). The root
`lean-toolchain` says `leanprover/lean4:v4.32.0`; `lakefile.toml` requests
mathlib `v4.32.0`. The relevant package has namespace
`LeanProofs.ConciseIPRA` and is a root-workspace Lake library whose sources
are under `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA`.

The exact sources inspected are:

- `PR.lean`: `PR`, `PTm`, `PRAAx`, and `PRA.qfInd`.
- `BiInterpretation.lean`: the equivalence between the ordinary iterator
  presentation and iPRA, notably `biInterp`, `teq_iff_pra`, `pra_iff_teq`.
- `NativeBiInterpretation.lean`: `NFm.toPRA`, `NFm.ofPRA`,
  `native_iff_pra`, `pra_iff_native`, and both formula round trips.
- The package `README.md`, especially its "Lean formalization" section.

The current `docs/drafts` directory contains archives for FTA, Basel,
isoperimetry, Minkowski, PNT, Stirling, transcendence, and triangle formulas.
Listing those filenames gives no entitlement to treat their mathematics as
proved. None is required as an axiom or black-box analytic theorem here.

The README reports that its modules build without `sorry`, with no added
axioms or `native_decide`. That is the repository's reported build status;
this environment has no Lean executable, so it was not independently
reproduced. The stated axiom dependencies of its main native bridge include
`Classical.choice`; the ordinary `T_eq`–iPRA equivalence uses `propext` and
`Quot.sound`. These are metatheoretic Lean dependencies. They do not make
excluded middle an inference rule of the deeply embedded object theory.

Pinned source URLs can be formed as
`https://github.com/VladimirReshetnikov/ProveIt/blob/c5093c20b5bffb0333fd42915b7bc858d5aa45cc/`
followed by the corresponding repository path.

## What “in iPRA” must mean

The repository's theory is intuitionistic first-order arithmetic with a
function symbol for each primitive-recursive definition, its defining
equations, successor separation and injectivity, and **quantifier-free
induction only**. It is not arithmetic with unrestricted induction, and it
does not contain a sort of arbitrary real or complex numbers.

The natural primary theorem is a uniform arithmetic statement over natural
codes for rational complex points, a box bound, and an output precision.
The expressions for theta, the regularized Mellin integral, reciprocal
gamma, and zeta are specified by fixed primitive-recursive approximation
algorithms. Their equality means the corresponding finite rational
residual is at most a prescribed dyadic error, at every requested
precision. Thus the object theorem is a universally closed equation
`check(point, bound, precision) = 1` for one fixed PR definition `check`.

A rational complex number is encoded by two signed rational components.
Malformed codes are decoded to a fixed default. Tests for code validity,
membership in a rational box, and inequalities between rational outputs
are primitive recursive. A checker returning 1 for malformed or out-of-box
inputs represents the desired implication without a partial function.
All denominators in rational codes are positive; signed arithmetic may be
encoded by pairs of naturals, avoiding any ambient integer axiom.

One can then specialize to a fixed PR Cauchy name
`a : N -> Q(i)`, with a supplied regularity hypothesis such as

`||a(p)-a(q)||_1 <= 2^(-p) + 2^(-q)`.

For every fixed PR definition of `a`, the same finite proof gives an iPRA
instance with `a` as a definitional symbol. The input-reading index is
explicit. On the enlarged box `A=B+3`, fix the expression's uniform
approximation accuracy to `k+4`, determine all cutoffs from that box and
precision, and suppress optional rounding. The finite evaluator is a
rational complex polynomial `P(s)=sum_j a_j s^j`. Compute

`K = 1 + ceil(sum_(j>=1) j*norm1(a_j)*(2A+2)^(j-1))`

by a PR coefficient fold, and take `m=k+lambda(K)+8`, where `lambda` is
the ceiling binary logarithm implemented by bounded search. The finite
difference-of-powers identity bounds the input sensitivity by `K`; the
regularity and uniform approximation bounds supply the required output
accuracy. The theorem does not quantify internally over all PR functions
and does not evaluate arbitrary program codes.

There is **no primitive-recursive universal evaluator for all PR codes**.
Using one would be a genuine error, not a cosmetic encoding choice. A
family of externally compiled definitions is appropriate. Alternatively,
the primary uniform rational-input theorem already expresses the analytic
content needed for every such specialization.

Nor is an arbitrary Cauchy name automatically admissible. Existence of a
computable real need not supply a primitive-recursive modulus, and
classically computable convergence must not be substituted for the
explicit convergence bounds in the proof.

## Avoiding an illicit induction principle

The formula asserting that two names are equal at all precisions is not
quantifier free. The formula asserting that a name is Cauchy is not
quantifier free. Therefore it is not legitimate to apply `PRA.qfInd` to
either formula.

The allowed procedure is:

1. Fix all numerical parameters, including the final requested precision.
2. Choose explicit finite truncation and mesh bounds by PR arithmetic.
3. Express the invariant for the current finite sum, product, or mesh as a
   rational inequality. Any bounded universal assertion over mesh indices
   is represented by a primitive-recursive Boolean conjunction.
4. Use quantifier-free induction on that finite-stage invariant.
5. Discharge the numerical parameters by universal introduction only
   after completing the finite estimate.

For example, `forall j <= n, |error_j| <= E_j` is represented by a PR fold
of the characteristic function of the rational inequality, set equal to
1. This is a quantifier-free equation. The bounded length of the fold is a
number parameter, not a hidden use of unbounded search.

The mere fact that an approximation algorithm is PR does **not** prove its
correctness in iPRA. The finite estimates and their qf induction invariants
must be proved. Conversely, a classical Lean theorem about a PR algorithm
does not automatically produce an object-language iPRA derivation.

## Pole-free arithmetic targets

Let `E(s)` denote the entire reciprocal gamma function, and let

`xi(s) = 1/2 + s(s-1)/2 * (J(s) + J(1-s))`,

where `J(s)` is the upper-half theta Mellin integral with the convention
`psi(t)=sum_(n>=1) exp(-pi*n*n*t)`.

The symmetry `xi(s)=xi(1-s)` is a polynomial identity once the same
algorithm `J` is used on the two arguments. The substantive analytic work
is to identify this function with
`s(s-1)/2 * pi^(-s/2) Gamma(s/2) zeta(s)` in the half-plane of absolute
convergence, using the proved theta transformation, and then define its
regularized continuation directly. No uniqueness-of-analytic-continuation
principle is needed for the construction.

Define the entire numerator

`Z(s) = pi^(s/2) E(1+s/2) xi(s)`.

Then `zeta(s)=Z(s)/(s-1)` whenever an explicit apartness witness from `1`
is available. This formula uses the reciprocal-gamma recurrence to remove
the apparent division by `s`, so it defines `zeta(0)` directly and does not
require deciding whether `s=0`.

The familiar sine–gamma equation has the following denominator-cleared
entire form:

`s E(1-s) Z(s) = (1-s) 2^s pi^(s-1) sin(pi*s/2) Z(1-s)`.

This is the preferred uniform finite-precision arithmetic target. The
ordinary meromorphic functional equation follows by division on regions
with the required explicit lower bounds. No test “is this real zero?” or
“is this point a nonpositive integer?” is performed.

The gamma identity needed for this target is also entire:

`E(1-s) E(s/2) = 2^s pi^(-1/2) sin(pi*s/2) E((1-s)/2)`.

It follows by substituting `z=(1-s)/2` into reciprocal-gamma duplication,
and using `E(s/2)E(1-s/2)=sin(pi*s/2)/pi`. Together with the reciprocal-gamma
recurrence and the symmetry of `xi`, it proves the cleared equation
without any division by potentially zero factors.

## Lean module plan and acceptance gates

### 1. `ZetaIPRA.Coding`

Construct fixed PR symbols for signed integers, rational arithmetic,
complex pairs, dyadic precision, finite lists, and bounded products/sums.
Prove their defining equations in `Prf PRAAx`. Provide an ordinary Lean
semantic interpretation as a separate theorem for each symbol. Rational
order predicates should reduce to natural cross-product inequalities, and
the characteristic functions must be shown correct.

Acceptance gate: each primitive operation has both a PR definition and an
object-theory derivation of the finite algebra used later. A semantic
implementation in Lean `Rat` alone does not satisfy this gate.

### 2. `ZetaIPRA.Elementary`

Implement the fixed rational Taylor/log/reciprocal/square-root algorithms
used in the paper. Compile the explicit truncation and error estimates.
Composition must carry a numerical bound for each intermediate value, so
the requested input precision is an explicit PR expression.

For the final cleared equation, the schedule is fixed: `A=B+3`,
`w=k+512A^2+20`, and `v=w+16A+30` for the remaining elementary powers and
sine. Compute pi, log 2, and log of the rational pi approximation to
precision `v`, clipping the latter's input to `[3,4]`. Form exponents
exactly and evaluate their exponentials to precision `w+4`, using the
uniform exponent bound `4A+1`; compute sine from the two exponentials.
For an exponential argument with `norm1<=S`, `S>=1`, the report's
Taylor degree is `4S+u+4` for requested precision `u`. These are fixed
PR schedules, not searches for convergence. The full J and reciprocal
gamma schedules are in `finite_contract.md`.

Acceptance gate: the exp/log/trigonometric estimates are theorems of the
form `Prf PRAAx [] finiteEstimateSentence`. Complex equality is reduced to
two rational coordinate inequalities, or a rational `l1` bound.

### 3. `ZetaIPRA.Quadrature`

Formalize the finite telescoping estimates behind integration, integration
by parts, and the substitutions actually used. A uniform left-rectangle
sum has error at most `L*(b-a)^2/M` for a Lipschitz bound `L`; the necessary
Lipschitz facts should themselves be proved by Taylor-remainder bounds.
Do not import a general compactness theorem or appeal to the existence of
an unspecified maximum. Every derivative bound is supplied numerically.

Acceptance gate: convergence notation is eliminable by a stated finite
error lemma. General measure theory or arbitrary Cauchy completeness is
not part of the object theory.

### 4. `ZetaIPRA.GaussianTheta`

Compile the finite Gaussian normalization, Fourier-transform estimate,
periodization tails, and finite Fejer recovery estimates. Keep all
interchanges of sums and integrals finite before applying the explicit
tail bounds.

Acceptance gate: the theta transformation has an all-precision arithmetic
proof with all finite cutoffs explicitly computed from the box and
precision. The proof does not merely invoke mathlib's Poisson summation.

### 5. `ZetaIPRA.ReciprocalGamma`

Compile the finite Euler products, their uniform tails, the recurrence,
reflection, duplication, and identification with the positive-half-plane
Euler integral. Use entire reciprocal identities to avoid poles. For any
nonvanishing assertion used to divide, construct a rational lower bound.

Acceptance gate: all identities are proven as finite residual estimates;
no analytic identity theorem or unbounded search for a nonzero witness.

### 6. `ZetaIPRA.Mellin`

Define the upper-half integral `J`, with explicit cutoffs for the theta
series, the `t`-integral, and its mesh. Compile the uniform majorants for
`J`, including parameter derivatives if needed to transport rational-input
theorems to named inputs. Prove the Dirichlet-series identification for
`Re(s)>=1+delta`, where `delta>0` is a rational input and tail cutoffs depend
PR on its numerator and denominator.

Acceptance gate: the arithmetic statement identifies the constructed
continuation with the usual zeta series where the latter converges.
Defining a symmetric function alone is not sufficient.

### 7. `ZetaIPRA.FunctionalEquation`

Assemble the finite residual theorem, universally generalize its natural
parameters, and obtain a term of

`Prf PRAAx [] (residualSentence compiledCheck)`.

Apply `pra_iff_native` to transfer this exact sentence into the existing
native scalar calculus. `ArithmeticBridge.lean` records this interface.
`AlgebraicCore.lean` records only the easy polynomial symmetry.

For specialization to named inputs, implement the polynomial-coefficient
bound and input index specified above. The evaluator's cutoffs must use
the common box bounds, and its polynomial form must be retained using
exact rational sums and products with no final rounding.

Acceptance gate: the definition `compiledCheck` and its actual object
derivation are present, with no `sorry`, no placeholder axiom, and no
imported semantic zeta theorem substituted for them. Inspect the axiom
dependencies, build each module, and include the build log. The two draft
interface files supplied here do not pass this final gate by themselves.

## Optional ambient semantic cross-check

Mathlib `v4.32.0`, file
`Mathlib/NumberTheory/LSeries/RiemannZeta.lean`, has the following relevant
theorems (the source was directly retrieved):

- `completedRiemannZeta₀_one_sub (s : C)`;
- `completedRiemannZeta_one_sub (s : C)`;
- `riemannZeta_one_sub`, under `forall n : N, s != -n` and `s != 1`;
- `zeta_eq_tsum_one_div_nat_add_one_cpow`, under `1 < s.re`.

The third theorem is stated in the cosine form

`zeta(1-s) = 2 (2*pi)^(-s) Gamma(s) cos(pi*s/2) zeta(s)`.

These theorems provide a useful independent ambient reference once the
constructed names have been interpreted in ordinary complex analysis.
They are not a short route to the required iPRA theorem: their development
is noncomputable and uses general real/complex analysis. Mathlib also
assigns conventional total values at poles, so comparisons must be made
on apartness domains or as meromorphic identities, not by silently
equating those totalized values.

Official source:
`https://github.com/leanprover-community/mathlib4/blob/v4.32.0/Mathlib/NumberTheory/LSeries/RiemannZeta.lean`.

## Deliverable status

This file is an implementation blueprint and trust-boundary audit. It is
not a claim that the analytic iPRA formalization has been completed. The
human mathematical proof must provide every finite estimate referenced
above. The bridge modules contain no unfinished proof commands, but have
not been compiled in this environment. Full object-language formalization
requires implementing the seven modules and discharging their acceptance
gates.
