# Route from the checked kernel to object-iPRA

## 1. What has and has not been formalized

The supplied Lean kernel proves finite logical transfer and rational scalar
estimates. It deliberately does not pretend that a theorem in Lean's `Prop`
is automatically an iPRA proof. The target for a completed ProveIt integration
is an explicit value of

```lean
Γ ⊢[PRAAx] φ
```

in the namespace `LeanProofs.ConciseIPRA`, with `φ : Fm PTm n`. Every
primitive recursive operation used in `φ` must be a fixed term or a named
symbol with its defining equations. Quantifier-free induction must be applied
to an actual quantifier-free formula, rather than a host statement about an
infinite metric space.

The archive supplies the full mathematical arguments and a checked host
kernel, but does not supply the new literal `Prf PRAAx` proof values for the
operator solver, continuous-model comparison, or PDE application. Existing
repository proof values below are integration dependencies, not evidence that
these new applications have already been checked.

## 2. Inspected repository interfaces

All paths below were inspected at commit
`5f3be02388442f16487d2dc5c2529961dd783d2b` of
`VladimirReshetnikov/ProveIt`. Their common prefix is
`Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/`.

| Module | Relevant declarations | How it is used |
|---|---|---|
| `Foundations/SetoidInterpretation.lean` | `Presentation`, `tr`, `cong`, `sound` | Literal first-order interpretation through a domain formula and an equivalence formula, provided all operation and axiom contracts are derived. |
| `Foundations/ObservationComposition.lean` | `ObsData`, `horizon`, `guarantees`, `compose_obs` | Combine finitely many observations using the maximum of their input demands; no unlimited oracle evaluator. |
| `Foundations/FiniteReplay.lean` | `replay`, `replay_at` | Replace a finite input table by another agreeing on the queries actually used by a trace. |
| `Foundations/ContractionIterates.lean` | `Contr`, `CInv`, `iter_contract`, `cauchy_iterates` | Existing exact half-contraction invariant and exact iteration fusion. |
| `Foundations/DiscreteGronwall.lean` | `GInv`, `g_step`, `gronwall`, `growth`, `gronwall_three` | A model for denominator-cleared recurrence induction; its existing `gronwall` theorem assumes growth factor at least one, so it is not itself the new stationary-noise contraction theorem. |
| `Analysis/ErrorBudgets.lean` | `ad_tri`, `ad_prod_step`, `sum_budget`, `prod_budget`, `inv_budget` | Finite sums, products, and separated reciprocals after denominator clearing. |

The inspected source identities and exact URLs are in `PROVENANCE.json`.
The repository root pins the same Lean version used here, 4.32.0.

## 3. Coding conventions and primitive recursive programs

Use the existing natural, integer, tuple, finite-list, and rational coding in
`IPRADerivations`. A mathematical rational is represented by a signed integer
numerator and a positive natural denominator. Rational inequalities become
integer inequalities by multiplication by the explicitly positive
denominators. The algorithms below can avoid gcd normalization entirely:
numerators and denominators are allowed to grow. Zero-denominator cases of
total coding functions receive a fixed default; every theorem retains the
positive-denominator guard.

A dense Hilbert-space vector is a finite rational linear combination of a
specified sequence of generators. Its code records the length and rational
coefficients. Inner products of dense generators are supplied by a fixed
primitive recursive rational presentation, or by rational approximation
contracts with an explicit demand. For the polynomial energy-space example,
the relevant dense inner products are exact integrals of rational
polynomials. Padding coefficient lists with zeros handles differing lengths.

Do not add a total primitive recursive function `eval(code,input)` for all PR
programs. There is no such universal PR evaluator. Instead, each operator,
coefficient name, finite-domain atomic evaluator, and modulus is a fixed
program for the current theorem schema. An input stream is supplied by a
finite table for the required observation horizon. `compose_obs` combines
these horizons; `replay` proves that extending the table does not alter an
already executed trace.

At fixed output precision `n`, the solver is a finite loop. Its state consists
of a dense-vector code, loop index, input-table references, and the auxiliary
numerical bounds used by the certificate. The loop bound and every query
demand are fixed PR terms. Intermediate code sizes may grow very rapidly;
primitive recursiveness is not a claim of practical efficiency. An explicit
size recurrence for the chosen representation must be included in a final
object implementation.

## 4. Exact induction invariant for stationary noise

Let the contraction factor be `q=a/b`, the initial majorant be `R=r/s`, the
per-step perturbation be `ε=p/t`, and the stationary reserve be `E=e/f`.
All seven numerators and denominators are natural numbers; assume

```text
0 < b, 0 < s, 0 < t, 0 < f,
a ≤ b,
p*b*f ≤ (b−a)*e*t.
```

The last inequality is exactly `ε ≤ (1−q)E`. Define two PR sequences by

```text
N(0) = r*t,
N(j+1) = a*N(j) + p*s*b^(j+1),
D(j) = s*t*b^j.
```

Then `N(j)/D(j)` is the exact rational solution of the majorant recurrence
`x(0)=R`, `x(j+1)=q*x(j)+ε`. The invariant

```text
I(j) : f*N(j) ≤ r*t*f*a^j + e*s*t*b^j
```

is quantifier-free. It is precisely `x(j) ≤ q^j R + E` after clearing positive
denominators. The base case is immediate. In the induction step, the
difference between the next right and left sides is

```text
a * [r*t*f*a^j + e*s*t*b^j − f*N(j)]
 + s*b^j * [(b−a)*e*t − p*b*f].
```

Both bracketed quantities are nonnegative under the induction hypothesis and
the noise bound. Thus the step can be implemented as an `ipra_le` polynomial
certificate with weights `a` and `s*b^j`. The proof uses the defining
equations of `N`, the successor equations for powers, natural order, and
polynomial identities. It does not need induction on a statement about real
numbers or quantified Cauchy sequences.

For errors bounded above by the majorant, a second finite induction shows
that each trace's rational distance certificate is at most `N(j)/D(j)`.
Where an actual norm is irrational, it remains represented by upper-bound
certificates, not by an invented exact rational value.

Suggested object module:

```text
IPRADerivations/Analysis/PerturbedContraction.lean
  noiseInv                -- the formula I(j)
  noise_base              -- its base derivation
  noise_step              -- the weighted polynomial certificate
  stationary_noise        -- PRA.qfInd applied to I
  stationary_noise_at     -- specialization to a bounded trace length
```

The final declaration should be a derivation in `Prf PRAAx`. The supplied
host theorem `perturbed_contraction_of_noise` checks the same scalar
mathematics but is not a replacement for this module.

## 5. Exact induction invariant for the clock

Write the gap as `δ=d/b`, with `0<d≤b`, so `q=(b−d)/b`. The checked host
inequality

```text
(1+jδ)(1−δ)^j ≤ 1
```

becomes the quantifier-free natural inequality

```text
J(j) : (b+j*d)*(b−d)^j ≤ b^(j+1).
```

Its step uses the exact identity

```text
(b−d)*(b+(j+1)*d) + (j+1)*d^2 = b*(b+j*d).
```

Multiply this identity by `(b−d)^j`, discard the nonnegative second term,
and apply `J(j)`. The guarded subtraction `b−d` is legitimate because
`d≤b`; one may equivalently introduce a separate natural `a` with `a+d=b`
and avoid subtraction in the polynomial certificate.

If `h*d≥b`, then `b+h*d≥2b`. The invariant at `h`, followed by positive
cancellation of `b`, yields

```text
2*(b−d)^h ≤ b^h.
```

Thus one block of `h` steps halves the error. The power identities are proved
by quantifier-free induction on the exponent. The remaining amplitude bound
is the natural inequality `C≤2^C`, equivalently `C*2^(−C)≤1`; it also has an
elementary quantifier-free induction.

Choose integers with

```text
h*d ≥ b,
2*λ ≤ δ*C,
R ≥ the initial radius bound,
k = n+3+C,
N = h*(n+R+3).
```

The coefficient `λ` is a positive rational. If `λ=l/u`, the precision
condition is the natural inequality `2*l*b ≤ d*C*u`. Ceilings such as
`h=ceil(b/d)` and `C=ceil(2*l*b/(d*u))` are bounded integer division
programs with positive denominators. No logarithm, search for a convergence
time, or square root appears in the clock.

The reserve `E=C*2^(−k)` is at most `2^(−n−3)`, as is `R*q^N`. Their sum is
at most `2^(−n−2)`. `solver_budget` checks this entire rational calculation.

Suggested object module:

```text
IPRADerivations/Analysis/ContractionClock.lean
  clockInv, clock_base, clock_step
  block_halving, block_decay
  amplitude_absorb, shifted_amplitude
  radius_at_clock, solver_budget
```

The formulas in this section are the actual targets to quote as `Fm PTm n`;
the host function types alone do not settle the object-language work.

## 6. Coherent output names from two finite runs

This construction avoids assuming an exact solution or iterating an
already-completed infinite object.

Let `T` have contraction factor `q=1−δ`, with `0<δ≤1`, and assume a dense
approximation `F_n` satisfies

```text
||F_n(v)−T(v)|| ≤ η_n,
η_n = δ*E_n,
E_n = 2^(−n−3),
||T(0)|| ≤ δ*R.
```

If the executable approximator only promises a smaller error than `η_n`,
use that same upper bound. Its validity is a finite arithmetic contract on
the dense vector and the input observations.

Define `z^n_0=0`, `z^n_(j+1)=F_n(z^n_j)` and `c_n=z^n_(N_n)`, where
`N_n=h(n+R+3)` and `hδ≥1`. The ball invariant

```text
||z^n_j|| ≤ R+E_n
```

is preserved because `qR+||T(0)||≤R` and `qE_n+η_n=E_n`.

For `m≥n`, we have `N_m≥N_n`. Compare the entire `n`-run with the final
`N_n` steps of the `m`-run. Their initial distance is at most `R+E_m`.
At every paired step, the triangle inequality and contraction contract give

```text
d_(j+1) ≤ q*d_j + η_n + η_m.
```

Apply the stationary-reserve calculation with reserve `E_n+E_m`. At the
last paired step,

```text
||c_n−c_m||
 ≤ q^(N_n)*(R+E_m) + E_n + E_m
 ≤ R*q^(N_n) + E_n + 2*E_m
 ≤ 4*E_n
 = 2^(−n−1).
```

Here `q^(N_n)≤1`, `R*q^(N_n)≤E_n`, and `E_m≤E_n` are all finite scalar
lemmas. Symmetry gives the corresponding estimate when `n≥m`. Thus the
output is a regular Cauchy name with an explicit modulus. The induction
state consists of two finite dense-vector traces and rational bounds;
the invariant can be Booleanized and used in `PRA.qfInd`.

### Fixed-point residual without a preexisting fixed point

For fixed `n`, put `w_j=||z^n_(j+1)−z^n_j||`. Approximate contraction gives

```text
w_j ≤ q^j*(||T(0)||+η_n) + 2*η_n/δ.
```

One extra step after `N_n` is enough to certify the residual:

```text
||c_n−T(c_n)|| ≤ w_(N_n)+η_n
 ≤ (2+3δ)*E_n.
```

The last inequality uses `||T(0)||≤δR`, `R*q^(N_n)≤E_n`,
`q^(N_n)≤1`, and `η_n=δE_n`. This tends to zero with a fixed precision
shift; for the report's Hilbert contraction, `δ≤1/2`, so the coefficient is
at most `7/2`.

Consequently, the regular output name and its image under the continuous
extension of `T` are equivalent in the completion. That proves existence of
a fixed-point name without presupposing a solution. Uniqueness follows from
`d(u,v)≤q*d(u,v)` and the positive gap, interpreted using rational upper
cuts. Passing to the completion is a separate semantic adequacy argument,
or an explicitly implemented name setoid; it is not an unexplained use of
completeness inside scalar iPRA.

For a fixed `n`, letting the explicit bounds for `m` improve gives the sharper
semantic error `d(c_n,u)≤R*q^(N_n)+E_n≤2^(−n−2)`. The existence proof
itself remains the finite two-run argument above.

## 7. The Hilbert-space and PDE interfaces

For a bounded coercive linear operator, the dense algebraic calculation is

```text
||v−λAv||²
 = ||v||² − 2λ<Av,v> + λ²||Av||²
 ≤ (1−2λm+λ²M²)||v||².
```

Choose `λ=m/M²` and `δ=m²/(2M²)`. With `0<m≤M`, we have
`0<δ≤1/2` and

```text
1−m²/M² ≤ (1−δ)².
```

All constants are rational. In a dense rational presentation, prove the
inner-product identities and squared-norm bounds after clearing denominators.
The positive norm upper-cut rules then imply the contraction bound. This
avoids computing an exact square root merely to certify the bound.

The following obligations remain distinct and must be implemented for each
application:

1. Dense-vector operations and their primitive recursive code-size bounds.
2. Inner-product arithmetic and the finite Cauchy-Schwarz inequality.
3. Validity and precision demands of `a(v,k)` approximating `Av` and `b(k)`
   approximating the right-hand-side vector.
4. Coercivity and operator-norm bounds, expressed as derived arithmetic
   contracts over the chosen presentation. An arbitrary assertion that a
   black-box operator is coercive is not a decidable finite certificate.
5. The finite trace's ball, perturbation, coherence, and residual invariants.
6. The regular-name setoid and the fact that the operator preserves its
   equality relation.
7. The application-specific identification of the represented fixed-point
   equation with the variational problem.

For the one-dimensional Dirichlet problem in the report, the last step uses
the derivative representation of the energy completion and the explicit
formula for the operator and load vector. It does not require a general
Riesz representation theorem, a weakly convergent subsequence, or an
unbounded search for a minimizer. General Hilbert spaces lacking the supplied
effective Riesz map or operator approximation contract are outside that
specific application.

## 8. Positive formula transfer and continuous model comparison

The checked `PosFormula`, `Env`, `push`, `Related`, and `Holds` definitions
give the complete host syntax and semantics for the positive fragment.
`positive_transfer` proves preservation under explicit back/forth selectors.
`eval_correct` proves the finite Boolean evaluator correct.

For a fixed object-language instance, replace host atoms by a fixed coded
signature. Every term evaluator must be a fixed PR program, or evaluation
must use a supplied finite table with a derived correctness contract. A
finite bounded universal quantifier is a Boolean product/fold; a finite
bounded existential quantifier is a Boolean disjunction/fold. Apply the
existing bounded-fold derivations to their defining recursions.

For source and target finite observations, the atomic transfer contracts are
actual derivations in `Prf PRAAx`. The formula's proof is then a structural
metalevel compilation: conjunction and disjunction use the corresponding
`Prf` constructors, existential transfer substitutes the `forth` term, and
universal transfer substitutes the `back` term. For a fixed formula this is
a finite proof construction. The source and target margins are retained in
the atom formulas. The proof introduces no quantifier-depth error term.

When the source is a genuine compact metric structure, finite nets represent
approximations to its bounded quantifiers. They are not finite substructures
unless operations preserve those nets. For the report's real-valued
continuous formulas, prove atomic oscillation bounds, use the nonexpansive
min/max/complement operations, and apply the corresponding net infimum and
supremum bounds. The two-direction approximation theorem is an additional
numeric induction, not literally the Boolean `positive_transfer` theorem.

The exact interpretation theorem `SetoidInterpretation.sound` remains
available for genuinely numerically presented sorts whose operations and
axioms have the required proof contracts. It must not be cited as a blanket
interpretation of all real functions, all models, or unrestricted second-order
quantification. Semantic statements about arbitrary streams and the first-
order arithmetic sentences extracted from their finite observations must
remain separately labelled.

## 9. Suggested implementation order

1. Add the denominator-cleared stationary-noise and clock modules; their
   invariants and polynomial certificates are fully specified above.
2. Add a finite two-trace module parametrized by the local approximate-
   contraction rules; derive the coherent-name and residual bounds.
3. Instantiate the dense rational polynomial energy space. Check the exact
   inner-product, derivative, endpoint, and integration identities.
4. Implement the fixed coefficient and load approximation interfaces and
   compose their demands with `ObservationComposition.compose_obs`.
5. Quote the regular-name equality and continuity formulas and prove the
   operator's setoid congruence. Use `SetoidInterpretation.sound` only after
   its actual hypotheses have been supplied.
6. Implement finite quantifier folds and the positive-formula compiler;
   separately add rational min/max and finite-extremum comparison for the
   continuous-valued logic theorem.
7. Export the literal `Prf PRAAx` endpoints, print their axiom dependencies,
   and replay exactly the affected dependency closure. Record host-semantic
   adequacy separately from object-provability.

This order makes every new theorem concrete before any broad theorem is
advertised as a checked iPRA derivation.
