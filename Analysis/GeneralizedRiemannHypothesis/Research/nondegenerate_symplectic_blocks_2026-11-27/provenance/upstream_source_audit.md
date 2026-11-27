# Source audit of `lsernau/grh-lean`

Audit date: 27 November 2026. Read-only inspection through the GitHub connector. This audit does not claim an independent Lean rebuild, replay, or complete mathematical reading of the development.

## Pinned source

The current default-branch commit returned by GitHub is
`72fead102f663d5c7a407964a13dc0cf9d977207` (commit date 25 November 2026). All file reads in this audit used this exact ref. The public repository has two Lake projects, `grh/` and `grh-compact/`; the tree contains 803 and 794 `.lean` files respectively under their `src/` directories. These counts include statement and entry modules. The readable source is about 30.05 MB and compact source about 7.42 MB. The repository README calls them approximately 300,000 and 76,000 lines of code. No repository writes were made.

Pinned base URL:
https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207

## What the declarations actually say

`grh/src/Statements.lean` imports only `Mathlib`. It defines four propositions using Mathlib's functions and characters. `grh/src/Main.lean` then exports five unconditional theorems:

1. `riemannHypothesis : RiemannHypothesis`, using Mathlib's proposition directly.
2. `riemannZeta_eq_zero_re : RiemannZetaZerosOnLine`. If `riemannZeta s = 0`, `s` is not one of `-2,-4,...`, and `s != 1`, then `s.re = 1/2`.
3. `LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf`. For every positive modulus `N`, every `DirichletCharacter ℂ N`, and every complex `s` with `s.re > 1/2`, the L-function does not vanish, provided the character is not principal or `s != 1`.
4. `LFunction_eq_zero_re : DirichletLZerosOnLine`. For every such character, a zero with `0 < s.re < 1` has real part `1/2`.
5. The primitive-character specialization `LFunction_eq_zero_re_of_isPrimitive`.

Thus the exported GRH scope is **Dirichlet L-functions**, including imprimitive characters and modulus 1. It does not by itself export Artin GRH, general automorphic GRH, GRH for arbitrary number-field Hecke characters, or a general Dedekind-zeta result. Its internal use of Hecke characters and unitary groups must not be confused with those stronger exported scopes.

The entry theorem really is a direct proof term:

```lean
theorem riemannHypothesis : RiemannHypothesis := New.zeta_zeros_on_line New.grh
theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf := New.grh
```

The condition excluding `s=1` for a principal character reflects the pole and Lean's total-function convention. It is not an RH-shaped extra hypothesis. `New/Main.lean` passes from right-half-plane nonvanishing to the critical line using functional-equation symmetry; its conditional `h : DirichletLNonvanishingRightOfHalf` is discharged in `Main.lean` by `New.grh`.

Primary source URLs:

- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Statements.lean
- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Main.lean
- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Main.lean

## The mathematical architecture found in the source

The reduction is an arithmetic determinant argument. With carefully constructed data `D`, let `d_T` be the target-space dimension, `M` the common main amount, `R` a weighted prime-sum remainder, and `m` the number of theta lifts. It constructs an almost full-dimensional family of target forms and compares the logarithmic Gram determinant `V`, corrected by twice an arithmetic index `δ`.

**Theorem A, short integral forms.** `span_short_integralRamified_eq_top` says integral source forms whose translated lifts have squared norms at most

`exp(M - m R + f a (log b)^4)`

span the source. The companion `indexLe_normalizedPoincare` controls their index in the target's twisted lattice by the number of chosen translates times the source dimension times `2 f a (log b)^3`. The underlying size/divisibility comparison uses theta derivatives, their p-adic divisibility, a chain of lifts, and seesaw identities.

**Theorem B, enough forms.** `enough_forms` supplies a finite set `t` of translates with

`|t| dim(source) <= 5 d_T log(1+2b^2)`

and combined image dimension at least `(1-4/b^2)d_T`. The method is a quantitative spanning argument built from near-isometry and second-moment estimates. Finite-field singular-compression bounds are an ingredient.

**Theorem C, integral forms are long.** `integral_forms_long` gives

`d_T (M - 3 f a (log b)^4) <= V + 2δ`

for independent target forms spanning at least `(1-4/b^2)d_T`. The proof completes a family by auxiliary forms, chooses twists separately at each prime, uses injectivity of the lifts, and controls the height of the ratio of chain determinants. The product formula turns simultaneous local integrality and archimedean smallness into a lower bound. Controlling denominators of the projections is where the Selmer/congruence machinery enters.

After Hadamard's inequality supplies the other bound, the main amount cancels. `star_inequality` proves the precise displayed inequality

`D.m * D.totalRemainder <= D.f * D.a * D.logB ^ 5`.

The scales include `(log b)^100 <= x`, `x^(10^6) <= x1`, `x1^(10^6) <= b`; data construction eventually allows `m >= sqrt(x)` and `log b <= 2 x^ε`. Larger-cutoff prime-number-theorem errors disappear, leaving a one-sided square-root-scale bound for the weighted prime remainder.

The remainder is

`R_{d,q}(x) = Σ_{n<=x, n≡1 mod q} Λ(n)(1-(n/d))(1/n-1/x) - (log x)/φ(q) - c_{d,q}`,

where the constant is chosen so the remainder tends to zero. `eventually_primeRemainder_le_rpow` establishes

`R_{d,q0}(x) <= x^(-1/2+ε)`

eventually for every positive ε, provided `18480 | q0`, `d` is prime, and `d ≡ q0/2-1 (mod q0)`.

The analytic criterion `LFunction_ne_zero_of_primeRemainder_le` is more general: a one-sided bound of exponent `β-1` for all auxiliary primes in a suitable class, with `β>1/2`, excludes Dirichlet zeros to the right of β. It chooses an auxiliary quadratic twist with no interfering zeros in the relevant finite-height region. The Laplace/Mellin transform of the remainder then has residues given by nonnegative zero multiplicities divided by `φ(q0)s(1-s)`, and a Landau argument rules them out. Finally `New.grh` applies the criterion at modulus `q0=18480q` and descends from the induced character.

Primary source URLs:

- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/ShortAndEnough.lean
- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Determinant/Twist/LongForms.lean
- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/MainInequality.lean
- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/OneSidedBound.lean
- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/Zeros/Criterion.lean

## A clean finite theorem that can be transferred independently

`New.Spanning.SecondMoment.PositiveType` isolates a finite-group lemma. Let `π:G -> GL_n(F_q)` be a representation, let `A0,A1` be `n x m` matrices, and let `Θ:G -> R_{≥0}` be of positive type, so `Θ(a^{-1}b)=<u_a,u_b>` for a vector family. Assume that for every nonzero `v in F_q^m`, the Θ-masses of the stabilizers of `A0 v` under π and of `A1 v` under the inverse-transpose representation are at most `Y`. Then

`q Σ_{g:det(A1^T π(g) A0)=0} Θ(g) <= 2 Σ_g Θ(g) + q^m sqrt(q^n) Y`.

This is `card_mul_sum_det_eq_zero_le`, proved directly in the inspected source. The proof rewrites character sums as inner products of finite tensor sums. The squared norms of these sums are stabilizer masses, giving Cauchy-Schwarz bounds. Finite Fourier orthogonality counts the kernel of the compressed matrix; singularity forces at least q kernel elements.

This lemma makes the connection to further finite-field matrix results explicit and independent of RH/GRH. Its key structure is the relationship between compression, kernel counting, and invariant bilinear forms. Stronger exact laws should account for restricted forms and mutual geometry rather than rely only on rank or a worst-case stabilizer bound. Prior delivered work already contains kernel-moment and symplectic extensions, so those must be credited rather than reintroduced as new.

Another isolated method is the Frobenius-cycle root lemma: compare degree with multiplicities of zeros after a one-variable substitution, while a Gauss filtration tracks valuation plus weight under all group translates. The resulting inequalities on extreme exponents control elementary divisors. The source explicitly relates it to Stepanov, twisted Dickson forms, and G-zip weight cones; the general root-counting idea is not new by itself.

Primary source URLs:

- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Spanning/SecondMoment/PositiveType.lean
- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Spanning/SecondMoment/SpanningTheorem.lean
- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/UpperBound/ElementaryDivisors/RootLemma.lean

## Trust and verification boundary

The project pins Lean `v4.35.0` and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. `grh/README.md` reports that all source modules compile without `sorry`, that the five entry theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`, and that independent checkers nanoda, con-leche, and con-ron accepted exported proofs. It also reports a successful Comparator run. These are **repository-reported checks**, not checks reproduced in this audit.

`scripts/PrintAxioms.lean` contains the expected five `#print axioms` commands. `comparator.json` permits only those three standard axioms and compares `Challenge` against `Main`. `Challenge.lean` deliberately contains `sorry`; this is a statement template for comparison, not imported by the proof. Its presence should not be reported as a hole in the actual theorem proof. The Lake default targets are `Lib`, `New`, and `Main`.

The inspected proof modules contain no `axiom`, `sorry`, `admit`, or `unsafe` tokens. This was a scan of the inspected subset only, and is not a repository-wide proof of absence. The exact top-level statement file and source-level discharge of its hypotheses were checked; the full dependency closure and exported kernel terms were not replayed. No assertion of external mathematical consensus follows from these observations. Equally, the source inspected gives no basis to dismiss the claim merely because RH was formerly open.

For any new theorem in the main deliverable, the defensible labels are: (i) a proved finite theorem inspired by an explicit upstream lemma, independent of RH if applicable; (ii) a theorem conditional on the exported Dirichlet-GRH theorem if it uses it; (iii) publication priority provisional unless literature work supports more. A fresh formalization must not be described as kernel-checked unless it was actually compiled or replayed.

The external source snapshots used for this audit are not bundled. Their pinned repository paths, URLs, byte lengths, and SHA-256 hashes are recorded in `provenance/sources.json`.
