# Lean completion plan

## Status and exact completion criterion

`Blueprint.lean` is an **uncompiled interface and implementation outline**.
There was no Lean executable in the environment used to prepare the archive.
It does not contain a completed transcendence proof, an instance of
`Programs`, or an instance of `Derivations`. It contains no `axiom` or
`sorry` declarations. The conditional `nativeE` and `nativePi` transport
already supplied internal derivations; they do not manufacture them.

The completion criterion is an actual value

```lean
theorem finiteTranscendence : Derivations concretePrograms := ...
```

with `concretePrograms` instantiated by the programs and explicit bounds in
the paper. In particular, its two proof fields have the types

```lean
Prf PRAAx [] (AllAccepted concretePrograms.eTest)
Prf PRAAx [] (AllAccepted concretePrograms.piTest)
```

A proof of `Transcendental ℚ Real.pi` or `Transcendental ℚ (Real.exp 1)` in
ambient Mathlib, however correct, would not meet this criterion. Avoiding
`Classical` alone is also insufficient. The restriction concerns the
object-language induction rules, not merely Lean's choice axioms.

The blueprint's `evalPR` is only the external Lean semantics of primitive
recursive syntax. Universal evaluation of arbitrary PR programs is not a
primitive recursive operation. It is **not** an object-language function
symbol. The finitistic proof uses fixed compiled programs whose input is a
polynomial code, not a program code supplied to a universal evaluator.

The paper gives a stronger uniform inequality at every sufficiently late
precision. `AllAccepted` only asks for the inequality at the computed
precision index, which already suffices to refute the encoded zero
relation. The later-index version can be included as an additional internal
lemma using the same error bounds.

## Verified repository interfaces

The following files were inspected at ProveIt commit
`0bf379a84212abd05e9a3f0b1320a3d7da509cf9`:

| File in the ConciseIPRA Lean import root | API used |
|---|---|
| `PR.lean` | `PR`, `PTm`, `PRAAx`, `PRA.qfInd` |
| `Deduction.lean` | `Prf`, equality substitution, natural deduction |
| `PRAToScalar.lean` | `FromPRA.code`, `FromPRA.interp` |
| `NativeBiInterpretation.lean` | `pra_iff_native`, `NFm.ofPRA` |

The namespace is `LeanProofs.ConciseIPRA`. `PR` has constructors for zero,
successor, projections, composition and primitive recursion. Its recursion
argument comes first. `PRA.qfInd` requires the explicit hypothesis
`φ.QF`; the base and successor derivations then produce `Fm.all φ`.
This is the intended enforcement point for every induction below.

## Suggested module order

### 1. `Arithmetic/Codec.lean`

Implement signed integers, unreduced rationals with positive denominators,
finite lists and rectangular arrays as natural-number codes. Noncanonical
rational codes are acceptable: equality and order use cross multiplication.
Make all malformed inputs total by an explicit default value. Provide
projection and update lemmas using quantifier-free induction.

Implement characteristic functions for zero, sign, comparison, divisibility,
and bounded conjunction. The latter turns an invariant asserting equality
at every array index below a bound into one atomic equation `check = 1`.

### 2. `Arithmetic/FiniteAlgebra.lean`

Implement addition, multiplication, power, factorial, bounded sums,
polynomial Horner evaluation, coefficient convolution, derivatives,
matrix multiplication, trace, and determinant. The determinant may use the
Leibniz formula with bounded permutation enumeration. Efficiency is not
needed for primitive recursiveness, and this route avoids introducing an
unproved fast determinant algorithm.

Key internal lemmas:

* telescoping a difference of powers and the polynomial Lipschitz bound;
* coefficient extraction after differentiation;
* `r!/(p-1)!` is integral and divisible by `p` for `r >= p`;
* a nonzero integer has absolute value at least one;
* factorial domination with the explicit threshold used in the paper.

### 3. `Analysis/FiniteExp.lean`

Implement Taylor truncations and use
`expLength R s = 4*(R+1)^2 + s + 4`.
Prove the geometric-tail bound first for two finite truncations. Prove
exponential addition coefficientwise from the binomial formula. Store an
error budget alongside every truncated calculation rather than importing
`Real`, limits, integration or power-series completeness into the internal
proof.

For the Hermite identity, differentiate the finite polynomial expression
`exp((1-t)B) F(tB)` coefficientwise, or prove its finite coefficient
recurrence. Integrals of rational polynomial coefficients are the explicit
map `t^j -> 1/(j+1)`. Bound the discarded exponential terms with the same
Taylor modulus. This supplies the integral notation used in the paper
without assuming a fundamental theorem of calculus inside iPRA.

A particularly concrete implementation uses `E_L` throughout. Define
`I_L=∫ E_L((1-t)B) B f(tB)` and
`D_L=B^(L+1)/L! ∫ (1-t)^L F(tB)`. Polynomial differentiation gives the
exact finite identity `E_L(B)F(0)-F(B)=I_L-D_L`. With coefficient majorant
`V=Σ_j |F_j|R^j`, the defect has norm at most
`V R^(L+1)/(L+1)!`. Prove this directly from
`D_L=Σ_j F_j B^(L+1+j)j!/(L+j+1)!`, using the finite beta integral
identity; no general positivity theorem for polynomial integrals is needed.
This is the recommended internal lemma; the limiting notation in the
paper is a readable abbreviation.

### 4. `Analysis/Machin.lean`

Implement the rational `piApprox`. Prove the alternating-tail bound by
grouping adjacent terms. Prove
`exp(2*i*atan x)=(1+i*x)/(1-i*x)` by the finite coefficient recurrence
`(n+1)e_(n+1)=2*i*e_n-(n-1)e_(n-1)` and the majorant given in the paper.
Check the exact Gaussian identity
`(12+5i)^4=i*(28560+239i)` by ring arithmetic. This produces a finite
quantitative version of `exp(i*pi)=-1`.

### 5. `LinearAlgebra/CompanionExterior.lean`

Construct the rational companion matrix directly from coefficient arrays.
Index exterior basis vectors by bit masks below `2^d`. Compute wedge signs
by inversion parity; every relevant search is bounded by `d` or `2^d`.

Prove the additive compound identity by the finite multinomial formula

```
B_k^n(v_1 ∧ ... ∧ v_k)
 = Σ_(n_1+...+n_k=n) n!/(n_1!...n_k!)
       A^n_1 v_1 ∧ ... ∧ A^n_k v_k.
```

Prove `det(I+M)=Σ_k trace(Λ^k M)` by principal-minor expansion. Combining
the two identities, with explicit finite tails, gives
`trace(exp B)=det(I+exp A)`.

For a fully finite implementation, compare `det(I+E_L(tA))` with
`trace(E_L(tB))` coefficientwise through degree `L`. Their value difference
at `t=1` is at most `C*2^(-L-1)`, where
`C=d!*(1+3^(2R))^d` and `R>=||A||_infty`. This follows by bounding the sum
of absolute determinant coefficients weighted by `2^j` by `C`. An explicit
choice `L>=C+s+2` makes the defect less than `2^(-s)`.

No field splitting, eigenvalue selection, polynomial factorization, root
isolation, general fundamental theorem of algebra, or classical spectral
theorem is part of this route.

### 6. `LinearAlgebra/TraceHermite.lean`

For integer `M=c*B`, compute `charpoly M = X^m G`. The multiplicity `m` is
the first nonzero coefficient index, found by a scan of length at most the
matrix dimension. Let `C` be the integer companion matrix of `G`.
Newton identities give

```
trace(u(M)) = m*u(0) + trace(u(C))
```

for each rational polynomial `u`. This replaces a primary decomposition.
The companion identity `G(C)=0`, high derivative divisibility, and the
explicit composite choice of the Hermite parameter give the nonzero
integer trace. Prove the norm bound and compare it with the factorial
remainder estimate to obtain the quantitative matrix lemma.

### 7. `Transcendence/E.lean` and `Transcendence/Pi.lean`

Instantiate the Hermite polynomials and the explicit auxiliary integers in
the paper. For pi, use the quantitative companion-matrix residual estimate;
do not extract a root or choose a factor on the assumption `P(pi)=0`.
Propagate numerical bounds through the coefficient-height, degree,
denominator and determinant formulas. Compute a final precision index
whose evaluation error is below half the separation margin.

Concretely, the paper uses the integer reciprocal margins `B_e=2D` and
`B_pi=2UKH`, with their auxiliary integer factors defined in the respective
proofs. For a constant monomial the reciprocal margin can be `1`. With the
original polynomial's integer Lipschitz bound `Lambda`, use
`N=4*B*Lambda+1`. The elementary inequality `2^N >= N+1` removes any need
for a logarithm or an open-ended precision search.

Implement `eTest` and `piTest`: they return `1` on zero polynomials and
otherwise check the computed rational separation inequality. The proof of
their correctness is uniform in the polynomial code. The all-input
statement then has exactly the `AllAccepted` form in the blueprint.

### 8. `Transcendence/Internal.lean`

Assemble the object-theory derivations with `Prf` constructors and
`PRA.qfInd`, producing `Derivations concretePrograms`. Apply
`pra_iff_native.mp` to obtain proofs in the native ConciseIPRA calculus.
If a literal checker certificate is desired, add a separately verified
reification of these derivations into the chosen finite checker syntax.
The existing theorem about a syntactic interpretation does not by itself
provide that serialization.

## Quantifier-free induction inventory

| Loop/recursion | Explicit bound | Quantifier-free invariant |
|---|---|---|
| Rational list/matrix arithmetic | Coded lengths/dimensions | Cross-multiplied entry equalities, encoded by bounded conjunction |
| Polynomial multiplication and derivatives | Degree/coefficient length | Coefficient arrays agree with convolution or factorial formula |
| Factorial remainder | Chosen natural parameter | Integer cross-multiplication of the claimed bound |
| Exponential finite tails | `expLength R s` and later finite endpoint | Partial geometric majorant inequality |
| Machin coefficient recurrence | Taylor order | Bounded coefficient-array equality |
| Exterior power expansion | `(n+1)^k`, `2^d` | Bounded multinomial coefficient identities |
| Determinant | Dimension factorial | Partial signed permutation sum |
| Newton sums | Power index and characteristic degree | Finite recurrence equality |
| Zero coefficient stripping | Matrix dimension/polynomial degree | Prefix is zero and next coefficient is retained |
| Final acceptance | Polynomial code as free parameter | Boolean acceptance equation |

The table is a checklist for formalization, not a claim that unspecified
recursion is automatically admissible. Each indicated invariant must be
represented by a concrete `Fm PTm (n+1)` and accompanied by a proof of its
`QF` property. All coefficients and intermediate arrays may be huge; their
sizes remain primitive recursive. The argument seeks a proof-theoretic
bound, not a practical transcendence test for large polynomials.

## Validation and integration

Use the repository's pinned Lean and Mathlib versions. Start by compiling
the blueprint and fixing any interface elaboration issues, since it was
not executable here. Compile each finite-algebra module before beginning
the two final proofs. Numerical examples are useful for catching sign and
scaling errors, but do not replace the uniform internal derivations.

An optional final semantic corollary can identify the two rational names
with Mathlib's `Real.exp 1` and `Real.pi`. It should sit in a separate file:
it explains the familiar real-number statement while preserving the exact
logical status of the finitistic proof.
