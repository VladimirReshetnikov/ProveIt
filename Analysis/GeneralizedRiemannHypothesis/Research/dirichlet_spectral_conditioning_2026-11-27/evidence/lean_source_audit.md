# Vendored Lean source audit

## Snapshot and verification performed

- Repository: `VladimirReshetnikov/ProveIt`.
- Pinned commit: `2a9f8e3ee74a1824d57546f0b1b4f1cef5df93d6`.
- Prefix: `Analysis/GeneralizedRiemannHypothesis/vendor/grh-lean/grh/`.
- Git subtree: `2e133df63d7f4da6b3059c4195324f8e9187ba73`.
- Retrieved the subtree recursively using the GitHub connector. GitHub reported 967 entries, without truncation, including 818 blobs. Independently computed Git blob SHA-1 values for all 818 corresponding cached files in `/workspace/scratch/b23454678602/sources/grh-lean/grh`; **818/818 match**.
- The `src/` tree contains 803 Lean files and 477,124 newline-delimited source lines: 495 `Lib.*` modules, 306 `New.*` modules, `Statements`, and `Main`. A static recursive import walk starting at `Main` reaches all 803 files. Its external imports are Mathlib modules.
- A comment/string-aware lexical scan of `src/` found no active occurrence of `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, `run_cmd`, `ofReduceBool`, or `addDecl`. This is a source scan, **not** a replacement for kernel replay. `Challenge.lean`, which intentionally contains placeholders, is not imported by a module in `src/`.
- Pinned toolchain: `leanprover/lean4:v4.35.0`; pinned Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679`.
- No full Lean build or independent checker replay was performed in this audit. Statements about successful independent checkers in `README.md` are repository claims, not newly reproduced evidence. The source review did not uncover a concrete flaw in the sampled proof interfaces below.

The all-file hash comparison makes the cached source suitable for substantive inspection of this exact snapshot. This does not mean that every one of the 477,124 lines has been manually checked.

## Exported mathematical interface

`src/Statements.lean` imports only `Mathlib`. It defines the following propositions, with ordinary Mathlib objects:

1. `RiemannZetaZerosOnLine`: if `riemannZeta s = 0`, `s` is not one of `-2,-4,...`, and `s != 1`, then `s.re = 1/2`.
2. `DirichletLNonvanishingRightOfHalf`: for every positive modulus `N`, every `DirichletCharacter ℂ N`, and every `s` with `1/2 < s.re`, the Mathlib `LFunction χ s` is nonzero, except that the principal-character value at `s = 1` is excluded.
3. `DirichletLZerosOnLine`: every zero of every such Dirichlet L-function in `0 < Re s < 1` lies on `Re s = 1/2`.
4. `PrimitiveDirichletLZerosOnLine`: the corresponding primitive-character restriction.

`src/Main.lean` exports `riemannHypothesis : RiemannHypothesis` using Mathlib's proposition, as well as `riemannZeta_eq_zero_re`, `LFunction_ne_zero_of_half_lt_re`, `LFunction_eq_zero_re`, and `LFunction_eq_zero_re_of_isPrimitive`. These are actual target statements; there is no substituted notion of zero or L-function in the exported interface. `New.Main` derives critical-line statements from `New.grh` through the functional equation and the nonvanishing of the gamma factor in the relevant region.

**Scope:** the GRH exported here is GRH for Dirichlet L-functions, with imprimitive characters included. It should not be relabeled as GRH for arbitrary automorphic, Artin, or other L-functions. Extra Euler factors of imprimitive characters have zeros outside the open critical strip covered by the exported zero-on-line statement.

## Analytic mechanism relevant to extensions

The following pieces are independent, named interfaces worth reusing rather than copying the entire proof.

### A. Meromorphic Laplace transform and residue order

`New.IsPolar E r`, in `Lib/Analytic/EntireLFunction.lean`, states that `E : ℝ → ℝ` is measurable, has a bound `|E(v)| <= C exp(v)` for `v >= 0`, and that its transform

\[
\int_0^\infty E(v)e^{(1-s)v}\,dv
\]

has a meromorphic continuation, with at most simple poles in `Re s > 0` and residue `r(s)`.

The same file proves that the logarithmic derivative of `entireL χ` has residue `analyticOrderNatAt (entireL χ) s`, with `entireL` regularizing only the pole of a principal L-function. The lemma `analyticOrderNatAt_entireL_eq_zero_iff` identifies zero multiplicity zero with actual nonvanishing; the proof excludes infinite analytic order using nonvanishing at `s = 1`.

### B. One-sided Landau criterion

`New.IsPolar.landau` in `Lib/Analytic/Landau.lean` proves:

\[
\beta>0,\quad E(v)\le e^{(\beta-1)v}\text{ eventually},\quad
\operatorname{Re}r(x)\ge0\ (x>\beta,\ x\in\mathbb R)
\quad\Longrightarrow\quad r(\rho)=0\ (\operatorname{Re}\rho>\beta).
\]

The proof constructs a positive measure from an exponential majorant minus the error function. It applies the real-boundary singularity principle for its Laplace transform. The nonnegative sign of the real residues rules out a boundary pole beyond `β`, yielding the desired half-plane. This is explicitly classified as a known Landau mechanism by the source.

### C. Weighted prime remainder and zero multiplicities

For a prime `d` and positive `q`, `New.primeRemainder d q x` in `New/Reduction/Zeros/PrimeError.lean` is

\[
R_{d,q}(x)=\sum_{n\le x}\Lambda(n)\mathbf1_{n\equiv1\pmod q}
\left(1-\left(\frac nd\right)\right)\left(\frac1n-\frac1x\right)
-\frac{\log x}{\varphi(q)}-c_{d,q}.
\]

`New.isPolar_primeRemainder` identifies the residue of the transform of `v ↦ R_{d,q}(exp v)` at `ρ != 0,1` as

\[
\frac{\sum_{\chi\bmod q}\bigl(m_\chi(\rho)-m_{\chi\otimes(\cdot/d)}(\rho)\bigr)}
{\varphi(q)\rho(1-\rho)}.
\]

The regularized transform has no pole at `1`. The source does not simply posit this formula: it proves the transform identity and derives the residues from logarithmic derivatives.

### D. Removing cancellation with a quadratic twist

`New.exists_entireL_quadTwist_ne_zero`, in `Lib/Analytic/QuadraticTwist.lean`, finds a prime `d` in a specified invertible class such that **all** the finitely many twisted L-functions are nonvanishing in a prescribed box `Re s >= β > 1/2`, `|Im s| <= H`. It uses `zero_density_quadTwist`, which bounds bad primes by `O(X^(1-δ/2))` for `β=1/2+9δ`, together with divergence of the prime harmonic sum in that class.

`New.LFunction_ne_zero_of_primeRemainder_le`, in `New/Reduction/Zeros/Criterion.lean`, combines B--D. Assumptions: `8 | q₀`, `d₀ ≡ 7 mod 8`, `(d₀,q₀)=1`, `β>1/2`, and an eventual upper bound `R_{d,q₀}(x) <= x^(β-1)` for every prime `d ≡ d₀ mod q₀`. The twist is chosen for the prospective zero's height. Its vanishing multiplicities are zero in that box, leaving a sum of nonnegative untwisted zero multiplicities. Landau then forces that sum, and each individual multiplicity, to vanish.

`New.grh` in `New/Reduction/OneSidedBound.lean` applies the bound with `q₀=18480 q` and `d₀=9240q-1`, then passes from the induced character back to the original character. The bound itself is `eventually_primeRemainder_le_rpow`.

**Useful boundaries for extensions:** the chosen prime in D depends on `β,H` (and the modulus). No one prime is asserted to work at every height. Eventual thresholds in the one-sided bounds are not asserted uniform in `q,d,ε`. The residue is a difference of multiplicities before twist elimination, so it cannot be treated as a nonnegative spectral weight without an additional argument. These are scope conditions, not discovered proof gaps.

## Geometric and linear-algebra mechanism relevant to extensions

`New.Data.exists_adjoint_singleLift_comp_eq` in `New/Determinant/Norms/AdjointThetaLift.lean` gives, for a single lift, an identity

\[
\Theta_j^*\Theta_j=c_jc_Q R_j,\qquad c_j\ne0.
\]

`New.Data.exists_adjoint_chain_comp_eq_smul_rallisProduct` in `New/Determinant/Chain/NormOfChain.lean` gives the corresponding identity for the chain, restricted to target forms:

\[
\Theta_\vartheta^*\Theta_\vartheta
=c(\vartheta)c_Q^m R(\vartheta),
\]

where `R` is the ordered product of the Rallis operators and

\[
|c(\vartheta)|=C\,\operatorname{Nm}(Q)^{e/2}
\prod_{1\le i<j\le m}\mathrm{quotientRatio}_{i,j}(\vartheta),
\quad C>0,\ e\in\mathbb Z.
\]

The source then takes determinants, using the generic lemma `New.normDet_sq_eq_pow_mul_det`, to obtain `exists_div_chainDeterminant_one_eq` and `exists_chainDeterminant_pos_and_div_chainDeterminant_one_eq`. The full-chain and individual lift Gram determinants are positive because the corresponding maps are injective.

This is a strong reusable entry point for spectral, singular-value, exterior-power, and mixed-Gram extensions: the available input is an **operator identity**, stronger than an identity of determinants. Nevertheless, the normalizing scalar is stated as complex; a claim about positivity of an unnormalized Rallis factor must account for its phase, rather than silently declaring the scalar positive. The chain proof also handles a zero-dimensional target as a separate branch. A nontrivial spectral conclusion should use `D.enough_forms`, which proves positive target dimension in the later main-inequality argument.

`New.Exchange.SquareLaw` in `New/Determinant/Chain/SquareLaw.lean` is an abstract finite-ring matching interface with two covariance laws and an equality of sums against matched data. `GridPaths.lean` supplies a finite path-turn induction, while `SpanningForms.lean` propagates sizes and denominators along those turns. These support extensions based on local exchange identities without requiring a new arithmetic construction from scratch.

## Source hashes for citations and reproducibility

Every path below is relative to the prefix above. A stable citation URL is `https://github.com/VladimirReshetnikov/ProveIt/blob/2a9f8e3ee74a1824d57546f0b1b4f1cef5df93d6/Analysis/GeneralizedRiemannHypothesis/vendor/grh-lean/grh/` followed by the path.

| Path | Git blob SHA-1 |
|---|---|
| `src/Statements.lean` | `1cd1bce93344065936b2b392b23306254e0785ef` |
| `src/Main.lean` | `1adf4187a938510363cdb0dde0a6d628ff39c600` |
| `src/New/Main.lean` | `fc0ae69627d2e66c3d1d57815d42f0aac5823432` |
| `src/Lib/Analytic/EntireLFunction.lean` | `1f4354050330c61245ab1c075c32f3ead9baa9ce` |
| `src/Lib/Analytic/Landau.lean` | `82f02212e0b4574396bc8198c3e84b6f36df9d9b` |
| `src/Lib/Analytic/QuadraticTwist.lean` | `6c26399571ac6b026c5bb144e65951bdaf20f796` |
| `src/New/Reduction/Zeros/PrimeError.lean` | `e37208a4e0d8567d47b9c4e38439790ebc3b979c` |
| `src/New/Reduction/Zeros/Criterion.lean` | `5c06362a50e044d491423fb3d830bae6a50c0075` |
| `src/New/Reduction/OneSidedBound.lean` | `99e5240de112527b739068b692e5007720d310c1` |
| `src/New/Reduction/MainInequality.lean` | `97f83ab52b2feb420e952a2722b4cef454b9e579` |
| `src/New/Determinant/Chain/NormOfChain.lean` | `02e0f4522b73496a748419506dec76c6e415f112` |
| `src/New/Determinant/Chain/ChainNorms.lean` | `6074db4eb17ddf1755bb74f05441516dc1a18e98` |
| `src/New/Determinant/Chain/SquareLaw.lean` | `2cc6166470f656127207e6f56f8f46d1cb1fb0d4` |
| `src/New/Determinant/Norms/AdjointThetaLift.lean` | `82d7c238ff88324623c21b2a335a1167053a3cda` |
| `src/New/Determinant/Norms/VectorKernel.lean` | `0531a2670210c8f409c3e91061252da3672ace52` |
| `src/New/Determinant/AuxiliaryForms/GridPaths.lean` | `fc45b488982f0021470fc2c177878b83a148b311` |
| `scripts/PrintAxioms.lean` | `ec5adcfd7baeff36130db9a763720ba1a6567c57` |
| `lean-toolchain` | `a6aff065db2882c535684f8c5bcd4f16e9a23915` |
| `lakefile.toml` | `171c6a3a8cf59aaf629a4a2c8b5533ae1e80c611` |

