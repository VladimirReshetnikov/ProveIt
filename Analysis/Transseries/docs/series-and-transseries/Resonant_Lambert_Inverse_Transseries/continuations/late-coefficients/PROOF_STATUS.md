# Claim, dependency, and proof-status map

This file identifies what is proved in the accompanying article, which inputs are imported, and which questions remain open. The identifiers below are the stable LaTeX labels in `sections/*.tex`; theorem numbers may change during integration. “Proved here” means that the article supplies a conventional mathematical proof. It does not mean that a proof assistant has checked the result or that the result has undergone independent peer review.

The repository comparison is with ProveIt commit `8f5afd4d7565df808359f6a0c22f87f79a119bb9`. The principal predecessor is *Double Resonance and Nested Stokes Geometry in Polylogarithmic Lambert Inversion*, dated 12 October 2026, the source member `Resonant_Lambert_Inverse_Transseries/article.tex` in `docs/incoming/Resonant_Lambert_Inverse_Transseries_2026-10-12.zip`. It is cited as `incoming` in `references.tex`. The inspected source paths and hashes are recorded separately in `provenance.json`.

## 1. Meaning of the contribution categories

| Category | Meaning in this package |
| --- | --- |
| Imported input | An established theorem or exact identity is used with attribution. This article does not claim a new proof of the imported analytic theorem. |
| Reproduced input | A result already present in the predecessor is rederived briefly so that the argument and conventions can be checked locally. |
| New proof or strengthening within the project | The article proves the predecessor's explicitly conjectural amplitudes or establishes additional uniform estimates and consequences. This classification makes no worldwide priority claim. |
| Generalization | The coefficient argument is extended under explicit additional input hypotheses, particularly to a finite set of equal-modulus phases. |
| Application of established analytic machinery | The article verifies a concrete change of coordinates and every required closure hypothesis, then applies the cited nonlinear resurgence and summability theorems. |
| Computational evidence | Executed exact finite checks or floating-point diagnostics support implementation consistency. They are not dependencies of the infinite analytic or asymptotic theorems. |
| Open problem or heuristic | A suggested extension is stated as a research question. It is not available as a lemma or an integration claim. |

The precise contribution is a resolved project conjecture, a first inverse-index correction with uniform errors, a finite-phase leading transformation law, explicit Borel boundary models, a checked application of nonlinear continuation and summability closure, and a uniform leading Stokes-transport estimate. The factorial endpoint mechanism has antecedents, including Bender–Richmond and Borinsky; the nonlinear closure theorems are Sauzin's. The article does not claim that these general mechanisms originate here.

## 2. Variables, normalizations, and limits

The forward formal remainder and the inverse are

\[
R(t)=\sum_{n\ge1}r_nt^n,
\qquad
V(q,u)+\frac u2V(q,u)^2+uR(qe^{-V(q,u)})=0,
\qquad
V(q,u)=\sum_{n\ge1}C_n(u)q^n.
\]

The article uses

\[
A=4\pi^2,\qquad c=A/4,\qquad d=A^2/288,\qquad
b_n=\Gamma(n)/n.
\]

The constant `d` without an argument is distinct from the divisor function `d(m)`. The full remainder includes `r_1=-1/4`; the predecessor's calligraphic degree-two remainder excludes this term. Its inclusion is essential to the shifted action amplitudes.

The three limits used in the article have different scopes:

| Limit or construction | Scope actually proved |
| --- | --- |
| Formal inverse | `q` and `u` are independent variables. Each `C_n` is an exact polynomial. No convergent evaluation of `R` is needed. |
| Late coefficients | `n` tends to infinity, uniformly on every fixed complex disk `|u|≤U`. The constants may depend on `U`; the theorem gives no growing-`U` estimate. |
| Relative coefficient asymptotics | Uniform for real `0<u≤U`, with no positive lower bound on `u`. Relative estimates at general complex parameters require nonvanishing of the relevant amplitude. |
| Borel continuation and directional summation | A complex `u` is fixed. The continuation and summability theorems do not state uniform bounds over unbounded parameter sets or arbitrary families of continuation paths. |
| Leading Stokes transport | Real `q→0+`, uniformly for real `0<u≤U`; the permitted upper bound on `q` may depend on `U`. |
| Physical inverse | `u=1/X`, `q=exp(γ−X)`, `X→+∞`, as specified in `eq:physical`. The coefficient index `n` remains a different variable. |

## 3. Imported and reproduced inputs

| Stable label or equation | Claim and status | Dependencies and limits |
| --- | --- | --- |
| `eq:F`, `eq:mellin`, `eq:r-residue`, `eq:forward-asym`, `eq:R` | The divisor Lambert representation, its Mellin expression, and its finite-order asymptotic expansion are established forward input. The article recalls the residue calculation and reflected coefficient formula. | Uses the standard Gamma and zeta identities and the predecessor. At every prescribed finite order the expansion is asymptotic on the stated smaller sectors. It is not a convergent power series at the origin. |
| `prop:lagrange` | **Reproduced input:** formal existence and uniqueness, and the exact finite Lagrange formula `eq:C-finite` with the polynomial `T_{n,k}` in `eq:T`. | A direct auxiliary-variable Lagrange calculation is included. Only `k≤n` contributes to the coefficient of `q^n`, so the auxiliary-variable specialization is coefficientwise legitimate. The result is exact for every positive integer `n`. |
| `prop:structure` | **Reproduced input:** alternating coefficientwise signs, degree `2n−1`, the Catalan top coefficient, and valuation one for even indices and valuation two for odd indices at least three. | Derived from `prop:lagrange` and the forward parity support. Includes the exact identity `[u²]C_n=n r_{n−1}/4` for odd `n≥3`. These valuations are used in the uniform estimates as `u→0`. |
| `prop:forward-Borel` | **Reproduced forward expression with a direct continuation proof:** the logarithmic divisor lattice in `eq:R-Borel-lattice`. | Uses the reflected forward coefficients and `Σ d(m)m^(−s)=ζ(s)²`. A convergent `d(m)/m²` majorant proves normal convergence of the remote terms along compact lifted paths; only finitely many logarithms acquire nontrivial monodromy. |
| `prop:Sauzin-input` | **Imported theorem:** nonlinear substitution, composition, and inverse closure for resurgent series and their directionally summable counterparts. | Sauzin, *Nonlinear analysis with resurgent functions*, Theorems 3 and 5 and their summable versions 3′ and 5′, cited as `Sauzin2015`. The required set is closed, discrete, contains zero, and is stable under addition. These hypotheses hold for `Ω=Aℤ`. No new proof of Sauzin's convolution estimates is asserted. |
| `eq:exact-lateral-input` | **Imported exact analytic identity:** `R_±=R_ex±J/2`, where `J(t)=4πi Σ d(m)E_1(Am/t)`. | The identification of the real arithmetic mean with `R_ex` is the predecessor's Mellin–Voronoi completion theorem, Section 5. It is not inferred solely from the formal expansion. The upper-minus-lower sign is independently checked from the logarithmic kernel. |

The predecessor already contains analytic transport of its exact forward jump through inversion. Accordingly, the present Stokes section contributes a proved uniform leading estimate with its finite amplitude shift; it does not claim invention of the exact transport principle.

## 4. Coefficient theorems and their dependency chain

All labels in this section refer to `01_setting.tex`, `02_coefficients.tex`, or `03_first_correction.tex`.

| Stable theorem label | Claim and contribution status | Essential dependencies and precise scope |
| --- | --- | --- |
| `lem:factorial` | **Proved here:** factorial convolution and ratio bounds preserving the large endpoint. | In particular, `(b*b)_n≤3b_(n−1)`, `S_(n,k)≤K^k 3^(k−1)b_(n−k+1)`, and `n^(k−1)b_(n−k+1)/b_n≤k e^k`, with the ranges stated in the lemma. The proof is a finite reciprocal-binomial argument. It does not use numerical testing. |
| `lem:endpoint` | **Proved here:** extraction of the configurations with one large index and all other indices equal to one, with a quantitative interior remainder. | Uses `lem:factorial`. Together with the bound for `T_(n,k)`, it yields a summable bound proportional to `k B_U^k/k!` in `eq:master-majorant`. This uniform majorant is the justification for summing endpoint asymptotics over all `k`. |
| `thm:leading-rate` | **New proof of the source conjecture, with stronger scope:** the hyperbolic even and odd amplitudes and an `O_U(1/n)` normalized error. | Uses `prop:lagrange`, `prop:structure`, `lem:factorial`, and `lem:endpoint`. Fixed-`k` limits alone are not the proof: the factorial majorant and quantitative ratio errors justify the full sum. Uniform on compact complex parameter disks, with the parity-sensitive improvement needed for a real relative statement down to `u=0`. |
| `cor:moving-u` | **New uniform consequence:** `n→∞` and positive `u_n→0` may be taken together at any speed. | Follows from the real relative estimates in `thm:leading-rate`. It gives `C_n∼−4u_n b_n A^(−n)` at even indices and `C_n∼A u_n² b_n A^(−n)` at odd indices. No restriction such as `u_n n→∞` is imposed. It does not justify ordinary summation or optimal truncation of the sector series. |
| `lem:second-endpoint` | **Proved here:** the next endpoint configuration, containing one additional index of size two, and a uniform remainder. | Uses the shifted coefficients `α_j=a_(j+1)`, with `α_0=c` and `α_1=d`, a Gamma convolution bound, and an interior reciprocal-binomial estimate. For `n≥12` and `1≤k≤n/2`, the displayed two-endpoint expression has remainder `O(B_*^k Γ(n−k−2))`. The constant is independent of `n,k`. |
| `thm:main` | **New strengthening:** an explicit first inverse-index correction and an `O_U(n^(−2))` normalized error. | The proof in Section `sec:correction` combines `lem:second-endpoint`, uniform expansions of the Gamma ratios and `T_(n,k)`, and a factorially summable error. The omitted range `k>n/2` is bounded to every fixed inverse-index order by `eq:master-majorant` and factorial moments. The theorem is an infinite asymptotic result independent of the verification program. |
| `cor:relative-two-term` | **New consequence:** two-term relative asymptotics uniformly for real `0<u≤U`. | Uses `thm:main`, `cosh(cu)≥1`, and `sinh(cu)≥cu`. The improved odd remainder follows from the exact vanishing at `u=0` and a complex-disk maximum-modulus estimate. It is not obtained by dividing an unqualified absolute bound by a small odd amplitude. |
| `thm:finite-phases` | **Proved generalization:** a leading transformation law for finitely many equal-modulus phases. | Assumes `eq:phase-input`: an absolute factorial majorant and `A^n r̃_n/b_n=Σ κ_ω ω^n+O(1/n)`, with a finite set of distinct unit phases and `r̃_1=ρ`. It uses the same finite Lagrange formula and absolute-value endpoint estimates; positivity is unnecessary. The output is an additive, locally uniform expansion with amplitude multiplier `exp(Aρu/ω)`. |
| `cor:prefix` | **Proved specialization:** a polynomial change of the forward tail changes the leading amplitudes only through its linear coefficient. | Apply `thm:finite-phases` to `R+P`, with fixed polynomial `P(0)=0`. The condition preserving the original leading amplitudes is `P(t)=O(t²)`, not merely `deg P≥2`. The statement gives leading additive asymptotics; it does not transfer every original parity valuation or the first-correction formula to an arbitrary perturbation. |

### The exact strength of `thm:main`

With `ε=n mod 2`, `z=cu`, `H_0(z)=cosh z`, and `H_1(z)=sinh z`, the theorem proves

\[
Z_n(u):=\frac{(-1)^{n+1}A^n C_n(u)}{4u b_n}
=H_\epsilon(z)+\frac{K_\epsilon(u)}n+O_U(n^{-2}),
\]

\[
K_\epsilon(u)
=\left(du+\frac{1+u}{2}z^2\right)H_\epsilon(z)
 +(2+u)zH_\epsilon'(z).
\]

The quotient defining `Z_n` has a removable value at `u=0`. For odd `n`, the normalized remainder is `O_U(|u|/n²)`. Consequently, before normalization the even error is `O_U(|u|b_n A^(−n)/n²)` and the odd error is `O_U(|u|²b_n A^(−n)/n²)`.

The relative formulation is

\[
\frac{Z_n(u)}{H_\epsilon(cu)}
=1+\frac{K_\epsilon(u)}{nH_\epsilon(cu)}+O_U(n^{-2}),
\qquad 0<u\le U.
\]

At complex zeros of a parity amplitude, the additive theorem remains valid but this relative quotient need not be defined. This does not imply disappearance of either individual Borel action.

The finite-phase theorem has the same distinction. Its leading phase sum can cancel at selected parameters or on subsequences; a relative equivalent requires a separate nonvanishing estimate. The theorem neither identifies a full Borel continuation surface for an arbitrary finite-phase input nor asserts that every polynomial perturbation preserves the exact odd valuation.

## 5. Boundary regularity, continuation, and summability are separate results

All labels in this section refer to `04_borel_and_continuation.tex`, except the preview in `01_setting.tex`.

| Stable theorem label | Claim and contribution status | Dependencies and scope |
| --- | --- | --- |
| `thm:Borel-models` | **New coefficient consequence:** the explicit logarithmic model `B_(0,u)` has a continuous closed-disk remainder; the logarithmic–dilogarithmic model `B_(1,u)` has a remainder whose complex derivative also extends continuously to the closed disk. | Uses `thm:main` and absolutely convergent model series. Residual Borel coefficients are respectively `O_U(|u|A^(−n)n^(−2))` and `O_U(|u|A^(−n)n^(−3))`. The series and asserted extensions are locally uniform in `u`. No continuation theorem is used in this deduction. |
| `thm:Borel-models`, endpoint conclusion | **New strengthening of the source radius result:** both `+A` and `−A` are genuine singularities for every fixed complex `u≠0`, and the Taylor radius is exactly `A`. | The radial logarithmic coefficients are `(2u/A)e^(−cu)` and `−(2u/A)e^(cu)`, neither zero for `u≠0`. A continuous remainder cannot cancel their logarithmic divergence. For `u=0`, the transform is identically zero and the radius conclusion is inapplicable. |
| `eq:radial-refinement` | **Proved further consequence:** the `ε log ε` radial term, with an `O_u(ε)` remainder as the endpoint is approached radially from inside the disk. | Uses the bounded derivative of the second boundary remainder and the elementary expansion of `Li_2(1−ε)`. The constants `L_σ(u)` are finite boundary constants; the article does not give a closed formula for them. |
| `thm:inverse-continuation` | **New application of established nonlinear resurgence closure:** the Borel germ of the inverse continues along paths starting at zero and thereafter avoiding `Aℤ`. | Uses `prop:forward-Borel`, `prop:Sauzin-input`, and the proved coordinate reduction `h(t)=(sqrt(1−2u²R(t))−1)/u`, `G(x)=x exp(−h(1/x))`, `T=G^(−1)`. Multiplication by `x` is checked by its Borel action, differentiation; the final composition gives the original implicit inverse by formal uniqueness. Fixed complex `u`, including the trivial case `u=0`. |
| `lem:kernel-growth` | **Directly proved analytic estimate:** the principal forward Borel kernel is bounded by `M_δ(1+log²(2+|ξ|))` on each closed angular region a positive distance from the real rays. | Uses the elementary divisor summatory bound and a split of the logarithmic lattice into head and tail. This is a principal-branch estimate on the specified angular domains, not a universal growth estimate on every continuation sheet. |
| `thm:inverse-summability` | **New application of summable closure:** `V` is 1-summable in every direction outside `πℤ`; its sum is the unique `O(q)` solution of the summed implicit equation on sufficiently small common sectors. | Uses `prop:forward-Borel`, `lem:kernel-growth`, and the summable counterparts in `prop:Sauzin-input`. The multiplication-by-`x` step is checked with Cauchy estimates on narrower angular domains. Summation commutes with the concrete substitutions and inverse operation. A local contraction supplies uniqueness. |
| `thm:analytic-preview` | **Summary theorem, not an additional independent input:** exact radius, two genuine nearest actions, lattice continuation, and nonreal directional 1-summability. | Its separate proofs are `thm:Borel-models`, `thm:inverse-continuation`, and `thm:inverse-summability`. None of these is justified by assuming the preview. |

### What the analytic conclusions do and do not determine

The boundary remainders are holomorphic in the open disk. The first extends continuously to its closure; the second and its complex derivative extend continuously to the closure. These are statements about regularity from inside the disk. They do not claim holomorphic extension of those remainders across `±A`, a full logarithmic singular germ, or a complete local discontinuity formula.

The continuation theorem supplies the allowed obstruction set `Aℤ`. It does not assert that every lattice point is active, or active on every sheet. Zero is included deliberately: after logarithmic monodromy the forward kernel can acquire a multiple of `1/ξ`, although its original germ is regular at zero. The theorem does not require continuation through zero after such a loop.

Directional 1-summability requires exponential growth control in addition to continuation. The article proves the requisite forward bound on nonreal angular domains and applies the summable closure theorem. It does not infer 1-summability from continuation alone. Nor does it identify the Borel–Laplace sum with an ordinary sum of the divergent `q` series. Fixed complex `u≠0` has factorial late coefficients and a zero ordinary convergence radius for that series.

## 6. Exact Stokes input and the independently proved transport estimate

The stable result is `prop:Stokes-transport` in `05_computation_and_research.tex`.

**Imported input.** Equation `eq:exact-lateral-input` is the predecessor's exact completion identity, with the article's full-remainder convention. The exponential-integral expression for the forward jump and the analytic principle of inverse transport are established source material. The article rechecks the branch sign and proves the elementary estimates `eq:J-leading` and `eq:J-derivative` from that input.

**Proved estimate.** For real `q→0+`, uniformly for real `0<u≤U`, let `V_0` solve the exact real inverse equation and let `V_±` use the two lateral inputs. Put

\[
t_0=qe^{-V_0},\qquad
D=1+uV_0-ut_0R_{\mathrm{ex}}'(t_0).
\]

The proposition proves

\[
V_+-V_-=-\frac{uJ(t_0)}{D}
 +O_U\!\left(u^2q e^{-2A/q}\right)
=-\frac{4\pi i}{A}u q
 e^{-A/q-Au/4}\{1+O_U(q)\}.
\]

The first error is an absolute bound retaining the square of the exponential and the displayed power of `u`. The final error is relative and uniform down to `u=0` within the positive interval.

**Proof dependencies.** Finite Mellin asymptotics and differentiated remainder bounds give `R_ex(t)=−t/4+O(t²)`, `R_ex'(t)=−1/4+O(t)`, and `R_ex''(t)=O(1)` on smaller sectors near the positive ray. A local contraction gives `V_0=uq/4+O_U(uq²)` and the exponentially close lateral solutions. Taylor estimates on a small complex neighborhood control the variation of `J(qe^(−v))` without losing the exponential factor. Finally,

\[
\frac{A}{t_0}=\frac{A}{q}+\frac{Au}{4}+O_U(q)
\]

explains the finite amplitude shift. With the physical specialization, equation `eq:physical-jump` follows:

\[
t_+-t_-=
\frac{i}{\pi}\frac{q^2}{X}
\exp\left(-\frac{A}{q}-\frac{A}{4X}\right)\{1+O(q)\}.
\]

This transport proof does not rely on inferring a complete jump from a continuous Borel boundary remainder. Its agreement with the coefficient of the positive-action logarithm is a consistency check between two proved calculations. The article also does not identify the arithmetic mean of nonlinear lateral inverses with a nonlinear median summation operation.

## 7. Executed verification and its evidential limits

The executable source is `verification/verify.py`. The records are `exact_results.json`, `results.json`, `run.txt`, `diagnostics.csv`, `coefficients_exact.txt`, and the two plot artifacts in the same directory. These records are evidence about this implementation; the proofs above do not assume their success.

| Verification class | Executed coverage | What this establishes |
| --- | --- | --- |
| Exact formal identities | `C_1,…,C_12` constructed over `ℚ[u]` by finite Lagrange inversion and by an independent implicit recursion; substitution residual zero through `q^12`. | Exact agreement at the recorded finite orders. Structural sign, valuation, degree, Catalan coefficient, and lowest-coefficient identities are checked there. |
| Exact finite inequalities | Two-factor and interior factorial inequalities through `n=100`; all ratio pairs `1≤k≤n≤100`; convolution powers through `n=32`. | The ratio check uses the rational consequence `n^(k−1)b_(n−k+1)/b_n≤k3^k`. The sharper `ke^k` estimate is proved in `lem:factorial`; it is not the exact numerical comparison used by the script. |
| Exact first-correction algebra | Twelve endpoint/inner-factor expansions and both hyperbolic parity sums. | Finite symbolic algebra checks agree with the analytic formula. The complete executed run reports **5,890 exact assertions**. |
| Main numerical coefficient evaluation | Seventy fixed diagnostic cases with indices through `1025`, including even and odd subsequences, real and complex parameters, and a positive parameter tending to zero. Every `1≤k≤n` finite Lagrange summand is included. | Complete finite-sum diagnostics, without a mathematical truncation of those main coefficient sums. Arithmetic remains floating point. |
| Independent higher precision | An independent 80-decimal-digit `mpmath` route checks the recorded indices; exact polynomial evaluation supplies a further low-order comparison. | The recorded maximum relative-or-absolute discrepancy with the main route is approximately `2.36×10^(−19)`; exact-polynomial/high-precision agreement is approximately `4.68×10^(−81)`. These are observed discrepancies, not certified roundoff enclosures. |
| Secondary large-index precision check | Separate binary64 convolution at the recorded larger indices, truncated at `k=256`, compared with the complete main evaluation. | The maximum observed discrepancy is below `3.12×10^(−16)`. An exact rational omitted-term certificate is below `2.861×10^(−18)` for `D_n/(4b_n)` and `|u|≤1/2`. That certificate bounds the omitted tail only; it does not bound floating-point error. |

The main run records a 64-bit-significand, extended-range `longdouble` and rejects an ordinary-binary64 alias. Package versions and the fixed parameter grid are in `results.json`. No fitting or random sampling is used. The plots illustrate first- and second-order decay on the tested grid. They do not prove a uniform asymptotic theorem, Borel continuation, or a Stokes identity. No interval certification is claimed.

## 8. Explicitly open claims

Section `sec:research` proposes the following extensions. None is asserted as proved in this package.

1. **All inverse-index orders.** An expansion through every fixed power of `1/n`, with a uniform remainder and a recurrence for its coefficient functions, is open here. Only the leading term and first correction are proved. The proposed higher polylogarithmic boundary models and `C^(N−1)` remainders are conditional consequences of such an all-orders coefficient theorem.

2. **A full paired-action or finite-phase asymptotic calculus.** `thm:finite-phases` establishes a leading transformation law. It is not an all-orders composition/inversion or alien-derivative calculus. Any use of a single-action factorial asymptotic theorem for simultaneous actions `A` and `−A` needs a justified extension or separate proof.

3. **The active arithmetic lattice.** Continuation is proved away from `Aℤ`, and the two principal-boundary points `±A` are active for `u≠0`. Activity, local structure, and cancellation at `±2A,±3A,…` on specified sheets remain open.

4. **Complete local singularities and Stokes operators.** A convergent logarithmic minor, an explicitly resurgent local germ, all-order discontinuity formulas, alien derivatives, and a global simple-resurgence classification have not been proved. Boundary `C¹` control and permitted continuation paths do not by themselves provide these statements.

5. **Growing slow parameters.** The article gives compact-parameter uniformity. It does not prove uniform asymptotics for `|u|→∞`. For positive real `u`, the relative first correction suggests a possible transition near `u≈n^(1/3)`; this is a scaling heuristic to be tested by a new analysis.

6. **Optimal truncation of the actual inverse.** The late coefficients suggest an action-controlled truncation scale near `n≈A/|q|`. A sharp remainder for the sectorially summed or exact physical inverse, together with uniform Stokes-neighborhood or terminant estimates, remains open. Coefficient estimates alone do not establish that remainder.

7. **Order displacement and resonant jets.** The predecessor already proves parameter-jet identities and forward odd-sector activation. The proposed new task is to control the late nonlinear inverse coefficients and their competing mechanisms uniformly as the order displacement and logarithmic core scale vary. This package supplies no such displaced-order uniform theorem.

8. **Proof-assistant and interval verification.** The finite algebraic identities and convolution estimates are candidates for future formalization. No Lean, Isabelle, Coq, or other proof-assistant proof is supplied, and the floating-point diagnostics are not interval proofs.

## 9. Integration and audit boundaries

The supported status changes are concrete: the predecessor's labels `eq:conj-even` and `eq:conj-odd` can be promoted from conjectures by citing `thm:main`; its continuation question can cite `thm:inverse-continuation` together with Sauzin's original theorem; its Borel statement can be sharpened by `thm:Borel-models`. The first correction, finite-phase theorem, and uniform Stokes estimate can be integrated as separately scoped results.

No false theorem was established in the scoped source audit. The predecessor explicitly described the hyperbolic amplitudes as conjectural, and its coarser bounds served their stated purpose. This package resolves and strengthens those statements; it does not retroactively describe a conjecture as an erroneous proof. The audit does not certify every file in the Polylogarithms, Transseries, or incoming directories.

The contribution is supported by a repository comparison and a targeted primary-source literature review. It makes no exhaustive global priority claim. Its proof status is mathematical prose plus executable finite verification, with the imported analytic inputs and the remaining open problems identified above.
