# Prior GRH transfer reports: inventory, claim boundaries, and non-redundant work

Reviewed 25 November 2026 (Pacific date). All six archives currently in `ProveIt/docs/incoming` were located locally and their identities are known. The root verified five archives against GitHub; I independently verified the sixth. This is a review of mathematical arguments and evidence reported in the files, not an independent rerun of their full computations or Lean proofs.

## 1. Exact archive inventory

| Archive | Git blob SHA | Local source |
| --- | --- | --- |
| `grh_transfer_analysis.zip` | `68caedfbe84e88899ec097e2e1a7b92ae7657bd5` | `/workspace/scratch/8ed95454a998/sources/prior/grh_transfer_analysis/grh_transfer_analysis/report/grh_transfer_analysis.tex` |
| `grh_transfer_analysis_2026-11-25.zip` | `2ec837a7b74075f98caa840b11ed467dd3e11509` | `/workspace/scratch/8ed95454a998/sources/prior/grh_transfer_analysis_2026-11-25/grh_transfer_report/report.tex` |
| `grh_lean_transfer_analysis.zip` | `b0f01e2ea825a07e7a711d4b7059f0fd3421f816` | `/workspace/scratch/0433c2266c67/output/grh_lean_transfer_analysis.zip`; read `.tex` directly from ZIP without extracting |
| `grh-transfer.zip` | `e8cba45276d211569726bc45eb24fee0d467b9a0` | `/workspace/scratch/8ed95454a998/sources/prior/grh-transfer/grh-transfer/report.tex` |
| `grh_transfers.zip` | `10ba8d2ac5e04809d70c468bc79ecdae31dedd19` | `/workspace/scratch/8ed95454a998/sources/prior/grh_transfers/grh_transfers/grh_transfers.tex` |
| `grh-lean-transfers.zip` | `ecce11d7f5d919b3c5fed4e310a0ac56ebc0b456` | `/workspace/scratch/8ed95454a998/sources/prior/grh-lean-transfers/grh-transfers/report.tex` plus nine included sections |

The sixth archive is exactly 846,790 bytes; hashing `blob 846790\0` followed by its bytes gives the Git blob SHA above. All reports inspect source commit `72fead102f663d5c7a407964a13dc0cf9d977207`, with Lean 4.35.0 and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.

## 2. What the earlier reports already establish or attempt

### A. `grh_transfer_analysis.zip`: foundational review and cubic target

This report explicitly says that it does **not** solve a new open problem beyond known Dirichlet-GRH consequences. Its substantial content is:

1. Exact public endpoint scope: arbitrary positive modulus, including imprimitive characters; RH and Dirichlet GRH, not arbitrary Hecke or Artin GRH.
2. Explicit Vinogradov consequence from Lamzouri–Li–Soundararajan: least quadratic nonresidue `n(p) < (log p)^2` for primes `p >= 5`. This is a published implication, not method transfer.
3. Abelian Dedekind RH by primitive Dirichlet factorization.
4. Determinant amplification certificate. Given `theta D <= n <= D`, `M,B,I >= 0`, `V <= n(M-mR+A)`, `delta <= DI`, and `D(M-B) <= V+2delta`, it proves
   `R <= [A+(B+2I)/theta]/m`.
   An additional completion cost `(D-n)K` is incorporated with a rank-defect fraction `eta`.
5. One-sided Landau pole exclusion: if a real remainder has an eventual upper bound `C exp((beta-1)v)`, a meromorphic Laplace transform with simple poles, and nonnegative residues at real points greater than `beta`, then the transform is holomorphic to the right of `beta`. The report correctly calls this a classical mechanism, not a new analytic theorem.
6. Cubic field `Q(theta)`, `theta^3-theta-1=0`, quadratic field `K=Q(sqrt(-23))`, and Hilbert class field `H`. The class group is `C3`, the splitting field has `S3` group, and
   `zeta_H = zeta_K L_K(psi)^2`, `zeta_F = zeta L_K(psi)`.
7. Principal ideal-power selector
   `-zeta_H'/zeta_H = 3 sum_[a]=1 Lambda_K(a) N(a)^(-s)`.
   A one-sided square-root bound for its correctly centered ramp smoothing would give RH for the nonabelian cubic and its splitting field. The required arithmetic estimate is **not proved**.

It reports seven elementary transfer lemmas independently compiled against the pinned Lean and Mathlib. This does not extend kernel verification to the cubic analytic target or to the entire report. In contrast, most other archives label their new Lean interfaces uncompiled.

### B. `grh_transfer_analysis_2026-11-25.zip`: sparse witnesses and K-theory cautions

Adds to the preceding architecture:

- A sufficiently populous successful twist family is enough. For fixed `1/2 < beta < 1`, let `eta=(beta-1/2)/18`. If the good arithmetic parameters `S` satisfy `limsup S(X)/X^(1-eta)=infinity` and each fixed `d in S` has its own eventual one-sided bound, then the source's bad-twist count finds a good witness for every proposed zero. No uniform bound in `d` for constants or thresholds is needed. Divergence of `sum_(d in S) (log d)/d` suffices.
- A positive `S3` coefficient system and exact cubic transfer criterion (again conditional on a new arithmetic bound).
- A careful audit of attempts to infer Vandiver or algebraic K-group vanishing from the shortened source. `shaOdd` is a custom cocycle model; the file expressly supplies no comparison with the usual Tate–Shafarevich group. Even-class orders are removed from one denominator estimate, rather than shown to vanish.
- An explicit obstruction to inserting a nonzero pure Tate-twist lattice into the generic Selmer twisting theorem: required inertia away from `ell` acts by a scalar `zeta_*` with `zeta_*^2-1` a unit, whereas a pure Tate twist is unramified there and has scalar 1.
- The elementary “products before gcds” certificate: pointwise witnesses `forall q exists j, ell | A[q,j]` are encoded by `ell | gcd_q prod_j A[q,j]`, not by elimination of each fixed branch separately. The example branch vectors `(2,3)` and `(3,2)` demonstrates the quantifier error.
- Records follow-on claims by Pintar through degree 104 (conditional on an original-source arithmetic construction) and Mok–Zheng through degree 120 (claimed unconditional, but modified Lean entry point not fully rebuilt). These are existing claims requiring fresh source verification, not discoveries of a new report. URLs in the bibliography are `https://hexagonmath.org/2611.00829v3` and `https://hexagonmath.org/2611.00998v1`.

### C. `grh_lean_transfer_analysis.zip`: consolidated architecture, not a new extension

This sixth archive repeats the determinant certificate, near-full spanning cost, sparse successful-family theorem, and the cubic principal-ideal target. Its useful sharpenings are explicit interfaces and four arithmetic gates:

1. A local determinant/divisibility formula sensitive to the principal ideal class, including powers of nonprincipal prime ideals.
2. Almost full spanning with controlled completion cost.
3. Exact archimedean centering: the Euler–Kronecker constant must be reproduced. An unspecified `O(1)` cannot be absorbed into an error tending to zero.
4. Loss bookkeeping that retains `x^(-1/2+o(1))` after division by the chain length.

It explicitly observes that the `S3` splitting field is totally imaginary but not CM: complex conjugation is not central. One cannot replace the source's CM field by this splitting field and keep the same unitary construction.

Its denominator-budget comparison is valuable: the loss/budget ratio is of order `m^2/[x (log b)^2]`. Thus `m ~ sqrt(x)` is quantitatively compatible with the present estimates; simply lengthening the chain does not improve RH into stronger distribution statements.

### D. `grh-transfer.zip`: substantial applications and general split-prime criteria

This report is much more than a generic list of consequences:

- Claims an exact classification of the 229 abelian extensions of `Q` for which the positive zero sum `B_K=sum_rho 1/(1/4+gamma^2)` is below 2. Counts: 1 rational, 168 quadratic, 7 cyclic cubic, 38 biquadratic, 9 cyclic quartic, 1 cyclic quintic, 4 cyclic sextic, and 1 with group `C2 x C4`. This is presented as a partial answer to Zhao's classification question, with interval computations and exact group enumeration. It is a sufficient sign condition, not a classification of all fields having eventual positive mean.
- Under a field's own RH, `B_K<2` forces degree at most 8 and discriminant below 193,000,000. This is not an unconditional nonabelian classification supplied by Dirichlet GRH.
- For every sufficiently large integer `n`, many strictly ordered solutions to `n=xy+yz+zx` have prime pair sum `x+y` of order `log^2 n`; provides an algorithm polynomial in bit length, a simultaneous version for finitely many `n_i`, and a lower obstruction of order `log n log log n` on infinitely many prime inputs. These still depend on quadratic Dirichlet GRH via existing smoothed character-sum estimates.
- General Galois-field criterion: for the correctly centered ramp sum `R_M(x)` over rational primes splitting completely in a finite Galois extension `M/Q`, RH for `zeta_M` is equivalent to an eventual one-sided bound `R_M(x) <= C x^(-1/2)`; bounds with every positive epsilon also suffice.
- A constant-free dyadic formulation detects primes for which `X^ell-2` is irreducible modulo `p`, for every odd prime `ell`. It is equivalent to RH for `Q(zeta_ell,2^(1/ell))`, not a proof of that RH. It already identifies why fixed congruences cannot distinguish identity from nonidentity translations in the affine Galois group.
- Exact upper endpoint under field RH:
  `limsup sqrt(x) R_M(x) = 2 b_M + B_M/[M:Q]`,
  where `b_M = #{g in G: g^2=1}/|G|`, including the identity. If field RH fails, the limsup is positive infinity. No linear-independence assumption on zeros is needed for the upper endpoint, because simultaneous approximation can align finitely many zero phases at 1.
- A `riemann95` nonhalting consequence, via a separate correctness theorem; no joint Lean build claimed.

Do not reproduce the general split-prime criterion or exact endpoint as a new finding of the current report.

### E. `grh_transfers.zip`: exponent six and fixed-window prime races

Main precise partial classification: all imaginary quadratic fields of exact class-group exponent 6 for which either `omega(|D|)<=6` or `|D|/P^+(|D|)<=10^8` occur in the Elsenhans–Klüner–Nicolae list. The first class has 429 examples; the union contains all 432 known examples. An omitted example must have at least seven prime divisors and cofactor above `10^8`. The report gives bounds `|D|<2.1e22` for exactly seven prime factors and `<2.2e24` for eight. This is a genus-field/least-split-prime argument with explicit constants and a published large census.

For the cubic `X^3-X-1`, let `b(p)=#roots mod p -1`, `B(y)=sum_(p<=y,p!=23) b(p)log p`, and `J_h(x)=-int_x^(hx) B(y)/y^2 dy`. The report proves equivalence between RH for its standard Artin factor and eventual nonnegativity of `J_4`. Under RH it gives
`liminf sqrt(x) J_4(x) >= 1-9/(pi sqrt(23)) > 0.4026`.
The corresponding modulo-four race is proved positive for every real `x>3/4`, and zero on `0<x<=3/4`, with a finite interval certificate.

The same report proves a general variance/zero-free-band bound for entire Mellin transforms of positive eta products. If `F(y)=prod_j eta(i d_j y)^(r_j)`, then with
`c=(pi/12) inf_y sum_j r_j max(d_j y,(d_j y)^(-1))`,
one has `(log M)''(sigma)<=1/c` and no zeros for `|Im s| <= (pi/2)sqrt(c)`. It applies this to the level-23 eta product and explicitly disclaims optimality and priority.

It already proves an exact mean-square obstruction for approximating the cubic trace by a fixed periodic weight: the best approximation is zero, with residual squared mean 1. Hence this `S3` result should not be advertised as new again.

### F. `grh-lean-transfers.zip`: CM coefficient fields and another cubic detector

Important claims not to duplicate:

- Finiteness, for fixed weight and coefficient degree, of coefficient fields of CM newforms even when level and nebentypus vary. The proof combines the GRH-dependent class-group exponent cutoff with earlier value-field results.
- For every even weight and trivial nebentypus, genus-field containment `G_E subset L=E K_f`, real genus subfield contained in `K_f`, and `2^(t-1) | [K_f:Q]` where `t=omega(D_E)`. Gives a non-computational explanation of Martin's class-number-two observation.
- Unconditional weight-two classification of all CM coefficient fields in degree 3 (18 fields), degree 5 (26 fields), and each odd prime degree at least 7. For prime `ell>=7` the claim is a bijection with imaginary quadratic fields of class number `ell`, using Dickson polynomials. Counts stated: 31 in degree 7, 41 in degree 11, 37 in degree 13.
- All-nebentypus exhaustiveness in odd degree uses existence of a real embedding and the even-weight real-coefficient restriction. Yang/González class-number divisibility is the decisive stronger input; the prime-degree classifications are largely independent of GRH and do not reuse the new theta-lift proof.
- A simultaneous weighted prime-race theorem in every quotient of a residue-class group, tracking central-zero multiplicities. Every nonsquare coset eventually leads the identity for a specified `log p/sqrt(p) * log(x/p)` weight. This is an explicit-formula deduction, with Suzuki attribution.
- For `Q(cuberoot(2))`, with splitting group `S3`, all class-function prime weights are decomposed into trivial, sign, and standard-character components. Any nonzero standard-character component gives a one-sided criterion equivalent to the missing cubic RH, after accounting for the Dirichlet components. Again it is a criterion, not the estimate.
- Exact fixed-congruence mean-square orthogonality for the standard `S3` trace.

Explicit future tasks already named there: classify quartic CM coefficient fields, derive the local discriminant formula at 5 for the quintic table, and produce a genuinely class-sensitive theta/divisibility estimate.

## 3. Conclusions for the current task

The user specifically excludes well-known consequences. A new report should therefore not lead with least nonresidues, abelian Dedekind RH, Grosswald, Euclidean fields, idoneal numbers, or the de Bruijn–Newman constant. They have already been covered repeatedly. CM classifications are potentially interesting prior achievements, but largely follow older CM algebra rather than the new proof's arithmetic mechanism.

The strongest unresolved bridge across the prior reports is still the local arithmetic detector, with precise square-root loss control, for an ideal-class or nonabelian Frobenius weight. The analytic endpoint is already in hand in several stronger formulations. Re-proving Landau, centering, or cubic factorization alone will not constitute progress toward resolving that target.

For the K-theory direction, the correct immediate deliverable is a standalone comparison theorem between ordinary strict Selmer groups and the actual cocycle models, with the quantifiers of automorphic witnesses explicit. Extending determinant computations while leaving that bridge unproved is not a resolution.

I did not discover a decisive mathematical error in the proof portions reviewed. There are numerous explicit scope limits, however, which should be preserved: reported versus locally executed kernel checks; infinite classification versus finite check; ordinary Sha versus a model; even-class avoidance versus vanishing; fixed versus varying fields; individual Kummer fields versus the full uniform squarefree family needed for Artin's primitive-root theorem.

## 4. One modest generalization not stated at full generality in these reports

The prior `S3` congruence obstruction has a clean general form. Let `M/Q` be finite Galois with group `G`, and let `chi` be a nonlinear irreducible complex character of `G`. For every fixed modulus `q` and complex function `a` on the units modulo `q`, Chebotarev gives

`lim_(X->infinity) (1/pi(X)) sum_(p<=X, p unramified and coprime q) |chi(Frob_p)-a(p mod q)|^2 = 1 + (1/phi(q)) sum_b |a(b)|^2`.

Proof: `E=M intersect Q(zeta_q)` is abelian over `Q`; hence `H=Gal(M/E)` is normal and contains `[G,G]`. For an irreducible representation `rho` affording `chi`, the average of `rho(h)` over `H` is projection onto its `H`-fixed space. That space is `G`-invariant, so it is zero or the whole representation. The latter would factor an irreducible representation of degree greater than one through an abelian group, which is impossible. Thus the mean character on each coset of `H` is zero. Chebotarev in the compositum gives zero correlation with every residue-class function; character orthogonality gives global second moment 1. Expanding the square proves the identity.

This generalization shows that no fixed family of Dirichlet weights even approximates a nonlinear irreducible Artin trace in prime mean square better than zero. It is a useful diagnostic lemma, not a claimed new open-conjecture solution or an independence theorem. It does not exclude varying moduli, correlations with extra arithmetic data, or a new geometric construction. It could be included as a clear additional theorem if the main report needs a non-redundant rigorous extension of the existing obstruction analysis.

## 5. Suggested follow-up ranked by connection to the proof method

1. Extract a class-sensitive local divisibility/height calculation for the `C3` ideal-class character over `Q(sqrt(-23))`; check its archimedean centering and losses before any claim about RH.
2. Extract the strict-Selmer-to-Hecke-witness bridge with pointwise quantifiers, then derive mathematically justified gcd/resultant certificates. This is the potentially strongest route to named non-RH conjectures, but it requires a comparison not present in the shortened source.
3. Develop quantitative determinant transfer with rank-defect, local loss and scale tradeoffs for a new family. Existing algebraic sandwich lemmas are already done; the real work is verifying new inputs.
4. If an explicitly solvable arithmetic side problem is desired, pursue the quartic CM coefficient-field classification or local discriminants of the prior quintic fields. This would build on prior reports, but the connection to the new GRH proof is indirect and should be described that way.
