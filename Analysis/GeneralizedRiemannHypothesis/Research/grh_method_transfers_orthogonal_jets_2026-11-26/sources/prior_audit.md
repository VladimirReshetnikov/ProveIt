# Prior GRH-transfer corpus audit

## Evidence and reproducibility

ProveIt was pinned to `9816644452bb42827167d6110e6d0322315a02b9` using `git ls-remote` on 26 November 2026. Its `docs/incoming` directory contains **52 GRH-related ZIP archives**, totaling **47,860,754 bytes**. Every archive was downloaded from a commit-pinned raw URL and its Git blob SHA-1 was independently recomputed from `blob LENGTH\0BYTES` and compared with the GitHub directory listing. All 52 matched. SHA-256 hashes are recorded too.

- `prior_manifest.json`: authoritative current identities and extracted-member paths.
- `prior_coverage.csv`: one row for each of the 52 archives, hashes, topic, and exact current review depth.

The comparison used 1,630 safely extracted text/code members, including 350 `.tex` files. Extraction excluded absolute and parent-traversal paths and selected a restricted set of text/code extensions. No supplied code was executed during this audit. The original ZIPs, temporary extracted trees, and download utility are not included in this deliverable; the manifest preserves their source identities and extracted-member inventory. Paths in that inventory describe the comparison workspace, not additional files bundled here.

This was **a complete inventory with targeted mathematical reading**, not a proof audit of all 52 archives. Most older topic descriptions in the CSV reuse the provenance-labeled inventory from the 26 November arithmetic report, whose bytes are still current. Current-session reading depth is separately recorded. No claim below independently certifies every earlier result.

## Coverage matrix

| Family | Strongest relevant prior reports | Already present | Remaining gap |
|---|---|---|---|
| Finite-field matrix probabilities | `grh_sharp_torsion_and_symplectic_blocks.zip`; `grh_beyond_dirichlet_2026-11-25.zip` | Positive-type Fourier estimate for frames; full rectangular matrix TV bounds; fixed-deficit isotropic symplectic limiting law; factorial kernel moments and rank tails for arbitrary positive-type weights | New group-specific geometry, simultaneous extreme-submatrix events, sharp finite laws beyond isotropic symplectic case. A simple rectangular rank-tail extension would duplicate prior work. |
| Lubin–Tate branch interpolation | `grh_transfers_cycle_signings_and_lubin_tate.zip` | Exact residue-field branch depth `1+sum q^v(b-c)`; optimized residue-field direction sets; exact finite-precision threshold expressed implicitly as pole order of `1/Delta_b`; universal finite-precision upper bound; two-branch valuation-one equality | Explicit multibranch cancellation and attainment classification at positive coefficient precision. The report explicitly asks this as a further research question. |
| Lubin–Tate coefficient depth | `grh_transfer_advances_2026-11-26.zip` | Exact valuation window for coefficients of powers of the formal logarithm; corrected finite `s0(n)` computations; old numerical algorithm's source erratum explained | General quantitative asymptotic for `s0(n)`, not merely finiteness or a single coefficient obstruction. |
| Cyclotomic and formal-group torsion selection | exact/fixed-field/sharp-torsion packets; graph-towers supplement | Exact shell minimax, fixed-field obstruction costs, ramified examples, formal-group extensions, positive tolerances and simultaneous determinants | Full effective classification over arbitrary ramified base and general positive tolerance may remain; small special cases require precise nonduplication check. |
| Signed graph spectra | `grh_transfers_cycle_signings_and_lubin_tate.zip`; `grh_transfer_advances_2026-11-26.zip` | Exact period-eight optimum for `C_(8m)(1,2)`; line rigidity; even-size certificates through 46; exceptional n=50 exact optimum and all minimizers | General incompatible-length family, all n, and structural classification of defect patterns. De Bruijn-style local-window closure is conceptually present although not named that way. |
| Geometric-progression densities | polynomial-density; density-gaps; `grh_ideal_densities_and_transfer_conditions_2026-11-26.zip` | Natural-versus-upper density gaps over integers, polynomial rings, ideals; computability/attainment; explicit improvements over greedy for integral-ideal ratios in every number field | McNew 7.2 exact rational-ratio natural optimum; comparison beta>alpha; natural-density improvement over greedy for fractional-ideal ratios. |
| Nonabelian zero criteria | A5/A6, Sylow, relative prime races, deficit, cyclic-generator, PSL2, reflection packets | Many explicit Frobenius-weight detectors and one-sided analytic equivalences; optimal character degree for PSL2; S3–S12 positive reflection identities | Actual new Frobenius-sensitive arithmetic inequality remains unproved. Rephrasing equivalent prime sums does not establish Artin RH. |
| Arithmetic Selmer transfer | structural, nonabelian, synthesis, ideal-density, arithmetic-transfers packets | Smith-length formula, anticyclotomic invariance, optimal integral frames, coefficient descent, one-precision reduction for strict odd cocycles, trace-congruence-depth identity under full matrix span | Uniform nonabelian Selmer/cocycle control, geometric realization, and the prime-sensitive determinant comparison. |
| CM sparse equations | CM four-term/sparse packets; sparse-singular-moduli; symmetric-power packet | Four/five-term classifications claimed; powered sextic family; Gaussian prime-conductor full-support lower density above 99.981826% | Original six-term classification; density-one full support. |
| Prime races and spectral inverse data | torsion-zero-data; exponent-seven; latest method-transfers | Signed zero-data recovery of arithmetic parameters; rational/torsion criteria; quantitative Suzuki sign-frequency bounds | No unconditional general LI/simplicity or nonabelian zero estimate; supplied spectral data require certified completeness/error bounds. |
| Class groups and arithmetic classifications | exponent-six/seven; Dirichlet GRH research; arithmetic packets | Full reported exponent-six and exponent-seven censuses; CM coefficient-field/isogeny/arithmetic consequences | These use Dirichlet GRH and external censuses; not automatically new internal-method transfers. |
| Finite rings, towers and combinatorics | graph-towers/finite-rings; latest method-transfers | Specific graph Iwasawa formulas; finite-ring progression constructions; balanced anticode instances and a small B3 minimum | General finite-ring classification, general tower algorithm, higher-dimensional anticode conjecture. |

## Exact nearest-predecessor passages

1. In `grh_transfers_cycle_signings_and_lubin_tate.zip`, member `grh_transfers/lubin_tate.tex` contains the complete branch theorem/proof. Its finite-precision proposition defines `t_b` by `X^t_b/Delta_b in (O/pi^r)[[X]]`, gives `t_b <= omega_b+(r-1)max(s_bc-1)`, and proves equality for two directions with valuation-one difference. The parent `report.tex`, final research question, asks which configurations with more than two branches attain the bound, explicitly noting highest-pole cancellation.
2. In `grh_beyond_dirichlet_2026-11-25.zip`, member `grh_beyond_dirichlet/sections/rank_moments.tex` was read in full. It already proves the arbitrary-weight rectangular factorial moment estimate and its minimum-over-moment tail certificate. It handles noninjective maps for the first moment and injective maps for frame moments. It gives a `GL_32(F_2)` example and a non-positive-type counterexample.
3. In `grh_sharp_torsion_and_symplectic_blocks.zip`, member `grh_sharp_transfers/symplectic.tex` was read in full. It already derives whole-matrix TV estimates and exact fixed-deficit isotropic symplectic limiting TV.
4. Latest `grh_arithmetic_transfers_2026-11-26.zip` already removes the rank factor from congruence-length estimates under full integral matrix span. A new trace-depth theorem with identical hypotheses would duplicate it.

## New local observation independently derived during this audit

For the standard Lubin–Tate coordinate `[pi](X)=pi X+X^q`, let `e=v_pi(p)`, coefficient precision `r>=1`, and suppose all pairwise differences of a finite direction set have valuation at most one. For a branch `b`, write `m_b` for the number of other directions congruent to `b mod pi`, and `s_b=d-1-m_b`. Formal-group difference identities give

`Delta_b = unit * X^s_b * [pi](X)^m_b`.

If `m_b>0`, put

`J=max { j>=0 : j + e*v_p(binomial(m_b+j-1,j)) < r }`.

Then the exact pole is

`t_b=s_b+q*m_b+(q-1)*J`.

This follows from the finite expansion of `(pi X+X^q)^(-m_b)` modulo `pi^r`; exponents for distinct j are distinct, so no further cancellation is possible after including the binomial coefficient valuation. For `m_b=0`, `t_b=d-1`. Example `q=p=3`, `d=3`, equidistant valuation-one directions, `r=3`: `J=1`, `t_b=8`, exact branch precision 9, whereas the older universal estimate allowed precision 11. The main report extends this observation to a broader attainment theorem.

This exact finite-precision multibranch statement was not found in the 350 extracted TeX members under searches for branch, pole, precision, binomial, cancellation and related terms. This is evidence of novelty relative to the reviewed corpus, not a literature priority proof.

## Primary-literature comparison for the branch result

- Laurent Berger and Johannes Sprang, [*Integer-valued polynomials and p-adic Fourier theory*](https://perso.ens-lyon.fr/laurent.berger/articles/POLINT.pdf), arXiv:2502.18053v2 (2025). Lemma 4.2 proves existence of a finite common cutoff by compactness over the residue field; Proposition 4.4 proves existence of coefficient-recovery functionals. Neither inspected statement gives the explicit multibranch precision/cancellation formula. Lemma 4.8 explicitly works in the coordinate `[pi](X)=pi X+X^q`.
- Manjul Bhargava, [*On P-orderings, rings of integer-valued polynomials, and ultrametric analysis*](https://doi.org/10.1090/S0894-0347-09-00638-9), JAMS 22 (2009), 963–993. The primary abstract describes explicit interpolation series and generalized factorials. This is foundational prior art, so neither valuation-based interpolation nor effective p-adic recovery should be claimed new in general. Full publisher PDF access was blocked during this search; no full theorem comparison was claimed.
- Uroš A. Colović, [*On the ring of bounded functions on the character variety*](https://arxiv.org/abs/2611.25162), arXiv:2611.25162v1, submitted 18 November 2026 ([PDF](https://arxiv.org/pdf/2611.25162)). Theorem 1.1 announces the full bounded-functions equality for every finite extension; the proof uses trace integrality/analytic boundaries. It does not use or present the new finite branch-depth formula in the inspected material. The local quantitative question should not be presented as a new solution to that global conjecture.
- Laurent Berger, [*Errata for my articles*](https://perso.ens-lyon.fr/laurent.berger/articles/errata.pdf), dated 13 October 2026, Section 19. The appendix code in the original Berger–Sprang paper adds spurious monomials and does not calculate `s0` as defined; this is confirmed directly by the author’s correction to Appendix A. The 26 November predecessor already corrects this and should be credited. It does not invalidate the source's Lemma 4.2/Proposition 4.4 branch existence argument.

Primary-paper searches for Lubin–Tate branch interpolation, finite jet precision, binomial valuation thresholds and Newton polygons did not locate the exact formula. Search coverage cannot establish worldwide priority. The result is **an explicit answer to an open question in the supplied research corpus, with classical ingredients and no claim of exhaustive bibliographic priority**.

## Source and claim cautions

- Do not describe every archived manuscript claim as independently verified. Exact checks and proof audits done in earlier packets remain their reported work unless rerun.
- Some earlier blanket objections about fixed precision were corrected by later packets: the source controls a full divisible Selmer module in the relevant theorem. Read the latest odd-cocycle/coefficient-descent discussion before repeating older objections.
- A local field/coefficient calculation or Frobenius detector does not supply a new nonabelian arithmetic square-root bound.
- The full bounded-functions conjecture has a separate November 2026 proof announcement; sharpened finite precision is a distinct result.

## Pinned GitHub links for report references

Corpus: https://github.com/VladimirReshetnikov/ProveIt/tree/9816644452bb42827167d6110e6d0322315a02b9/docs/incoming

Nearest branch predecessor: https://github.com/VladimirReshetnikov/ProveIt/blob/9816644452bb42827167d6110e6d0322315a02b9/docs/incoming/grh_transfers_cycle_signings_and_lubin_tate.zip

Matrix-moment predecessor: https://github.com/VladimirReshetnikov/ProveIt/blob/9816644452bb42827167d6110e6d0322315a02b9/docs/incoming/grh_beyond_dirichlet_2026-11-25.zip

Symplectic predecessor: https://github.com/VladimirReshetnikov/ProveIt/blob/9816644452bb42827167d6110e6d0322315a02b9/docs/incoming/grh_sharp_torsion_and_symplectic_blocks.zip

Latest local correction: https://github.com/VladimirReshetnikov/ProveIt/blob/9816644452bb42827167d6110e6d0322315a02b9/docs/incoming/grh_transfer_advances_2026-11-26.zip


## Independent check of the binary-orthogonal question

Primary public question: https://math.stackexchange.com/questions/5119604/principal-submatrices-of-random-binary-orthogonal-matrices . The retrieved page (26 November 2026) explicitly defines `O_n={Q in GL(n,F_2): Q^T Q=I}` and maximum nullity over all principal subsets. It asks for typical size and, specifically, whether a linear nullity occurs with probability at least `1-2^{-alpha n^2}`. The displayed page has no answer body. The definition is the nonalternating **bilinear** identity-form isometry group; it must not be replaced by a characteristic-two quadratic-form orthogonal group.

The proof using the canonical symplectic quotient was independently reviewed. For even n, set `c=(1,...,1)`, `H=c^perp`, and let `W=H/<c>`. The quotient action of `O_n` surjects onto `Sp(W)`: take `a=(1,...,1,0)` and `b=e_n`, so `T=<a,b>` has Gram `I_2`, `W0=T^perp` is nondegenerate alternating of dimension `n-2`, and `H=W0 direct_sum <c>`. Any symplectic automorphism of `W0` extends by the identity on `T`. Uniform group elements therefore have uniform quotient images. For each proper nonempty coordinate subset J, the even vectors in `E_J` and `E_Jc` have dimensions `|J|-1` and `n-|J|-1`, and inject into W. Intersecting an r-dimensional principal kernel with H leaves at least r-1 dimensions. Counting these subspaces and their symplectic-frame images gives the fixed-J bound `C 2^{-r(r-1)/2}`. Odd n has the direct decomposition `<c> perp c^perp` and the same bound using r-frames. A union bound over at most `2^n` subsets gives `Pr(max nullity >= r) <= min(1,6*2^{n-r(r-1)/2})`, for `1<=r<=floor(n/2)`; larger r is impossible.

The orbit-size lower bound is valid for arbitrary (including degenerate) prescribed alternating Gram matrices: independent frames with that Gram extend by Witt's lemma. Successive vector selection imposes i independent linear conditions and excludes at most `2^i` prior-span vectors. Their product is bounded below by `(2/3)*2^{Nk-k(k-1)/2}` when `k<=N/2`. The Gaussian-subspace count uses the product `prod(1-2^{-j})>1/4`. Thus the constant 6 is conservative.

This refutes the linear-nullity alternative and gives a square-root upper order with high probability. It does **not** determine whether the true order is bounded, logarithmic, or square-root; no matching lower-order claim should be made. This is an answer to the [publicly posted question](https://math.stackexchange.com/questions/5119604/principal-submatrices-of-random-binary-orthogonal-matrices), not evidence of a previously unknown major named conjecture.
