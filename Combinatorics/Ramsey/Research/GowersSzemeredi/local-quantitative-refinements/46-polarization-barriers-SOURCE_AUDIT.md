# Source and claim audit

Prepared 6 October 2026 (America/Los_Angeles).

## Repository material actually inspected

Repository: https://github.com/VladimirReshetnikov/ProveIt

1. `Combinatorics/Ramsey/Papers/sz-thm-gowers-proof/sz-thm-gowers-proof.tex`
   - Inspected blob: `41085a0efde8c1932e86e80c791984f52841c22e`.
   - Several passages in later sections were read, including the neighborhood
     of Lemma 17.1 and Proposition 17.2.
   - The corrected source assumes k < N in Lemma 17.1 and k+1 < N in
     Proposition 17.2, for prime N.
   - Our scalar result permits nonclassical phase-valued functions; it is not
     a claim that the original classical codomain works without those bounds.

2. `Combinatorics/Ramsey/Research/GowersSzemeredi/local-quantitative-refinements/README.md`
   - Inspected blob: `fe4d31eb3077580b2509ea146315d9857eb021d3`.
   - Read the inventory and several later ranges, including sources 15–18.
   - Source 15 already discusses derivative-spectrum square identities and
     separated-phase untwisting. The paper does not claim those general
     phase-absorption or Gowers–Cauchy–Schwarz steps as new.
   - Reading the inventory is not an exhaustive line-by-line audit of all
     existing articles. The main research target was chosen to be distinct:
     exact obstruction-rank-controlled binary cubic norms and low-characteristic
     trace tensor classification.

3. `Combinatorics/Ramsey/Lean/GowersSzemeredi/`
   - The directory listing was inspected. It contains a nested project and
     wrapper files including `sections_17_18.lean`.
   - A direct attempt to fetch `Section17.lean` at the top project level failed;
     that failure does NOT establish an absence of Section 17 material.
   - No existing Lean module was modified, and no Lean verification is claimed.

The identifiers above are **Git blob identifiers, not commit identifiers**.
The paper's bibliography links the public repository directories, which may
continue to change after inspection.

## Primary literature consulted

- W. T. Gowers, *A new proof of Szemerédi's theorem*, GAFA 11 (2001), 465–588.
  DOI: https://doi.org/10.1007/s00039-001-0332-9
  Used through the repository's corrected transcription and verified publication
  metadata. Main connection: Lemma 17.1 / Proposition 17.2.

- T. Tao and T. Ziegler, *The inverse conjecture for the Gowers norm over finite
  fields in low characteristic*, Ann. Comb. 16 (2012), 121–188.
  https://arxiv.org/abs/1101.1469
  Credit: nonclassical polynomial framework, coordinate degree/depth description,
  and necessary repeated-variable conditions on total derivatives.

- J. Tidor, *Quantitative bounds for the U^4-inverse theorem over low
  characteristic finite fields*, Discrete Analysis 2022:14.
  https://doi.org/10.19086/da.38591
  https://arxiv.org/html/2109.13108v2
  https://arxiv.org/abs/2109.13108
  Credit: general converse integration theorem (Proposition 3.5).
  Comparison: Proposition 4.6 gives codimension <= 8 log_2(1/delta) under the
  same symmetric seven-function hypothesis. Our theorem proves <= 2 log_2(1/delta).
  We do not claim a new general integration criterion or an unaudited improvement
  of the nonsymmetric Corollary 4.8 / full inverse-theorem constants.

- A. Berger, A. Sah, M. Sawhney, J. Tidor, *Non-classical polynomials and the
  inverse theorem*, Math. Proc. Cambridge Philos. Soc. 173 (2022), 525–537.
  https://arxiv.org/abs/2107.07495
  https://doi.org/10.1017/S0305004121000682
  Used to distinguish exact integration from the existence of classical
  correlations in inverse theorems. These statements must not be conflated.

- J. Leng, A. Sah, M. Sawhney, *Improved bounds for Szemerédi's theorem*.
  https://arxiv.org/abs/2402.17995
  Context only. No claim that the present local results improve its global bound.

- L. Milićević, *General inverse theory for the U^4 norm* (2026).
  https://arxiv.org/abs/2601.01682
  Its existence and abstract were checked. The entire long preprint and its
  appendices were NOT exhaustively audited. This is an explicit priority
  limitation, particularly for related tensor-integration and trace questions.

## Claim ledger

### Proved in this article

1. Exact mixed binary cubic norm 2^(-rank(C_T)/2), with a common eighth-root
   cubic-phase extremizer for every symmetric T.
2. Exact vertex-polarization agreement and mean squared phase-error thresholds.
3. Exact spectral defect identity and the stated near-extremal consequences.
4. Seven-function bound 2^(-rank(C_T)/4), and restriction codimension
   <= 2 log_2(1/delta) under symmetry.
5. Explicit scalar integration in every order with optimal universal root order;
   explicit all-characteristic scalar multi-affine polarization.
6. Trace-multiplication exact-integration classification for every degree.
7. Closed first-obstruction rank and maximal integrable restriction dimensions.
8. Exact elementary symmetric repair number; ordinary slice-rank bounds
   r/2 <= rho <= r, with rho=2 when r=2.
9. The explicitly stated analytic untwisting identities and consequences.

Items 5–9 combine self-contained calculations with established background.
The ledger is not a declaration that each statement is historically new.

### Explicitly not established

- Exhaustive novelty or first-publication priority across all literature/repo notes.
- A new general nonclassical integration theorem (already known).
- A sharper global Szemerédi bound or a new general U^k inverse theorem.
- Sharpness of the seven-function estimate or its codimension constant.
- A full classification of all cube extremizers or structural stability of f.
- Exact unrestricted slice-rank repair beyond the stated cases.
- Lean kernel verification of any theorem in this package.

## Computational evidence

All reported validation arithmetic uses integers or rational numbers. The
report contains 80 scalar checks, 141,781 trace-integrator cube/basepoint checks,
770 trace-coefficient rank/isotropic checks, 5 explicit obstruction witnesses,
692 fourth-root function tables, 209,664 additional cube/basepoint checks for
nine symmetric binary tensors, and 36 mixed plus 36 seven-function tests.
Some function tables are sampled; the JSON records which cases are exhaustive.
Finite tests do not replace the general proofs.
