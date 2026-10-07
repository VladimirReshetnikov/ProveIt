# Source and novelty audit

Date: 6 October 2026. This audit separates inspected sources, proof ingredients,
newly developed formulations, and limitations. It is not a priority certificate.

## Repository snapshot

Repository: VladimirReshetnikov/ProveIt. Read through the connected GitHub tool.
Pinned commit: `6c2e2172bab8a0af4aed6b62d53ae7cde9252e8d`.
The branch response identified its commit time as `2026-10-06T23:11:03Z`.

Relevant paths and Git blob hashes:

| Path relative to `Combinatorics/Ramsey/` | Blob SHA |
|---|---|
| `Papers/sz-thm-gowers-proof/sz-thm-gowers-proof.tex` | `41085a0efde8c1932e86e80c791984f52841c22e` |
| `Papers/sz-thm-gowers-proof/sz-thm-gowers-proof.pdf` (metadata inspected) | `db4a37e25a5b7800c925d08f1d38eae9aee8d923` |
| `FORMALIZATION_STATUS.txt` | `bd290646acae149b364432b7870de4d7dae5196a` |
| `Research/GowersSzemeredi/local-quantitative-refinements/README.md` | `b0edfc23a3624a09c7a2087a336d447a4378622c` |

Read scope: directory listings and selected README/status ranges, plus source
TeX ranges including lines 3530–3610 (Lemma 17.1, Proposition 17.2) and
3650–3790 (local phase extraction and the beginning of final assembly).
The large merged research article and every newly pending report were **not**
exhaustively read. Overlap avoidance is therefore scoped, not guaranteed.

The corrected Proposition 17.2 explicitly assumes k+1 < N and gives a phase of
degree at most k+1. The article uses that repaired statement. The original PDF
prints a smaller degree; this discrepancy is already documented and repaired
in the repository, and is not claimed as a new discovery.

## Primary literature consulted

1. W. T. Gowers, *A new proof of Szemerédi's theorem*, GAFA 11 (2001),
   465–588, DOI `10.1007/s00039-001-0332-9`.
   Public copy: `https://www.cs.umd.edu/users/gasarch/TOPICS/vdw/sz-thm-gowers-proof.pdf`.
   Parsed text and a rendered screenshot of PDF page 114 (zero-based page 113),
   journal page 578, were inspected. Relevant baseline: Proposition 17.2.
2. Shamgar Gurevich and Ronny Hadani, *Notes on quantization of symplectic vector
   spaces over finite fields*, arXiv `0708.0669v3` (2009; first version 2007).
   Abstract/metadata verified. Cited only as standard finite-Heisenberg background;
   the article supplies its own proofs rather than invoking an unchecked theorem
   statement from that paper.
3. Jonathan Tidor, *Quantitative Bounds for the U^4-Inverse Theorem over Low
   Characteristic Finite Fields*, Discrete Analysis 2022:14,
   DOI `10.19086/da.38591`, arXiv `2109.13108v2`.
   HTML inspected, especially the symmetry/integration framework and its
   low-characteristic distinctions. We do not claim a replacement for its
   general mixed-function or nonclassical integration results.
4. Luka Milićević, *Approximately Symmetric Forms Far From Being Exactly
   Symmetric*, arXiv `2112.14755v1` (2021). Abstract/metadata verified.
   Records the counterexample to a general approximate-symmetry conjecture;
   our research questions do not present that unrestricted conjecture as open.
5. Luka Milićević, *A quasipolynomial inverse theorem for the U^k(F_p^n) norm
   in the high characteristic*, arXiv `2609.33733v1`, submitted 27 September
   2026. Abstract/metadata verified. It states quasipolynomial bounds for
   p >= k. Cited as a contemporary benchmark, not a proof dependency or
   a fully audited competing theorem.
6. James Leng, Ashwin Sah, and Mehtaab Sawhney, *Improved Bounds for Szemerédi's
   Theorem*, arXiv `2402.17995v2` (2024). Abstract/metadata verified.
   Used only to delimit global-bound claims.

No source paper, source screenshot, or proprietary asset is bundled.
Bibliographic links appear in the article. The source URLs and version IDs
above are stable references, not evidence that every source proof was checked.

## Classification of the article's claims

**Standard ingredients, proved here for completeness:** character orthogonality,
finite Weyl/Heisenberg representation facts, positivity and trace of finite
operators, support induction for a separately linear map, diagonal polarization,
Parseval, and the U^2 fourth-moment identity. No priority is asserted for these.

**Proposed local contribution:** the exact extremal threshold
`1-(1-1/p)^k` for one-function derivative-spectrum selectors; the
amplitude-sensitive alternating-slice-rank profile; the simultaneous endpoint
construction; and the combined robust, lossless symmetry-to-phase interface.
The multiaffine coefficient formulation and the equality/stability description
are included as derived extensions, without claiming they are unknown elsewhere.

**Concrete improvement relative to the inspected scalar proposition:** explicit
canonical phase and a pointwise equality, with the same scalar energy parameter.
This is not an improvement of its already-optimal coefficient one. The new
symmetry threshold is a vector-space extension; symmetry is automatic in the
one-dimensional homogeneous setting.

**Not claimed:** a new end-to-end inverse theorem, a new final Szemerédi bound,
a proof of Proposition 17.7 in the local-box setting, a resolution of general
approximate symmetrization, classical integration in all characteristics,
independent peer review, a checked Lean proof, or literature priority.

Searches around derivative spectra, multilinear symmetry, alternating rank,
and finite Heisenberg orthogonality did not establish the priority status of
the exact threshold. Absence of a located match is not evidence of novelty.

## Mathematical self-audit

- Checked Fourier sign by an independent Fourier-square/cube expansion test.
- Checked the projective cocycle sign: U_h = e_p(-B(h,h)/2) W_h.
- Proved the bilinear bound both by eigenspace multiplicity and by block
  orthogonality; equality/stability use the latter description.
- Kept k derivatives, k+1 tensor slots, degree k+1, and U^(k+1) distinct.
- Used rank over F_p for the prime field and over F_q in the extension-field
  statement; restricted scalars multiply the alternating rank by [F_q:F_p].
- Separated odd characteristic from the stronger p > k+1 integration hypothesis.
- Included an exact characteristic-three counterexample to universal classical
  integration and an affine-offset counterexample to an overextended identity.
- Checked the sharp endpoint in every parameter symbolically; finite enumerations
  verify small cases independently but are not the general proof.
- Restricted equality/stability conclusions to the Hilbert norm; the nearby
  extremizer is not falsely asserted to retain a pointwise amplitude cap.
- Stated global-selector assumptions explicitly in the dense-domain corollary.

These are self-checks, not independent verification by another researcher.
