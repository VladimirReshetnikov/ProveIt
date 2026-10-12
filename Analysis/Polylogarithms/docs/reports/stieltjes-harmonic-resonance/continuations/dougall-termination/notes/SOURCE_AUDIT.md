# Source audit and provenance

## Repository snapshot

Repository: `VladimirReshetnikov/ProveIt`.

Pinned commit: `da2792fc9cc8ef19c6a314be6c65e1437fbdc66b`.

The branch metadata reported commit message “New research reports” and commit time `2026-10-11T21:44:07Z`. The report was prepared on 11 October 2026. No repository mutation was made.

## Text inspected

Paths in the first group are relative to `Analysis/Polylogarithms/docs/manuscript/`.

| Path | Inspection scope | Role |
|---|---|---|
| `polylogarithms.tex` | Complete top-level file | Preface, proof/evidence conventions, chapter order. |
| `chapters/10-discovery.tex` | Returned chapter text, including surviving research programme and S8 exclusion | Scope: S6 remains conjectural; frozen S8 vector rejected. |
| `chapters/07-integration.tex` | Lines 1–180 | Gamma integral, Hurwitz-jet conventions and attribution. |
| `chapters/04-depth.tex` | Lines 1–200 | Alternating Gaussian sums, classical antecedents, domain conventions. |
| `chapters/04-cyclotomic-quotients.tex` | Lines 1–200 | Distinction between formal quotient relations and numerical period independence. |
| `chapters/07-mixed-dougall-identities.tex` | Lines 1–240 | First mixed resonance, normal convergence, trigamma square, tail identities. |

The decisive prior report is under:

`Analysis/Polylogarithms/docs/reports/stieltjes-harmonic-resonance/continuations/centered-dougall-resonance/`

Inspected there:

- `README.md`, complete.
- `integration/centered-dougall-resonance.tex`, complete.
- `article.tex`, lines 650–880.

The full integration text already proves the all-N centered subtraction, residue polynomial, collapsed digamma value, and all spectral jets. The inspected article range proves selected polynomial loci and harmonic specializations. These are antecedents, not new results of this package. A complete termination classification was not present in the inspected text.

Selected source blob identifiers, supplied by GitHub, are retained as provenance rather than an integrity-check project:

- Canonical mixed section: `81089b25df9c2eb13c29ee86fcae007895ddb9a0`.
- Prior integration text: `c98242c8ffe443acc771a7f13348c86b50132899`.
- Prior article: `a9f059fd9a95ecd60d85e90288d2bcd7cd00a0de`.
- Prior README: `cedf75196dabd7ee1949dcb2c32da1eb2fa7eb8d`.

## Incoming archive limitation

The directory listing and lines 1–140 of `docs/incoming/README.md` were read. The listing exposed:

- `ProveIt_Alternating_Tails_Spectral_Defects_2026-10-11.zip`
- `ProveIt_Finite_Difference_Determinants_2026-10-11.zip`
- `ProveIt_Higher_Quadratic_Jets_2026-10-11.zip`
- `ProveIt_Higher_Spectral_Defects_2026-10-11.zip`
- `ProveIt_Quartic_Spectral_Reconstruction_2026-10-11.zip`

The binary download route did not yield usable archive bytes. **The archives were not unpacked and their contents were not reviewed.** Their names do not establish their mathematical content or absence of overlap. Novelty comparisons are therefore limited to inspected text, not the entire incoming collection or repository.

## External primary sources

The following official references were retrieved online on 11 October 2026:

- NIST DLMF §16.4, including Eq.16.4.9, Rogers–Dougall very-well-poised 5F4 sum: https://dlmf.nist.gov/16.4
- NIST DLMF §5.5, Gamma functional relations: https://dlmf.nist.gov/5.5
- NIST DLMF §5.11, shifted asymptotic expansions: https://dlmf.nist.gov/5.11
- NIST DLMF §25.11, Hurwitz zeta: https://dlmf.nist.gov/25.11
- NIST DLMF §25.12, polylogarithms: https://dlmf.nist.gov/25.12
- Ce Xu and Weiping Wang, “Dirichlet type extensions of Euler sums”, Comptes Rendus Mathématique 361 (2023), 979–1010, DOI 10.5802/crmath.453. Publisher page: https://comptes-rendus.academie-sciences.fr/mathematique/articles/10.5802/crmath.453/

Only the Xu–Wang publisher abstract and bibliographic information were inspected, not a full-paper comparison. Broader web searches were not sufficient to establish worldwide priority. No claim that the displayed Euler-sum special cases are absent from the literature is made.

## Reproducibility scope

All code in this package was executed in the current session. The article and insertion preview were compiled locally and rendered for visual inspection. Exact tests and numerical diagnostics have separate result records. The proofs are ordinary mathematical proofs, not proof-assistant formalizations; numerical records are not rigorous error enclosures.
