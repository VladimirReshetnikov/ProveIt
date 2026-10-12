# Scoped source audit

Prepared 11 October 2026. Source metadata and hashes are in
`source_manifest.json`.

## Repository and incoming report

The canonical manuscript README and incoming-directory metadata were read
through the GitHub connector. Selected older harmonic-tail sections were
read at commit `47f2d0da4f1c0e19f9ec8aecb39112756f167d82`; later indexed
searches reflected newer commits. This is not a claim to have checked a
single atomic snapshot of the entire repository.

The mathematical predecessor is the standalone TeX of *Affine Gamma
Polarization*, Library version 1 (1,702 lines). The principal inspected portions
were the Lerch endpoint section (lines 880–985), Bernoulli selector section
(lines 1087–1321), and the further questions beginning at line 1505.
Its source hash is recorded in the manifest. GitHub separately listed the
matching named incoming ZIP, but this run did not extract the binary ZIP
and compare all its members with the Library file.

The report's Frobenius–Euler basis ingredient is already a classical theorem,
not a new polynomial construction. The external primary-source check identified
Kim and Kim's Theorem 1 as an exact predecessor for the endpoint basis formula.
The new classification includes the finite remainder and a C(s)-linear
independence proof, endpoint obstructions, and exact confluence consequences.

No false theorem was identified in the inspected selector portion of the
incoming ProveIt report. Its question about twisted single-order selectors
is answered in the stated domain. A nonresonant double-flat one-order
extension is disproved, rather than being silently assumed to exist.

## External coefficient question and corrections

Source: Dora Pokaz, Mihaela Ribičić Penava, Yilmaz Simsek,
*Certain families of series involving Hurwitz and Lerch zeta functions*,
arXiv:2609.13796v1 (12 September 2026).

The definition, question, and relevant formulas were checked in HTML and
in PDF pages. The corrective normalization always preserves Definition 1.

| Source location | Observation | Replacement in this report |
|---|---|---|
| Page 9, open coefficient question | Coefficients requested for every v | alpha_j=(-1)^(j-1) binomial(v-1,j), Article (11.2)–(11.4) |
| Page 11, equation (17) | Mellin prefactor differs from Definition 1 by ((v-1)!)^2 | Article (11.8), prefactor -1/((v-1)! Gamma(s)) |
| Page 11, displayed v=2 integral | Negative sign and Gamma(s) conflict with its positive Mellin kernel | Article (11.9), Gamma(s+2) zeta(s+2,a) |
| Page 12, equation (19) | Interpolation minus sign conflicts with the defining series | Article (11.11), Z_v(-k;a)=ell_k(a+1;v) |

The last claim has the immediate normalization check v=2, k=1: both correctly
normalized values are 1. The package additionally checks 78 integer values by
independent rational generating-series and continued-zeta calculations.
These are version-specific mathematical corrections, not allegations about
the ProveIt manuscript and not an exhaustive audit of the external paper.

## Novelty and proof-status limits

The contribution is a research continuation with all-index proofs. The
partial-fraction solution to the external question is elementary; no new
partial-fraction method is claimed. Classical bases, special-function
continuation formulas, and earlier weighted-integral literature are credited.
A limited literature search cannot establish global priority.

The report has no theorem-prover formalization, numerical interval certificates,
or assertion of arithmetic independence after specializing the spectral order.
The major S6/S8 and general unequal-tail period/rank questions are left open.
External papers and the predecessor TeX are not bundled in the deliverable.
