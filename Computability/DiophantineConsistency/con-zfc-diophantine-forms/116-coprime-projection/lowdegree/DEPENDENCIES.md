# Ordinary dependency chain and exact source boundary

## New local reductions

1. `equation.json` (15 unrestricted integers, degree56,110 operations) is equivalent in integer-zero existence to `source/normalized17_degree48.json`, by `PROOF.md`, Sections2–6. The proof restores every literal source coordinate, including the omitted main projection, and maps every source zero back.
2. `fourteen/equation.json` (14 unrestricted integers, degree108,119 operations) is equivalent to the15-variable equation by `fourteen/PROOF.md`, Sections2–4. Monic-quartic integrality licenses CRT before radical extraction.

The copies under `source/` are unchanged except their filenames. `SOURCE_PINS.json` binds their exact bytes and original paths.

3. `thirteen/equation.json` (13 unrestricted integers, degree274,129 operations) is equivalent to the15-variable equation by its complete three-root and adjacent-Pell maps.
4. `twelve/equation.json` (12 unrestricted integers, degree500,148 operations) is equivalent to the15-variable equation by its four-root and guard-restoration maps. Both use monic integrality before CRT and fixed three-adic separation before restoring the omitted integer roots.

## Retained mathematical sources

- `source/BUDGET_PROOF.md` is the complete ordinary proof for normalized17 degree48. It supplies the signed centered guard, normalized strong-rank restoration, exact source18 coordinate maps, and simultaneous canonical completeness.
- `source/PROOF.md` is the normalized18 proof, including the normalized rank lemma, auxiliary-index reconstruction, and mapping to its pinned nineteen-integer parent.
- `source/CENTERED_BUDGET_PROOF.md` supplies the late centered half-binomial argument. The budget does not imply the old determinant guard; positivity of eta is recovered only after the signed power bootstrap.
- `source/SIGNED_QUADRATIC_PROOF.md`, Sections2,4–5, supplies main-root recovery and the whole-product quadratic projection estimate. Its use here is restricted to hypotheses explicitly established with the centered interval; the omitted main projection is never presupposed.

Their full named predecessor chain, coefficient recipes, compiler sources, licenses and original calibration proofs are retained in the accompanying unchanged budget predecessor archive:

`docs/incoming/ZFC_Diophantine_Budget_Interpolation_2026-10-24.zip`

in the pinned ProveIt tree (HEAD84e16e43092614bae262ca59651cb9d77e31a255), and/or its unmodified extracted package `ZFC_Diophantine_Budget_Interpolation/` shipped by the enclosing release. In particular inspect `guard/provenance/centered17/` and `guard/provenance/centered18/`, and their source34/orientation/native/compiler/refutation interfaces. The enclosing release must retain that complete predecessor archive or extracted package rather than present these copied cuts as a standalone compiler proof.

## Coefficients

All six fixed payloads under `coefficients/` are the actual complete source34 mixed-parity-unrounded-1064921 integers. MF is already shifted by beta. `coefficients/BINDING.json` records raw hashes, bit lengths and original source commit. No alternative compact44/BFS44 coefficient slice is substituted. Every circuit has exactly these six fixed leaves and no adjustable coefficient parameters.

## Checks and dependencies

The builders use Python's standard library only. The independent audit scripts additionally require SymPy, listed in `requirements.txt`. Every audit imports no builder and checks explicit data independently. An optional byte comparison to an adjacent original baseline may run when that baseline is present, but raw payload hashes are independently pinned and always checked; the baseline is not needed for portable execution.

These are ordinary mathematical reductions and finite transcription certificates. They do not constitute a new end-to-end Lean/Rocq proof, an encoded internal object-ZFC derivation, an assertion that the polynomial has no zeros, or a consistency proof.
