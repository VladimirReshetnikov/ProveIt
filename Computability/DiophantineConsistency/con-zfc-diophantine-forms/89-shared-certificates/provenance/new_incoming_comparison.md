# Incoming comparison at the pinned repository snapshot

Repository: `VladimirReshetnikov/ProveIt`.

Snapshot: `08200eb10fde2db408c69dffd840d6920a569b1f`.

All six ZIP archives present under `docs/incoming` were inspected as inert
data. This comparison reads their root descriptions and, for the relevant
integer-coordinate family, their literal packets and proofs. It does not
claim that every incoming release verifier was rerun. Exact archive and
member hashes, and retained root texts, are supplied in
`../coordinate_family/INCOMING_PINS.json` and
`../coordinate_family/comparison/`.

In the tables, `(n,d)` means **n unrestricted integer unknowns, exact total
degree d**. Positive-variable counts are explicitly separated. A source-level
checker improvement is not counted as a completed consistency polynomial.

## All six incoming sources

| Exact incoming archive name | Relevant unrestricted-integer results reported there | Other leading reported endpoints | Scope note |
|---|---|---|---|
| `ConZFC_Structural_Reductions_Round11_2026-10-24.zip` | `(37,4)`, `(30,6)`, `(26,8)`, `(25,10)`, `(24,12)`, `(23,16)`; also 10 integers, degree 1,245,324, 480 operations | 11 positive integers, degree 277, 111 operations; 12 positive integers, degree 78, 101 operations | Locally downloaded as `round11.zip`; the exact repository filename is the one shown here. |
| `ZFC_Diophantine_Joint_Guards_2026-10-24.zip` | `(37,4)`, `(31,6)`, `(25,8)`, `(23,12)`, `(22,16)`, `(21,20)`, `(20,32)`, `(19,88)` | 11 positive integers: degree 277 / 111 operations and degree 257 / 114 operations | The new coordinate family uses the exact incoming `joint/joint25_octic.json`, connected to the convenient reconstructed presentation by checked reversible row operations. |
| `con-zfc-radical-guard-descent-2026-10-23.zip` | `(31,6)`, `(26,8)`, `(23,12)`, `(22,14)` | 9 positive integers, degree 1,158,228, 1,753 operations; 11 positive integers, degree 277, 111 operations | Its extracted root is named `con-zfc-cross-guard-descent-2026-10-23/`. |
| `con-zfc-budget-and-centering-2026-10-23.zip` | `(26,8)`, `(24,10)`, `(23,16)` | 11 positive integers, degree 277, 111 operations; 12 positive integers, degree 78, 103 operations | The separate direct-certificate appendix has local metrics, not a materialized final consistency equation. |
| `con-zfc-centered-pell-norms.zip` | `(31,6)`, `(26,8)`, `(24,10)`, `(23,12)`, `(22,14)` | 11 positive integers, degree 277, 111 operations; 12 positive integers, degree 78, 103 operations | Its 22-integer degree-14 point has 123 reported live binary operations. |
| `report.zip` | A 31-integer sextic | 11 positive integers, degree 277, 111 operations; 12 positive integers, degree 70, 100 operations; 9 positive integers, degree 1,158,240, 811 operations | This archive contains only `report.tex`. Its referenced equation/certificate files are not delivered inside this ZIP, so these are manuscript-reported endpoints, not independently replayed artifacts. |

The combined low-degree integer points relevant to this comparison are

| Integer unknowns | Lowest relevant incoming degree found | Source |
|---:|---:|---|
|37|4|Round11; Joint Guards|
|30|6|Round11|
|25|8|Joint Guards|
|24|10|Budget and Centering; Centered Pell Norms|
|23|12|Joint Guards; Radical Guard Descent; Centered Pell Norms|
|22|14|Radical Guard Descent; Centered Pell Norms|
|21|20|Joint Guards|
|20|32|Joint Guards|
|19|88|Joint Guards|

This table is a comparison of the inspected low-degree branch. It is not a
complete literature-wide frontier and does not erase the separate
10-unrestricted-variable or 9-positive-variable high-degree constructions.

## New coordinate-family improvements

| Integer unknowns | Incoming degree | New exact degree | Degree reduction | New residual count |
|---:|---:|---:|---:|---:|
|21|20|16|20%|9|
|20|32|18|43.75%|8|
|19|88|40|54.545...%|7|

The new ingredient is the coordinated choice of `C=q-F-alpha`, `Y=a-E`,
and `k=eta+zeta`, followed by monic elimination of `F,E,eta,V` and integral
Pell-root translations. This keeps the two quantities entering the joint
guard quartic while removing four coordinates. Later monic projections
give the 20- and 19-variable equations. No new sign, positivity, or nonzero
condition is introduced by these maps.

The exact equations, proofs and independent audit are in
`../coordinate_family/`. Their six numerical coefficients are the same
complete source-34 tuple and determinant scales used in the incoming
integer family. The total minimal coefficient payload remains 615,883
bytes; no improvement in coefficient height is claimed. No globally
minimal arithmetic circuit is asserted.

The earlier independently reconstructed `(37,4)`, `(31,6)`, `(25,8)`,
`(24,12)`, and `(23,16)` packets are retained solely as reproducible
background and restoration checkpoints. They are explicitly **not new
frontier claims** after the incoming material was considered.
