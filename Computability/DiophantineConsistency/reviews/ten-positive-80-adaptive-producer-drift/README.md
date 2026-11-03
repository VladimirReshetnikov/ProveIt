# Adaptive producer records and two additional drifts

The selected 80 iPRA closure contains 13 adaptive modules whose object hashes
match outputs in the historical adaptive continuation author state and its
independently matched peer receipt. `check.py` verifies those output hashes
and compares the author state's recorded direct project inputs to the final
selected closure. Two records differ:

- `ArithmeticAdaptivePopulation2011` recorded a different
  `ArithmeticHalfBinomial` object.
- `ArithmeticAdaptiveConstructionAuxPhase2011` recorded a different
  `ArithmeticPellRecurrence` object.

The exact historical and final paths and hashes, all 13 comparisons, peer
records, and combined affected module names are in
`observations/attempt01.json`, SHA-256
`20c94b0e3f8c11528ec6b5a3d44c75a0ff1a37a26b286df7f1854656e0d5fc01`.
These are byte-matching, independently verified historical producer
records; byte identity does not establish that the selected file came from
that unique producer. The historical peer receipt itself discloses a known
project-origin mismatch and inherited author-only/package/dynamic ancestry.

Adding the two recorded-drift modules to the five independently identified
nine-prefix drift seeds expands their combined reverse-reachable cone in the
captured 80 selected import graph to 122 modules, all freshly read in that
scan. This is a plan-only lower bound for a coherent rebuild: other historical
drifts can enlarge it. The comparison does not show that the loaded theorem is
unsound and does not authenticate the entire historical source/object chain.
