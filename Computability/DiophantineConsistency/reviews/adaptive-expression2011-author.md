# Adaptive 13-variable expression binding: author result

29 October 2026. Four new leaves bind the accepted adaptive 88-gate expression
to an `Expr (Fin 13)` with the exact current ports, and prove the single
positive shift for equality of the natural split in every commutative
semiring. The wide leaf proves integer evaluation and exact polynomial
identity for arbitrary ports, plus the standard-natural split-zero equivalence.
Its generic ring evaluation is private; no extra Mathlib import was needed.
This is not an all-model zero-existence equivalence, an HA/PRA derivation, or
a proof of the factor extraction/Pell reconstruction still required.

The 24 prerequisite current-source rebuilds all exited zero using the frozen
plan. Two existing prerequisite sources produced linter warnings:
`NativePellStepDown` (1) and `SplitCertificate59` (46). These complete logs
are preserved; no warning-free claim is made about that rebuild. Source pins
and inputs were checked, but this was not a fresh independent mathematical
review of every old prerequisite. Package interiors remain the explicit plan
boundaries. The objects remain in `/tmp/adaptive13-refresh-p6h7b6p0/lib`.

Two complete fresh four-leaf runs passed with identical source, object, and
full-log hashes. The first successful timings were 4.669, 2.829, 8.804, and
5.041 seconds; seven reported theorems used only `propext`,
`Classical.choice`, and `Quot.sound`. The later reproducibility run was by
the same author and is not an independent review. An independent source-text
audit matches all 13 coordinate aliases, four ports, and all 88 ordered gates
to `NativeAdaptiveGraph.core`.

The [138-file evidence manifest](adaptive-expression2011-build-evidence/FILES.json)
SHA256 is `97b4984951b4d9dc42467c390186013780c85d8436975e68acf65081dd7a7175`.
It contains the full refresh inputs, source snapshots, logs, timings, states,
drivers and the five leaf attempts. Attempt 1 failed because Lean selected the
first namespace directory without the prerequisite object; attempt 2 reached
the narrow pair but lacked an imported `MvPolynomial.funext`; attempt 3 needed
operation-specific simplification lemmas for the generic ring evaluator. Both
successful runs followed these corrections. A preliminary driver had a Python
syntax error before creating an overlay or invoking Lean, and is preserved.

| Leaf | Source SHA256 | Object SHA256 |
| --- | --- | --- |
| AdaptiveEquationSyntax2011 | `f1d7f3835bc2a183b0767497a45ffdd0a54e6aab086b259ccce3de4af9392cb6` | `b59cc86a1351d7f6eff9caa2256b7b52aee8fda49a65e9f5ed6b9553ae573261` |
| AdaptiveEquationSyntax2011Checks | `133526f67e182a7b836745b8798e896b78e1464fd63babcfaf22a5adfcc5dc68` | `b5df2657addccb1eb5a4d941e7a4850fc026ecd173d437bcf3293f1b2f414fa3` |
| NativeAdaptiveExpression2011 | `4ddcf6a48cc1967652d13d05394091295561f2f5f75aa76b425a4e8f97d69643` | `e8e26d0997810d8b604dc6a2a81e8b9e5652ce9505db155477815a154a76a627` |
| NativeAdaptiveExpression2011Checks | `a3509a3fd10017b794abeb4395bd585640ff393b1155df618310420a34302eb6` | `f069b7eb1d010a8f90bfd3fb27d24afde2e58bb3e071bb0a027dac7cb188f3a5` |
