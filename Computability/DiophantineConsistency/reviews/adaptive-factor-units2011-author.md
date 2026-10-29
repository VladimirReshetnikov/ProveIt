# Adaptive factor units: author result

The new `ArithmeticAdaptiveFactorUnits2011` proves, in every IΣ₁ model,
that an actual split-natural zero of the accepted 13-variable expression
forces each of its four exact signed factors to equal positive one. The
public generic-port theorem requires no positivity, supplied factor unit,
integer-model assumption, or residue oracle. Its concrete current-port and
single positive-shift natural clients use the actual accepted expression.

The proof maps each arbitrary internal natural to its genuine remainder modulo
four, using the theorem that an element below the standard numeral four is
one of four standard numerals. The resulting map respects addition and
multiplication. Structural induction shows that the difference of the
split-natural evaluations maps to the ordinary `ZMod 4` value of the exact
expression. Finite kernel-checked residue checks exclude negative one for
each of the four literal factors, including when any input is zero. Applying
these exclusions to the previously compiled magnitude theorem yields the
four additive factor equalities.

A lightweight scalar copy of the accepted graph is used solely to state the
four finite residue expressions. Each scalar factor is proved equal to the
mod-four evaluation of the corresponding literal factor expression. The
copy avoids importing the wide native graph together with Foundation, whose
Matrix definitions conflict; the actual expression and factors remain those
of the independently reviewed narrow syntax.

The two fresh author builds match source, object, and complete logs. The main
log is empty, and six axiom reports use only `propext`, `Classical.choice`,
and `Quot.sound`. They used 406 authenticated parent/package source or
object entries and an explicit package boundary for `Mathlib.Data.ZMod.Basic`;
its transitive package interior is not a fresh rebuild. The two runs were by
the same author, and independent review remains necessary. This theorem does
not yet recover the adaptive Pell indices, prove the 13-variable equivalence,
or produce a PRA derivation.

The [36-file evidence manifest](adaptive-factor-units2011-build-evidence/FILES.json)
SHA256 is `9c37e58f5a9c8a449e344ca498d03e00cc91b9e4cf6a5ab86d4d271913d6a8c3`.
It preserves both complete pair builds, snapshots, full logs, timings, provider
pins, drivers and the available scratch proof sources/logs. Scratch runs were
exploratory; their command output and timing were not all separately captured.
The proposed wide graph import produced the preserved Foundation/Mathlib
`Matrix.map` conflict; the final implementation does not use it.

| Source | Source SHA256 | Object SHA256 |
| --- | --- | --- |
| ArithmeticAdaptiveFactorUnits2011 | `7a7ca8ed3cdf7dafb0a084f91750be497a6e333124a940122ababeeb3c85c48d` | `02b388702e68d5727a0f9b1a06c03e5be03bdca54dc82a31abe03f35df0ca7a6` |
| ArithmeticAdaptiveFactorUnits2011Checks | `442e4b2587ccd0894529798497cc0ff7fceef543a0b238280e87e0a44046203c` | `986aa2ee96648c7c0aa10b51dbe637aab2ade0040832278da2fb74aac6d1aa7c` |
