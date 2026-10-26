# Actual C222 Nat checker: independent root review

26 October2026. Root read all132 main lines,51 check lines, the author
receipt and independent source review. `conclusion222` and `valid222`
recompute the actual C222 conclusions and recursive MP checks. Old C254
raw-tree parsing, quoting and round trips are reused as syntax; old C254
semantic soundness is not substituted for the changed calculus.

The endpoint is the actual `KCode222.C222 n` iff some Nat code passes
`check222 code n`. Decoding uses fuel `code+1` and rejects malformed code0.
The truth proof code1, valid conclusion code0, and false formula code1
remain distinct. The changed growG formula, helper-free seed freshness
gate and MP comparisons use their new definitions, including the legal
bundle case a=b,c=0. No consistency or desired-provability premise is added.

Root independently compiled both leaves with `-M6000 -j1
-DElab.async=false`. Both passed; main log is empty and all nine axiom
reports are restricted to `propext`, `Classical.choice` and `Quot.sound`.
Both objects match the author exactly. Thirteen cached custom prerequisites
were reused;28 source/object/external/prior observations were checked
before and after, with compiler and manifest checked separately. No
Foundation module or full closure was freshly rebuilt. Exact records:
[code222-proof-root-replay/ROOT.json](code222-proof-root-replay/ROOT.json).

This establishes an external Nat checker for the actual calculus. A
represented all-model checker, internal seed calibration, actual machine
runtime and the final HA equivalence require additional proofs.
