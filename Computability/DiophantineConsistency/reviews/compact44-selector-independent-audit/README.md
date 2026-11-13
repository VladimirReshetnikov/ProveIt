# Independent compact selector-count audit

The read-only [audit](audit.py) of `bea685c46d` actually exited 0 in session
35742; its [receipt](CHECK.json) and [terminal observation](terminal-observation.json)
record the result. It checked the committed sources, recorded outer exit,
both source/object/log chains, direct imports and child exits, and reran the
independent 24-module window parent audit successfully. The two objects and
logs match, and the report on each side lists Lean metatheory `propext`,
`Classical.choice`, and `Quot.sound`, without warnings or `sorryAx`. No Lean
compile was rerun. The inherited providers lack a complete printed axiom
inventory, and Foundation outer-wrapper and package-transitive/dynamic
ancestry qualifications remain. RSS values are samples rather than a
continuous whole-process-tree quota.

The theorem works in any IΣ₁ model and takes arbitrary model elements n and
P, with explicit hypotheses `n < 2^10` and
`NoCarry(n + 2^10*P, 2^51−2)`. It concludes `n ≤ 1`. Exponentiation,
subtraction, modulo and the no-carry predicate are model operations. The
argument extracts the low 51-bit digit, applies the mask lemma to bound it by
one, then reduces modulo 2^10. It does not show that an actual graph supplies
these hypotheses, identify a selected tile, bind the compact44 payload,
calibrate the checker, or produce an iPRA proof.

The separately retained exploratory attempt 01 is recorded as exiting 1
with `sorryAx`; the corrected exploratory attempt exited 0 without warnings.
Neither substitutes for the successful paired replay.
