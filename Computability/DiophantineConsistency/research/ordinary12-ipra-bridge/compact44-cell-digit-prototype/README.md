# Compact local cell digits

`CompactCellDigit.lean` defines a local digit function from a row and a
dummy bit. On the author-side word and payload-slot providers, Lean proves
that its selector positions, dummy position and all 41 copy positions have
the intended values, and that every digit is at most one when the dummy bit
is at most one. Tool session `18074` exited 0 without warnings or `sorryAx`;
the four printed reports contain only `propext`, `Classical.choice` and
`Quot.sound`. The sampled direct dependency and companion records remained
unchanged; the command, logs and hashes are retained in `observations/`.

`CompactCellDigitDef.lean` further proves that, for fixed model elements `a`
and `d`, the function `k ↦ cellDigit a d k` is Σ₁-definable. The first attempt
left numeral comparisons unsolved; the retained second attempt adds numeric
normalization and exited 0, with unchanged sampled direct dependencies and no
warnings or `sorryAx`. Its printed axiom report contains `propext`,
`Classical.choice` and `Quot.sound`. The failed source and both attempt logs
are retained under `observations/`.

`CompactCellDigitUniform.lean` strengthens this to a Σ₁-definable ternary
function in `a`, `d` and `k`. Its guarded author attempt exited 0 without
warnings or `sorryAx`; the printed axioms are `propext`, `Classical.choice`
and `Quot.sound`, and the sampled direct dependencies were unchanged. An
earlier dependency scan used an incorrect provider path and failed before
Lean compilation; its diagnostic is preserved as `uniform-attempt01`.

These incremental single-author results inherit the word and lookup providers'
transitive and package ancestry. They do not yet pack the digits into a cell,
establish no-carry or graph-zero conditions, or prove an iPRA endpoint.
