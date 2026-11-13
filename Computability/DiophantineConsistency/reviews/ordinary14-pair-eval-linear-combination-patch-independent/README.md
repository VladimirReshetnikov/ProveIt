# Independent source review: explicit linear-combination import

The inert snapshot equals the committed pair-evaluation bridge byte for byte
after exactly one prepended import, `Mathlib.Tactic.LinearCombination`. The
original committed and working-tree source bytes match. The bridge contains a
`linear_combination` invocation, and the selected Mathlib source declares
that tactic. The selected guarded package object resolves to the recorded path
and SHA-256; the author receipt was reproduced.

This is a preventive source import, not a demonstrated Lean fix. The review
does not establish whether the original transitive imports already expose the
tactic, whether the selected object and its companions/providers are coherent,
or whether either source elaborates. It makes no root74 overlay, iPRA endpoint,
physical-byte or PDF claim. No Lean run was performed.
