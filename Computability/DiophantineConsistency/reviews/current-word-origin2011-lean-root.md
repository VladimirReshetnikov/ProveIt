# Constructing the cell-origin masks: author receipt

Date: 2026-10-26. ROOT authored and read both complete final sources.
This is an author self-review, separate from independent composition
review of these proofs and their stated scope.

| Source under `Lean/DiophantineConsistency/` | Lines | SHA-256 |
| --- | ---: | --- |
| `CurrentWordOrigin2011.lean` | 118 | `6b6bb89e40422745154e5ef990d9909a65b740d43e86842b54fde887f5de3f56` |
| `CurrentWordOrigin2011Checks.lean` | 54 | `141e38f2420bb0b6aa29f3e42fdb294944a9edd7eca3dc5ae9d6d8d37108e558` |

The direct imports are frozen `CurrentWordCopies2011` and
`CurrentWordTopBounds2011`. ROOT read both complete sources/checks and
author/peer receipts before writing this composition, together with the
literal high-mask and marked-word definitions. Existing prerequisite
objects were reused. No dependency was changed.

All three bare kernel inputs are unsupported at an aligned cell origin.
Each reflected source lies in the previous cell at1006+position(e),
again outside support. Thus the full convolution is zero for arbitrary
numeric controls, including cyclic wrap and N=1. For Boolean controls,
the actual whole-cell rotation gives the indicator of Start at j−s.
The outgoing origin carry follows from the low reset; its incoming carry
is the proved previous cell's top2010 reset. The actual decomposition
therefore gives precisely that indicator for the normalized digit.

Actual temporal matching at the global Start would equate South1 with
North435 if its temporal predecessor were Start. This proves the
predecessor is not Start without a unique-Start premise. The normalized
global-origin digit is consequently zero and passes the exceptional
mask3. Every other cell-origin digit is0 or1 and passes mask4.
No mask, supplied pair equality, clean carry or controller assumption
is used. The new theorem concerns every bounded normalization of the
same constructed word.

Both complete final files were freshly compiled sequentially using
`lake env lean -M6000 -j1`, source-level `Elab.async false` and pinned
Lean4.32.0, writing their named main/check objects. Both terminal results
were exit0; the main log is empty and all six intended reports contain
only standard Lean axioms. No `sorry`, `admit`, `native_decide` or new
axiom occurs. No fresh full closure or umbrella replay is claimed.

Checks retain arbitrary numeric raw controls at N=1; a possibly positive
shifted Start digit and the different mask3/mask4 effects; impossibility
of actual marked matching at zero stride and N=1; and an existential
normalization with every actual cell-origin mask. The negative controls
assert no machine halt or synthetic tiling.

| Root evidence | SHA-256 |
| --- | --- |
| `/tmp/current-word-origin2011-root-main.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/tmp/current-word-origin2011-root-checks.log` | `34fbf75192297661043cf4fa08a40a9c2874983b2f0d79cb1a124c4b80f0da71` |
| Main `.olean` | `5533a1a5815948582be193d9ae0b3a62a8e9f20425ed9402b1f18d99f8ca32a1` |
| Checks `.olean` | `28ada5474edf83bb2cfc28c08b6fadb242181889c4885e712562f041abb157d9` |

Development failures were missing namespace and numeral-cast rewrites,
an unexpanded word alias and redundant simplification after a rewrite.
Explicit helper equalities and unfolding fixed them without adding
premises or raising limits. Padding, full high-mask packing, actual rank
controller, polynomial converse and internal-ZFC derivation remain open.
The maintained equation artifacts and required presentation are unchanged.
