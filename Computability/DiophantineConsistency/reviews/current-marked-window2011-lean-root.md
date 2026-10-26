# Actual polynomial zeros yield a marked cyclic Wang word

Date: 2026-10-26. Independent complete source/check review and fresh replay:
ROOT. See the [author receipt](current-marked-window2011-lean-author.md).

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| CurrentMarkedWindow2011.lean (148 lines) | b8df6733e6a812d31e251c817076671ce319927fd635731af3e88bab309585d3 |
| CurrentMarkedWindow2011Checks.lean (69 lines) | 0da5024cc6a44866be51dc659174e67c360bdfe753c3480eaba6b92bb1339ce6 |

Both complete sources, including the final local-instance priority
annotations, were read before fresh direct root `lake env lean -M6000
-j1` runs. Main output was a separate temporary object; checks imported
the frozen author-built main object. Both passed, with empty main
diagnostics and nine standard-only axiom audits. Existing prerequisite
objects were reused, not their entire closure freshly rebuilt. ROOT
authored TileColors and earlier count/decoding compositions, so this is
independent review of this new implementation, not the entire chain's
authorship. No umbrella build is claimed.

The exact bitShift is the original core.rank.toNat-47*(N*2011), and the
stride is(bitShift/47)/2011 without reducing it or choosing another value.
The canonical cell coordinate sends the actual predecessor to j-1 and
the original temporal base to j-stride, even for large cyclic shifts.

Choice selects the already existing actual tile in each original cell
coordinate.symm j. Its full Selected predicate is retained, including all
other selectors being zero. It does not create a replacement Boolean word.
At the origin only, within-cell uniqueness identifies the tile with Start0.
Actual color theorems then provide both fields of MarkedWord, with the
literal table and true East/West, South/North orientation.

The actual Start also excludes zero temporal displacement modulo the
entire physical word. Cancelling2011 from the displacement and modulus
together transfers this to nonzero stride in ZModN, without assuming
coprimality. Positive natural stride follows. N=1 is consequently excluded
for actual Facts, while the earlier generic singleton-coordinate lemmas
remain valid. These are conclusions, not added fields of MarkedWord.

The Facts endpoint needs only the original Facts; count, phase, alignment,
occupation and labels are all derived. The polynomial endpoint takes only
positivity and zero evaluation of the actual fixed14-variable polynomial
and retains the same N, source x, c, carry and digits, augmenting them by
the marked assignment and exact selector binding. There is no rectangular
quotient, globally unique Start, run, halting or target-equivalence premise.

The actual Wang-word-to-machine theorem, cofinal canonical converse,
arithmetic/controller completeness, other frontier equations and
internal-ZFC proof remain open. This is the forward polynomial-to-native
marked-word checkpoint, not a finished consistency equivalence.
The displayed decimal equation and all its metrics are unchanged.
