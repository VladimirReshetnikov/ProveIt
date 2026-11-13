# Independent audit of the current-provider denominator composition

The read-only audit of the paired result exited 0 in tool session 71522.
It binds the proof packet `6a852a749c`, retained logs `44b1d4fd2c`, wording
correction `d40b6397f5`, and the recorded outer wrapper exit 0 in session
52014. No Lean compiler was run by this audit.

Both sibling chains contain the same 12 source rows. The audit checks all
24 recorded compiler and direct-dependency exits, source and object hashes,
copied logs, sampled leader-RSS values, and exact direct imports against the
declared source order. It verifies the 70 parent object links on each side,
the complete parent-plus-suffix object inventories, the audited parent and
monitor receipts, and an independent read-only parent comparator rerun.
Corresponding 12 source, object, log and axiom-report rows match. The final
composition object has SHA-256
`d9ac9454128d5ee18a511962be0ba9446f5e09640c8fc343a59cd95d0522d8f7`.
The recorded suffix logs have no warnings, errors or `sorryAx`; the final
three reports use only `propext`, `Classical.choice` and `Quot.sound`.

The final model theorem assumes the positive twelve-coordinate internal zero
and the stated natural-port inequalities in an `IΣ₁` model. It identifies the
proof-only denominator in the model difference ring, proves it nonzero, and
derives the cleared auxiliary equation for that same denominator. This
connects the signed residual transport and denominator sign. It does **not**
prove denominator integrality, construct the ordinary witness, calibrate the
compact44 checker, or establish an iPRA equivalence.

At the post-run audit instant, both the repository and frozen source manifests
matched the audited `9a7059e4…` hash; all 70 parent source pairs and all 12
suffix source pins matched. Independently reconstructing the 12 source import
lists against that manifest and preceding suffixes confirms the closure at
this observation. The live driver did **not** hash-pin the manifest at the
time of its earlier read, so this does not establish the exact bytes it read
or exclude transient mutation. The outputs and other recorded checks remain
point-in-time evidence, not an adversarial race guarantee.

RSS and free-space checks were sampled; RSS covers the leader, not the whole
process tree, and no hard quota or continuous reservation is implied. The
independent fake-process controls establish only the tested leader and
same-group descendant cleanup cases. Package-transitive and dynamic provider
ancestry remain inherited, and the original Foundation wrapper outer exit
was not captured. The earlier failed attempts and their actual exit
distinctions remain retained in the author packet.

`CHECK.json` records the matching-row digest, exact object counts, parent
links, manifest observation and sampled peaks; `terminal-observation.json`
binds the observed audit exit to the receipt. Re-run while the original
temporary outputs and provider remain available:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary12-current-denominator-independent-audit/audit.py
```
