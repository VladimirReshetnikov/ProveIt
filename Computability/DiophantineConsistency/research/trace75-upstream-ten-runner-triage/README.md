# Ten positional-pin runner records

This read-only triage covers the ten remaining candidate receipts identified
after the [19 named-import checks](../trace75-upstream-19-provenance/README.md)
and the separate [ScaledOffsetGeneric check](../trace75-upstream-scaled-offset-provenance/README.md).
It finds, for each receipt, the unique current prototype runner file matching
the recorded runner hash; checks the recorded producer output realpath,
source copies, logs and unchanged recorded pins; then parses **only** a small
allowlisted Python AST grammar to reconstruct that runner's positional
`extra` path list. It never executes the historical runner or invokes Lean.

The ten sources have 18 explicit direct imports. For 17, the path selected
**now** under the receipt's recorded `LEAN_PATH` is exactly a path in the
reconstructed positional list, and its current `.olean` hash matches the
corresponding recorded before/after positional hash and the final selected
hash. For the remaining import,
`CarrierSizes` → `DiophantineConsistency.ArithmeticPellPowerRecovery`,
the current first path has the final selected hash but is not named by the
positional path list; it is resolved through the broad provider. Complete
paths, positions and hashes are in attempt03 stdout.

This is **current path reconstruction**, not a captured producer-time direct
import record. A path or namespace could have changed between the historical
run and this check. Positional `.olean` pins do not establish all companion
bundles, implicit `Init`, upstream source/object history, package-transitive
or dynamically loaded inputs. The one broad-provider import is not promoted
to a pinned named edge. No change to the final endpoint's ancestry or
external-file boundary is claimed.

Author attempt03 exited 0. Checker SHA-256 is
`4221feae3c636a5b6f33a469c7f3116ccb8158e799424ce37bd03f389cf11e85`,
terminal SHA-256 is
`54b54364f4e6521ee0d5e471bde24d0bd8dfab7b4bb8839a34d9708577d79ed0`,
and stdout SHA-256 is
`d31977de4a6c5c724f52c9b43a1caeb173a2a979a5834ab8c68b87ee4aa3a7be`.
Eight isolated parser/path-policy controls passed, with terminal SHA-256
`3ddba4a4bd319e3c44149d9599685a2de609353a134855820ee9cbfc82ff69bc`.
Those controls test the scanner's policy, not Lean's loader or historical
filesystem state. Attempt01 failed because the parser did not yet recognize
`extra.append`/`extend`; attempt02 passed after adding them, and attempt03
added a guard against modifications after the recorded pin construction.
All three attempts and their source snapshots are retained. The
[independent static audit](../../reviews/trace75-upstream-ten-runner-triage-independent/README.md)
reconstructed the lists and checked the top-level-only parser limitation; it
did not authenticate historical path choice or transitive ancestry.
