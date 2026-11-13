# Fixed symbolic direct-BFS 80-row iPRA client

`DirectBFS80FixedIPRA.lean` specializes the parameterized direct-BFS 80-graph client to the concrete Lean tuple `ports betaNat (DirectBFSSymbolicKernel.paramKernel rho) lowNat highNat` using generic finite-port projections. Lean checks four **assumption-free derivability statements** for this symbolic tuple: the standard-theory and equality-only reference-theory versions, each with both the negated mapped refutation predicate and the negative-translated source consistency sentence. The exact iPRA axiomatization and translation are those in the imported adapters; the no-zero sentence uses the adapter's positive-variable shift.

Accepted exploratory author check: `observations/directbfs80iprafixed-attempt01/`, with the separate outer supervisor receipt `observations/outer-attempt01/`. Lean, the inner runner and outer supervisor exited 0; no diagnostics were reported, and all four axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Output `/tmp/direct-bfs-80iprafixed-df6_j_mk/DirectBFS80FixedIPRA.olean`, SHA-256 `2155f5f05a8e993dc3582f3c14ce9c56916d0ac09dc326c02093d83a878e4703`. Direct imports and selected objects were pinned and rechecked. The supervisor records its own, the runner's, and the source's hashes before and after execution, the actual outer exit, and outer log hashes.

This is **not yet a fully audited coherent end-to-end source build**. Full serialized transitive closure, historical source-to-object and package-transitive ancestry, and dynamic dependencies remain to be audited; no independent Lean replay is claimed. The literal retained 80-row JSON/gzip coefficient and the symbolic Lean K have external byte/recipe evidence but no Lean equality in this packet. This is not the distinct trace75 graph or the original 14-variable PDF.

A later [selected-header scan and reconciliation](../direct-bfs-80-ipra-serialized-audit/README.md)
captured 1,795 project objects and found that all 739 previously captured BFS
forward objects and companions match. Compared with the separate 127-stage
rebuilt original-kernel union, 1,627 project objects match, 166 are absent,
and the selected `.olean` hashes differ for `ArithmeticNegativeNorms` and
`ModelRatioBounds`. The fixed BFS client therefore cannot be claimed to have
been built on that other union. The scan does not authenticate full historical
source/object, package-transitive or dynamic ancestry, or replace a coherent
rebuild. An [independent audit](../../reviews/direct-bfs-80-ipra-serialized-independent/README.md)
rechecks the captured reachability, selected objects and the two differences,
without replaying Lean or authenticating the remaining provider history.
The subsequent [producer-drift review](../../reviews/direct-bfs-producer-drift-independent/README.md)
checks the recorded producer-time dependency differences and the captured
rebuild cone. It does not assert unique producer identity or prove unsoundness.

The [65-stage selected-union replay](../direct-bfs-80-coherent-rebuild/README.md)
subsequently rebuilt that captured affected cone on the 127-stage base and
rescanned 1,795 selected project and 80 outside objects. Its recorded inner
runner exited 0 and its result is PASS; all 65 output `.olean` bytes match the
previous selection. An [independent post-check](../../reviews/direct-bfs-coherent-attempt-postrun-independent/README.md)
verifies the stages, selected dependencies and closure without replaying Lean.
The actual outer-wrapper exit was not separately captured. The 127-stage base
and 101 supplemental objects are inherited, as are remaining historical,
package-transitive and dynamic ancestry; Lean does not bind the external
coefficient files here.

A later selected-header comparison found **concrete producer-time direct-dependency drift** for the selected `ArithmeticNegativeNorms` and `ModelRatioBounds` objects. Their historical producer records use four direct dependency object hashes that differ from the objects selected by this client. The captured affected cone and proposed fresh rebuild are documented in [`../direct-bfs-80-coherent-rebuild-plan/README.md`](../direct-bfs-80-coherent-rebuild-plan/README.md). Consequently the accepted exploratory check should not be described as a coherent end-to-end source replay.
