# Typed-color bounds for both row tables

`DirectBFSColorBounds.lean` proves, by kernel reduction without axioms, that every row of both the retained-original and direct-BFS Lean tables has west/east color <250 and north/south color <439. These separate all-row facts ensure the candidate array-based renaming cannot silently rely on a default for an out-of-range tile color. They do not prove the candidate arrays are permutations or the rows match.

The guarded author check `observations/directbfscolorbounds-attempt01/` exited 0 without diagnostics. Its object `/tmp/direct-bfs-colorbounds-7y9sdrzg/DirectBFSColorBounds.olean` SHA-256 `95ee661ab88e807316aeaa714e16beb40c90b057397437994f40963ff2ea561e`; direct import pins/resources are recorded. Inherited transitive ancestry and independent Lean replay are outside scope.
