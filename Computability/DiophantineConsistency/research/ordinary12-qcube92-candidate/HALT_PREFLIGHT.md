# Fixed-port halt join: historical provider preflight

This records the earlier preflight state. A later selected-project ancestry
audit and a successful namespaced halt build are documented in [HALT.md](HALT.md).

The drafted `QCube92Halt.lean` composes the 92-to-95 positive-zero theorem
with the existing fixed-symbolic model-halt theorem. It also proposes shifted
natural-witness and closed Lean byte-recipe versions. **At the time of this
preflight the file had not passed Lean.** A later version passed in the
namespaced build linked above.

The first selected-union preflight failed before launching Lean. The
92-proof author search path included an object named
`FreeJOrdinaryTailWitness.olean` with SHA-256
`b36cc3c0c13c6aba7538ec3587933b816907706432cb38d8419391f8799474fe`,
while the earlier 1,288-file fixed-port model union selects the same-named
object with SHA-256
`3af9bb5c54c1fda2d7ea0daf22e43c4fe02176b5eda32a345b45ded73024304e`.
The exact preflight runner, error and nonzero exit are retained under
`observations/halt-preflight01/`. This is a provider-path overlap, not yet a
shown incompatibility in the new proof’s actual import ancestry.

The new 92 ring proof directly imports `FreeJSumSquares`, which directly
imports `FreeJCompletenessFactorBridge`; that bridge's source declares only
`DiophantineConsistency.Ordinary12FreeJ`. The differing tail object was on a
search path in the 92 author runs, but these source statements alone do not
exclude it from serialized transitive ancestry. The subsequent serialized-import audit excluded the tail from the new proof’s
selected-project ancestry. The checked namespaced join uses the halt model’s
selected tail object. Package-transitive and dynamic ancestry remain separate
boundaries.
