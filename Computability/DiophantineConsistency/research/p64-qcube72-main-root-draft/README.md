# Main Pell root and index from an actual 72 zero

[`FreeMainGraphMainRoot.lean`](FreeMainGraphMainRoot.lean) passed its guarded
[Lean check](observations/attempt01/result.json). In every `IΣ₁` model, for
any natural ports and positive 72-graph zero:

- `main_root` constructs a natural `g` satisfying the main Pell norm and
  retains the carrier equality `U g=U(X+a c)+H h`.
- `main_index` classifies that root with an index `m`, yielding the exact
  `xcoord m a=g` and `ycoord m a=c` equations together with the same carrier.

Both declarations reported `[propext, Classical.choice, Quot.sound]`; Lean
exited 0, no warnings or `sorryAx`, stable direct guards, and no monitor stop.
The object SHA-256 is
`2429ba1307bde7a83ca68110773cd073825ba5f1d1ee0e1dd59dbbf8dc8d7930`.
The comment “unchecked draft” predates this check and is retained to match
its pinned source. Captured direct providers are authenticated as in the
receipt; their transitive, dynamic, and between-sample ancestry is inherited.

The proof constructs the scaled quotient from the actual main residual and
uses the existing `ArithmeticPellClassification.solution_index`. It does
not prove the additional large-c hypothesis of the signed half-index theorem,
identify `m` with the rank `R`, recover the first-index congruence, establish
a reverse witness map, or give a 72 iPRA endpoint.
