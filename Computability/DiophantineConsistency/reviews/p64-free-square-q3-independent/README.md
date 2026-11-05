# Independent check of the q=3 nonsquare norm obstruction

The reviewed [author packet](../../research/p64-free-square-q3-obstruction/README.md)
claims a partial solution of the q-cube coordinates, transport equation and
two scalar norms with `h` nonsquare. An independent exact check uses binary
powering in `Z[sqrt(12099)]` instead of the author's 12,099-step recurrence,
then verifies nonsquareness by integer square root instead of its mod-7
certificate. It checks the pinned author's script and result hashes, the
coordinate relations and positivity, transport, both norm equalities, and
the strict gap between consecutive squares.

The check exits 0 and records a 94,139-bit `c`, a 376,541-bit `h`, and
`h mod 7 = 6`. Its deterministic result includes a SHA-256 hash of `h` in
unsigned big-endian encoding. The independent checker caps intermediate
binary-power operands at 200,000 bits. Its result does not rely on printing
the enormous integer.

The scope is partial: this does not verify the actual graph residual `M=0`,
the first norm, the auxiliary unit equation, or a full graph zero. It is not
a counterexample to a graph-specific square theorem or any existential iPRA
equivalence. No Lean proof or provider audit was performed.

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/p64-free-square-q3-independent/check.py
```

| Artifact | SHA-256 |
| --- | --- |
| `check.py` | `9378454e11db33185d8ab49559119dd215c09132288aebc2185a8922122998f6` |
| `result.json` | `d70f0013bc0580521c5359d53fe8c2f8ef02ca30bf6c6eb2a5ca4fe0775a35ad` |
