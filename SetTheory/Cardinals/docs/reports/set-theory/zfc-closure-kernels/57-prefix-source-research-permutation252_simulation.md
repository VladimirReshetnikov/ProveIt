# Clean paths and whole-tape framing for permutation252

The new [RegisterPathClean.lean](../../Lean/BusyBeaver/ZFC/RegisterPathClean.lean)
proves `step_clean`: every successful path-machine step produces a path whose
bits at and beyond the depth of any subsequent successful decoder walk are
false. The result applies to every `RegisterPath.Program` and arbitrary
register values. It requires neither a well-formed program nor an initially
clean path. `run_clean`, `no_stray_bits`, and `no_stray` give the corresponding
property after any finite run from the empty path.

The argument follows `ZF/m254/coq/tm/RMEquiv.v`, especially lines 585–700,
at the attributed upstream commit
`297ab8df7e5de329605c3875b4934643b371a5e3`: Mira-Cult's machine, Jeff's
verification, and Wade's compiler framework. The Lean proof treats increment
overflow exactly: the result is an all-false path of the original length.
The successful-walk premise is material. These theorems do not establish
decoder termination; well-formedness or concrete coverage must supply it
separately.

`gap_consume` proves the complete finite-region identity

```text
P ++ 0^gap = consume P d ++ 0^(P.length + gap - d).
```

Its assumptions are `d ≤ P.length + gap` and that every bit in `P.drop d`
is false. The depth may exceed the stored path length: `consume` then takes
the missing zeros from the existing gap. `reachable_gap_consume` obtains the
clean suffix from an actual finite path-machine run. No physical cell is
discarded.

[Permutation252Simulation.lean](../../Lean/BusyBeaver/ZFC/Permutation252Simulation.lean)
connects this identity to the actual candidate's symbolic checker.
`source_represents` turns a whole-tape dispatch frame into its symbolic
source at parameter `n = P.length + gap - 40`, using an exact consumed prefix
of length at most 40. It preserves arbitrary blank exterior padding and the
entire physical file `vregs R ++ spares`.

`target_frame` turns a symbolic target into another complete dispatch frame,
given an exact equality for the updated physical file and the updated
logical zero-tail condition. The effect lemmas prove those equalities for
unchanged, increment, and positive-decrement outputs. Positive decrement
preserves the old spare suffix and appends one zero block. An overflow target
has one additional marker-to-header cell. Physical spares, including the
nonzero spare in the actual blank bootstrap, remain distinct from the
zero logical register tail.

Both modules passed scoped serial source checks with the pinned Lean
4.32.0 compiler. Thirty-one axiom audits and six callers passed; their axiom
union is `propext` and `Quot.sound`. The callers include a consumed depth
strictly beyond the stored path length, an arbitrary reachable-path source
frame, a named permuted zero guard, positive decrement's spare extension,
and an overflow target. Eighteen unchanged dependency modules were reused;
the expensive boot and box checks were not repeated. The complete commands,
source fingerprints, caller source, and axiom output are in
[the verification record](results/permutation252-simulation-verification.json).

These are framing and path-cleanliness results. They establish no all-site
coverage certificate, general binary instruction simulation, halting
equivalence, or ZFC consistency equivalence by themselves.
