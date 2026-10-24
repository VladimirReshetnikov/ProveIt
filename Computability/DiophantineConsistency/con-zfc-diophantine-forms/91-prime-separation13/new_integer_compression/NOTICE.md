# Provenance and license

`circuit.py` is copied from the incoming ProveIt package
`con-zfc-radical-residue-2026-10-23/integer/circuit.py`. It supplies a small
standard-library arithmetic-DAG implementation. Its original MIT No
Attribution license is included as `LICENSE`.

The six coefficient payloads and their original binding record are copied
unchanged from that package's `integer/coefficients/` directory. They are
the full source-34 tuple and source-71 determinant scales, not newly chosen
or incompletely specified numerical ports. Their original internal source
path identifies the upstream package's binding ledger.

`build.py`, `check_degrees.py`, and `PROOF.md` are new AI-assisted research
work in this iteration. They are offered under the same license. The
coefficient-based construction is deliberately separate from the compact
optimized evaluator so that exact finite-field comparisons can check the
two implementations independently.

No mathematical provenance is transferred by copying a program: the
ordinary proof explicitly identifies the inherited compiler, Pell,
canonical-completeness, and syntactic-refutation results it uses.
