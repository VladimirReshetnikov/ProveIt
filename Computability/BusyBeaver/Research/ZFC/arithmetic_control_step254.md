# A represented step of the numbered literal control program

`ArithmeticControlStep254.lean` defines a fixed nine-register coded state and a
single arithmetic control step, using the actual source-derived columns from
`ArithmeticControlData254`. Every arithmetic input may be internal to an
arbitrary `IOpen` model. The module supplies fixed parameter-free Sigma1 graphs,
a total Delta1 step graph, and exact equations for the coded cases. It does not
prove a binary simulation, represented run, or internal L2/scheduler equivalence.

The tuple helper has an externally fixed arity. Nine registers use eight nested
Cantor pairs; register8 is the remaining tail itself. Both roundtrips hold for
every code and every tuple of internal values, without a trailing-zero validity
premise. The generic helper does not encode an internal variable-length list.
Fixed finite selector and write graphs then implement the nine physical fields.
Out-of-range selectors return zero, and an out-of-range write preserves the
fields. The selected register is read before its update.

The live-state code is `P(control,file)+1`; zero is absorbing halt. Every
positive state reconstructs from the two projections of its predecessor, under
an explicit nonzero premise. Positive state1 encodes control0/file0, so it is an
invalid control rather than an absorbing state. The canonical first catalogue
control has live key1; with nine zero registers it is represented by
`liveValue 1 0`. This is separate from the Enum scheduler's initial encoding.

The actual opcode, physical-selector and successor columns share one proved
catalogue index. Inc adds one to the selected physical register. Dec truncates
by one and chooses its successor from the old register's zero/nonzero value.
Break/continue use the control-only opcode and preserve the register file.
The next column's branch convention is zero versus every nonzero internal value.
Non-Dec source rows give the same successor in both columns.

Actual halt opcode4 returns the absorbing state. Invalid/absent opcode0 also
returns zero as an explicit total-function policy. These remain separate opcode
facts. Later binary simulation must require a valid source control; a zero
step result from an arbitrary invalid input cannot establish that the actual
binary program halted. The audit includes literal absent control0 without
assuming its opcode as a premise.

The fixed tuple, projection, selector, update, state and transition graphs use
unbounded Sigma1 intermediate witnesses. No composition is incorrectly claimed
to remain bounded merely because its ingredients have bounded graphs, and a
rejected output0 places no spurious bound on intermediate values. The final
step has unique total output and a total Delta1 graph in every `IOpen` model.
All numerical inputs, including invalid controls and selectors, are covered.

The pinned Lean 4.32 check passed the 333-line source in 17.321822s and the 103-line
audit in 3.223714s: 27 ordered axiom probes, 30 callers, standard axioms only and
zero warnings. It reused 82 exact project source/object providers and six external
boundaries, with 187 input files checked before/after. The fresh object also
remained unchanged after the audit. No dependency build, guard/coverage replay,
or 82,552-step bootstrap replay occurred.

One failed source attempt is preserved. Fixes removed an incorrect selective
namespace open, relied on Lean's automatic generalization of dependent tuple
variables, made `Fin.cases` and conditional reductions explicit, and unfolded
the fixed nine-field pack to normalize the formula-vector argument. An unused
simp argument was also removed. No function, graph definition or theorem
contract changed. The original preparation, failed attempt, successful record,
source/audit/driver snapshots and proof-only diff are archived separately.

A portable focused replay uses existing matching objects:

```sh
python3 Computability/BusyBeaver/Research/ZFC/check_arithmetic_control_step254.py \
  --repo /path/to/Proofs \
  --dependency-root /path/to/built/Proofs \
  --control-evidence /path/to/arithmetic-control-data254-verification.json \
  --output /outside/new-empty-directory
```

`--prepare-only` performs provider validation and snapshots without source/audit
compilation; compiler version discovery may run. Optional cache/library paths
are accepted only when the actual selected objects match the recorded hashes.
No dependencies are downloaded or rebuilt.
The maintained-default preflight passed without proof compilation. Four controls
rejected optimized Python, nonempty output, and shadowed first Init/Omega
providers. These are metadata/preflight failures, not logical counterexamples.

The next concrete theorem must relate the coded physical file and fixed PC
column to the checked whole binary frame, preserve valid controls on live steps,
and use the actual halt site's contract. A represented iterator can follow.
The further all-internal relation to the actual L2/Enum scheduler remains a
separate obligation. This checkpoint supplies no new machine bound, calculus
reduction, PA consistency endpoint, or whole binary internalization.
