# Represented literal control iteration and blank binary halting

`ArithmeticControlRun254.lean` proves an all-internal halting equivalence
between the actual blank binary evaluator and a represented interpreter of the
actual source-derived numbered control program. It uses the checked concrete
step simulation and the existing exact bootstrap. It does not identify that
interpreter with the all-internal L2/Enum scheduler.

The iterator is one fixed `PR.Blueprint 1`. Its parameter is the initial coded
control state, its zero case returns that parameter, and its successor applies
`ArithmeticControlStep254.stepValue` to the previous result. A fixed Sigma1
graph is uniquely total at every internal `IΣ1` time and initial code; a total
Delta1 graph and exact zero, successor, additivity and zero-absorption laws are
also proved. The graph argument order is output, time, initial.

For every external catalogue index and arbitrary internal nine-field file,
spare count and gap, `halts_iff_entry` equates zero of this iterator with binary
stateCode0 from the exact corresponding whole entry frame. It instantiates the
previous positive-clock transport theorem with the concrete `Related` step and
halt contracts. Activity excludes a premature binary halt at every matching
frame. Positive clocks reach beyond any proposed binary halting time, while
whole-configuration halt absorption handles intervening time. No upper bound
on register growth or additional execution assumption is needed.

Valid control keys remain essential. The interpreter's total invalid-input
policy also returns zero, but the initial relation admits only actual numbered
controls and its checked live-step contract preserves that validity. The
transport therefore uses the actual halt opcode4 rather than the default
invalid opcode0. All arithmetic register values, count/gap witnesses and clocks
may be nonstandard model elements.

The blank binding is exact. External finite tuple induction proves that packed
file0 has nine zero physical fields. The empty initial PC is recanonicalized by
the existing walk/resolver theorem at clock0; this is a whole-configuration
equality, not a positive executed source instruction. The resulting entry has
spare count56 and gap0 and equals the existing closed `bootCode`. The earlier
82,552-step bootstrap and arbitrary-prefix halt equivalence then give
`halts_iff_blank` without replaying any bootstrap or site check. The initial
logical state is `liveValue 1 0`; it is distinct from the Enum scheduler's
encoding convention. The externally fixed tuple induction does not introduce
an internal variable-length list.

The pinned Lean 4.32 source and audit passed on their first attempt in
3.430852s and 2.385916s: 16 ordered axiom probes, 18 caller examples, standard
axioms only and zero warnings. The check reused 87 matched project source/object
providers and six external boundaries, hashing 200 inputs before and after.
The fresh object also remained unchanged after the audit. Actual first Init
and Omega providers were validated. No dependency build, coverage replay or
82,552-step bootstrap replay occurred.

Three exact prerequisite records supply the concrete simulation, generic
positive-clock theorem and machine-prefix theorem. Their shared Cantor source
has two already checked object variants. The simulation's object is selected;
the older positive-clock record's source-equal object is explicitly unselected
and still hashed before/after as provenance. It is not silently substituted
for the selected provider. The original preparation, successful record,
source/audit/driver snapshots and header-only prebuild cleanup are archived
separately. There were no failing proof attempts in this checkpoint.

A focused replay uses the frozen prerequisite records and matching objects:

```sh
python3 Computability/BusyBeaver/Research/ZFC/check_arithmetic_control_run254.py \
  --repo /path/to/Proofs \
  --dependency-root /path/to/built/Proofs \
  --simulation-evidence /path/to/arithmetic-control-simulation254-verification.json \
  --positive-evidence /path/to/arithmetic-positive-simulation254-verification.json \
  --prefix-evidence /path/to/arithmetic-machine-prefix-perm252-verification.json \
  --output /outside/new-empty-directory
```

`--prepare-only` validates providers and snapshots without source/audit
compilation; compiler-version discovery may run. `--cache` may relocate the
selected project objects, while `--alternative-cache` may relocate the
explicitly unselected Cantor variant. Every selected or inherited variant must
match its recorded hash. External library providers are selected from the
built dependency root. Nothing is downloaded or rebuilt. The portable driver
is byte-identical to the executed successful driver. The maintained-default
preflight is recorded as unbuilt; redundant rejection/relocation controls were
explicitly waived and are not claimed.

The remaining semantic task is the all-internal connection from this actual
numbered interpreter to the L2/Enum scheduler. The scheduler already has a
separate checked numerical proof-checker equivalence; transporting it requires
this further connection. The ordinary natural-number program correspondence
alone does not establish it for nonstandard register values or times. This
checkpoint proves no whole binary/validator equivalence in PA, new consistency
endpoint, calculus reduction or machine-state improvement.
