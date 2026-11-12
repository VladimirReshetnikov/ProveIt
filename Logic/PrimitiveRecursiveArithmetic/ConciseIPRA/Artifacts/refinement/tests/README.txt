FROZEN EXECUTABLE VALIDATION

The manifest fixtures.json records each input file's SHA-256, source and
protocol. Expected compact and strict verdicts are stored separately.

FOUR-FIELD SUITE
66 fixtures from the pinned incoming three-field archive's four-field
regression suite, plus its separately pinned future-scope attack as already
counted among those 66 cases. Each runs against the compact candidate,
readable candidate, 495-byte compact control, strict candidate, 862-byte
matched strict control, and 869-byte older strict control, normally and -O.
Total: 792 CLI runs. This includes genuine computation, guarded introduction,
equation induction using its hypothesis, transport, compound cases and
specialization; rejected capture/context attacks; raw arity aliases; and
unused malformed JSON prefix data. Compact acceptance of an administrative
alias is not confused with strict acceptance of a public formula.

THREE-FIELD BASELINE SUITE
13 canonical global certificates run against the 249-token profile, and 13
canonical local certificates against the 271-AST profile. Seven adversarial
certificates run against both. Every run is repeated under -O.
Total: 80 CLI runs. These fixtures preserve the distinct global/local fresh
parameter conventions; they are not fed into incompatible checkers.

TWO-FIELD REFERENCE SUITE
Six positive certificates exercise zero and successor computation,
reflexivity, guarded introduction, equation induction with an actually used
hypothesis, and D elimination followed by Q specialization. Seven negative
cases cover a false closed equation, a negative free parameter, an unbound
positive parameter, two unbound computation bodies, and two future-witness
capture attempts with otherwise closed goals. All run normally and -O.
Total: 26 CLI runs.

RECORDED TOTAL
112 distinct manifest entries; 898 isolated CLI executions; zero failures.
The native 643-byte contextual baseline is measured, not re-audited here.

The harness uses isolated subprocesses and exact ACCEPT-line checking.
Timeout, inconsistent output, fixture-hash mismatch or unexpected acceptance
is a test failure. No tests are imported by a measured checker. These finite
tests support implementation confidence; universal soundness, completeness,
and interpretation claims require the mathematical arguments in the report.

TARGETED COMPUTATION-LEAF AUDIT
Run `python3 tests/check_targeted_leaves.py` from the package root, or supply
that script's absolute path from any directory. It imports only the sibling
standard-library-only semantic checker, tests 8,008 fixed combinations of
counter, seed and update spelling, and regenerates
`evidence/twofield_targeted_leaf_audit.json`. The expected result is 3,608
accepted true leaves and 4,400 rejections, with no false equations or exhausted
evaluation budgets. It exits nonzero if those results differ. The evaluator
uses one fixed assignment to its rigid parameter; this finite check does not
establish the mathematical theorem for all valuations.
