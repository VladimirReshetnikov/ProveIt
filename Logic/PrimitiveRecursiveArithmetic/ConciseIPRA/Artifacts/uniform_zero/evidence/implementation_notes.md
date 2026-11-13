# Frozen packet-research deliverables

The seven selected standalone checker files are `code/control_compact.py`,
`code/control_explicit.py`, `code/checker_zero_compact.py`, `code/checker_zero_explicit.py`,
`code/checker_constructed_compact.py`, `code/checker_constructed_explicit.py`, and `code/checker_readable.py`.
All source is counted; none imports a producer or theorem library.
`evidence/metrics.json` contains hashes and all measurements, and each checker
has a maximum-compression `.py.gz` companion. Interpreter: CPython 3.12.14;
zlib 1.3.2. Gzip is FYI only, with `compresslevel=9,mtime=0` and wrapper counted.

| Family | Compact bytes | Explicit-list bytes | Compact tokens | Compact AST | Compact gzip9 |
|---|---:|---:|---:|---:|---:|
| Matched old |545|553|267|311|336|
| Zero only |550|558|269|314|338|
| Constructed majors |556|564|272|314|341|

The old supplied record is 558 bytes, but the fairest matched old control is 545.
The thirteen-byte implementation reduction consists of already available
lexical scopes, an empty default context that is never mutated, the inherited
invalid missing-image sentinel 0j, and Boolean hypothesis dispatch after using
supported non-null false markers. The new zero normalization then costs 5
bytes. Constructing majors adds a further 6 bytes. Consequently the positive
new result is certificate efficiency, not a reduction attributable to a new
arithmetic foundation. The new 550-byte checker beats the literal supplied
source record, while losing to its fully matched old control.

The zero-only new numerical codec uses 1 for zero everywhere. Instruction
flags remain 0 or []. The opener maps any retained falsy scalar to 1; the reserved
coordinates 0, 1, 2 all already have numerical meaning zero. Canonical terms are
therefore truthy: zero 1, negative scoped parameters, and nonempty S/I arrays.
This recoding removes the need for nonempty-zero seed/predecessor repairs.
Zero witnesses are ordinary truthy encoded numerical data. It changes no
mathematical arithmetic operation or axiom.

Constructed-major packets have four fields [m,s,u,t]. With truthy m, truthy s
constructs the equality [s,u]; otherwise truthy t constructs the closure [t]*3;
otherwise the supplied m is checked (canonical use is D elimination). Equality
source 0 is encoded 1, so source truthiness does not exclude that case. The
major is checked before any goal change. If opening t at u matches the goal,
the continuation proves t opened at s; in the Q case the source flag 0 is
normalized by the opener to the numerical zero 1. A false template can only
match a truth alias, so the residual-major branch causes no meaningful
unjustified transport. Case and progress introductions retain the inherited
literal-equation restriction and eigenparameter condition.

`tests/test_profiles.py` imports only the untrusted symbolic producers and
runs the complete checkers as separate processes. Required producer files are
`tests/producer_old_local.py`, `tests/producer_zero_only_local.py`, and
`tests/producer_zero1_local.py`. The generated fixtures are in `examples/`.
The test receipt is `evidence/validation.json`.

The run passed 504/504 expectations in ordinary and optimized Python across
all seven checkers. There are 19 named native cases per family, ten additional
positive/negative controls, and seven malformed-input controls, each replayed
in both modes. Controls include false goals, wrong computation targets,
forbidden compound progress, future-name capture in goals, invalid witnesses
and Q targets, missing updates, malformed records, and harmless unused prefixes.
Two deliberate mutations were checked in both modes: removing major-proof
verification admits an explicit false 0=1 transport proof; removing the
literal-equation guard admits the forbidden compound-progress certificate.
All four mutation checks behaved as expected. These are finite tests, not a
formal proof of universal soundness or bi-interpretability.

Across 16 named successful non-neutral proof examples, old certificates total
120 commands and 5029 compact JSON bytes; zero-only totals 90/3801; constructed
majors total 90/2955. Thus the selected examples save 25% of commands and 41.24%
of serialized bytes against the matched old encoding. These percentages are
sample measurements, not universal bounds. The contextual induction example
is 48 commands/2359 bytes old, 40/2012 zero-only, and 40/1437 constructed. Direct
zero-base and zero-predecessor computations each shrink from 3 commands to 1.

No generic exception-traversal profile is needed in the final deliverable.
The compact list predicate `a*0==[]` is valid for successfully handled exact
JSON built-in values; the recommended explicit-list companions make that
intent clear. The 0j default is deliberately not a JSON term and raises on a
used missing numerical replacement, just as None did. Input is never executed
as Python code. Successful verification means exit status 0 and exactly ACCEPT.
