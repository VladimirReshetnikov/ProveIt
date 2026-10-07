# Report193: offline exact checks and interval certificate

Python 3.12 or later, standard library only. No package installation, network,
TeX, SciPy, mpmath, or ordinary floating-point special-function calculation is
part of this mandatory replay. Run from any directory, with a new output path
whose parent already exists:

```
python -I -S -B /path/to/code/reproduce.py --output-dir /path/to/new-results
```

The command runs every check in isolated ordinary and `-O` Python processes,
compares all eight generated files byte for byte, and only then publishes the
results. Output paths must be fresh, outside this `code` directory, have no `..`
components, and have existing nonsymlink directory ancestors. Existing paths,
dangling links, symlinked inputs/parents, unknown source files, empty extra
directories, modified fixtures, duplicate JSON keys, and nonfinite JSON
constants are rejected. Sources are checked against `PROVENANCE.json` before
and after execution. The command never overwrites an existing file/directory.
Interrupted publication may leave an incomplete new directory; use another
fresh destination for a retry. Ordinary operation never writes into the source
bundle or creates bytecode caches. Supply `-B` when importing these modules in
your own programs as well.

## What the replay establishes

- `check_exact.py` recomputes polynomial rows through 30; compares them with
  independently decoded, exhaustively enumerated Prüfer trees through 6;
  checks coefficient positivity, Cayley leading coefficients and a one-child
  coefficientwise lower bound; verifies finite towers at six positive rational
  shifts against independently expanded formal exponentials through height and
  degree 10; checks scaled integer coefficients through 30; and verifies 17
  explicit rational inequalities used in the analytic tail estimate
- `test_intervals.py` performs 20,008 deterministic rational inclusion and
  normalization checks. These include independent rational Airy-basis series,
  alternating arctangents, real/complex derivatives, gamma integer values,
  exact square comparisons, and ambient-Decimal rounding traps in proof-valued
  kernel and panel evaluations
- `test_guards.py` checks rejected numerical domains, constructor misuse,
  unsupported powers, negative arctangents, corrupt provenance/fixtures,
  unsafe paths, and modified panel/core schemas. All guards use explicit
  exceptions and remain active under `-O`
- `certificate.py` starts from the 64 initial panels on `[0,3.2]`, adaptively
  recomputes the core to width at most `0.08`, and reproduces all 562 terminal
  panels and the frozen enclosure. It then recomputes every terminal panel
  again, verifies exact rational coverage without gaps or overlaps, and sums
  endpoints independently using `Fraction`. It adds the separately proved
  absolute tail bound `0.141` and computes the positive prefactor with directed
  arithmetic. The resulting coefficient is strictly negative and lies inside
  `[-0.61,-0.25]`

The panel verifier is independent of adaptive scheduling and running-total
bookkeeping; it reuses the same interval/kernel/panel implementation. This is
not an independent implementation of the entire numerical method. Reference
JSON files are regression targets, never substitutes for recomputation.

## Mathematical and implementation trust boundary

The code does not prove the infinite-family asymptotic theorem, the real-integral
identity, contour deformations, or the analytic tail theorem. Their proofs are
in Report193. Exact finite checks are tests of finite identities, not proofs
for all orders. In particular, the rational tail checks verify the rounded
arithmetic inequalities after the analytic estimates have been established;
they do not evaluate the infinite tail or prove those estimates by themselves.

The interval calculation uses precision-70 directed `decimal.Context`
operations. It trusts Python's documented correctly rounded `sqrt`, `ln`, and
`exp`, padded by outward adjacent representable values, and the Python
integer/Fraction implementation. It also uses the real Stirling signed
first-omitted-term gamma bound, convergent Airy power-series remainders,
nonnegative-axis Airy monotonicity, positive-argument arctangent identities,
and the midpoint `sup|f''| * width^3 / 24` error bound. These mathematical inputs
are explained in the report. This is a reproducible numerical certificate
under those assumptions, not a machine-checked proof of Python or libmpdec.
The 70-digit working precision is not a claim of 70 correct digits in the
coefficient. The certified interval is deliberately broad.

The public numerical helpers accept exact integers, strings, Decimals and
specified Fraction inputs; binary floats, booleans, nonfinite values,
constructor ambiguity, unsupported exponent types, and out-of-domain calls
are rejected. Positive-real Airy evaluation is restricted to `[0,9]`, and panel
integration to positive-width subintervals of `[0,3.2]`. Heap priorities use
context-independent negation. The tested certificate uses the fixed contexts
as distributed; deliberately modifying those contexts is outside this replay.

`PROVENANCE.json` records the complete allowed source inventory, lengths and
SHA-256 hashes. The fixtures additionally have pinned hashes in
`certificate_io.py`. Hashes detect modification relative to this bundle, not
an attacker replacing both code and hashes. Authenticate the enclosing release
or its separately received digest if provenance authentication is needed. The
reader's Python installation, operating system, and source directory must be
trusted; file checks reduce accidental/path-based misuse but do not implement
a hostile concurrent-filesystem sandbox. No source paths, private research
logs, timestamps, elapsed times, cache files, or optional numerical diagnostics
are included in generated success receipts.

For development, `integrate_core.run()` returns a core object and a sorted
panel list; it performs no file I/O. `certificate_io` provides reusable strict
I/O and provenance checks to an enclosing deterministic report builder. There
is no PDF/ZIP build step in this subtree.
