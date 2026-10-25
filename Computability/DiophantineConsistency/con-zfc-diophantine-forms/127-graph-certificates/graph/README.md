# Graph constructions with coefficient height one

Every profile supplies a complete sparse integer polynomial and its finite
certificate. All variables range over all integers. Every nonzero coefficient
is +1 or -1, the constant coefficient is one, and total degree is four.

| Profile | Source variables | Final variables | Monomials | Largest individual degree |
|---|---:|---:|---:|---:|
| `principal` | 442 | 2,215 | 30,468 | 4 |
| `matched519` | 519 | 2,776 | 30,554 | 4 |
| `matched519_no_square` | 519 | 2,988 | 31,218 | 2 |

The incoming height-one construction on the same 519-variable source had
7,431 variables, 34,086 monomials, total degree four, and individual degree
at most two. The third profile improves its variable and term counts while
retaining those degree bounds. The second permits individual degree four
to save more variables. The principal profile also uses the newer literal
442-variable source. These distinctions should be kept when comparing gains.

`PROOF.md` proves the graph-flow and alias lemmas. `SOURCE_PINS.json` fixes
the exact source equation bytes and archive provenance. The inherited
arithmetic and C222/ZF/ZFC calibration is supplied elsewhere in this release;
the graph compiler alone proves an exact correspondence of zero sets.

## Format

`polynomial.json` contains all monomials as `[coefficient,[indices]]`, with
zero-based variable indices and repetitions denoting powers. The empty index
list denotes the constant term. `certificate.json` supplies every normalized
source row, graph edge, factor assignment, alias class, and unit path.

The polynomial is mathematically defined by the complete sparse JSON. The
descriptive variable metadata and metrics make the representation auditable;
they do not introduce additional unknowns or coefficients.

## Exact checks

From this directory, run the independent verifier separately on each profile:

```sh
python3 -B verify_graph.py --source sources/source442.json --artifact-dir principal --mutations
python3 -B verify_graph.py --source sources/source519.json --artifact-dir matched519 --mutations
python3 -B verify_graph.py --source sources/source519.json --artifact-dir matched519_no_square --mutations
```

The same commands work with `-O`; the checks use explicit exceptions. The
verifier imports neither producer. It checks each normalized row against the
literal source, all alias provenance, both simple-graph invariants, every
connected free tree, all equality and unit constraints, every coefficient by
expanding twice the polynomial as a sum of squares, and all reported counts.
It also rejects eight deliberately corrupted artifacts. Finite diagnostics
are distinct from the ordinary unbounded proof and its inherited calibration.

For an exact, network-free rebuild of all profiles:

```sh
python3 -B rebuild.py
```

The rebuild uses temporary directories, compares every generated polynomial,
certificate, metrics file and compression summary byte for byte, and preserves
the release files. Python's standard library is sufficient.

`build.py` first constructs the graph and one private alias per occurrence.
`compress_aliases.py` then reuses aliases according to a C4-free factor graph,
keeping square-loop aliases separate. `verify_graph.py` is the independent
checker. `receipts/` contains the recorded normal and optimized checks.

No optimization search here establishes a global minimum. The result does
not assert that any supplied equation has no solutions.
