# Singular-safe port compression and finite-state multiplicity registers

Research continuation for `ProveIt/Topology/UnknotRecognition`, 8 October 2026.

The 23-page article is in `article/port_registers.pdf`, with its complete LaTeX
source and generated measurement tables alongside it. This package is a research
backend and reproducible evidence, **not a standalone general unknot recognizer**.
No files in the remote ProveIt repository were modified.

## What is proved and implemented

The backend computes exact total homology over F_2 for

```
D = direct_sum(A_nu tensor I_{Omega_nu}) + U V,
```

where each `A_nu` is a small square-zero template, the multiplicity domain is
Boolean words or a supplied deterministic language, and all port coordinates
are represented by exact layered weighted automata. It checks homogeneity and
the entire square-zero identity before returning a homology dimension.

The singular-safe formula is

```
rank(D) = rank(A) + rank(K) - r,
beta(D) = beta(A) + 2*r - 2*rank(K),
```

with `K` having at most `2*r` rows and columns. No inverse of `I + V*h*U` is
assumed. Register reachability and parity contractions build the core without
enumerating the multiplicity domain. Gram matrices are not used as rank tests.

For a **fixed** base, `minimize_ports` finds exactly `rank(D-A)` homogeneous
ports and preserves register widths. It does not find the optimal base.
Decision saturation must reserve the cancellation budget: the sufficient cap
is `min(beta(A), 2*r+3)`, not a fixed cap of three. Tensor amplification can
force the port count to grow; the article proves that obstruction explicitly.

The complexity theorem is polynomial in the complete supplied description,
with no factor exponential in register length. A quasi-polynomial recognizer
still needs a certified, sufficiently fast diagram-to-presentation producer.
That missing constructive theorem is **not** assumed to have been proved here.

## Run without installation

Python 3.10 or later is required. The executed checks used the interpreter
recorded in `data/validation.json`. The runtime has no third-party dependencies.

```sh
export PYTHONPATH="$PWD/src"
python -m unittest discover -s tests -v
python scripts/validate.py
python -m portkh verify \
  examples/connected_singular_40.json \
  examples/connected_singular_40.certificate.json
```

The connected example has `2^41 = 2,199,023,255,552` virtual generators, width
four, one port, a singular scalar core, and total homology dimension two.
It is an abstract algebraic example, **not a constructed knot diagram**.

To replay a binomial-multiplicity example:

```sh
python -m portkh verify \
  examples/binomial_63_31.json \
  examples/binomial_63_31.certificate.json \
  --languages examples/binomial_63_31.languages.json
```

This computes rank-two homology on a domain with `binomial(63,31)` copies.
Changing the example to `binomial_64_32` gives homology zero. Both outcomes use
the same singular-safe algorithm, not a separately hard-coded formula.

The command `verify` is deterministic **replay using the solver**, not an
independently implemented proof checker. The separate dense rank and crossing-
cube audits provide additional checks but are not formal proofs.

## Python API

```python
from portkh.complexes import connected_singular_pair, analyze
from portkh.minimize import minimize_ports

presentation = connected_singular_pair(40)
smaller, report = minimize_ports(presentation)
certificate = analyze(smaller)
assert certificate["homology_dimension"] == 2
assert certificate["topological_verdict"] is None
```

The topological verdict deliberately remains unset. A caller must establish a
valid one-component classical diagram and a trustworthy association between
that diagram's closed Khovanov complex and this presentation before applying
the rank-two unknot criterion. Abstract homology-zero examples are not knot
certificates of any kind.

`portkh.languages` provides deterministic domain counts, masking, and
`analyze_restricted`. The `minimize` CLI operates on the basic full-word format;
a restricted-domain application should retain its separate domain bookkeeping
when using a masked presentation. Do not saturate the padded whole-domain
homology before removing the known uncoupled complementary summands.

The matrix format uses integer rows, with bit zero denoting column zero. Full
schema conventions and commands appear in Appendix B of the article. The CLI
allows large exact decimal integers by disabling CPython's digit guard in its
own process. Importing the package does not change that interpreter setting.

## Evidence and its limits

The packaged run passed **48 unit tests**, many containing seeded loops. The
separate exhaustive audit contains **4,352 binary rank updates**, including
**1,728 singular middle matrices**. The independent cube audit covers **404
signed braid presentations**: 210 knot presentations and 194 link presentations,
not 404 different knot types. Their largest cube dimension is 246.

`data/benchmarks.json` contains seven randomized paired rounds and A/A controls.
For the connected **abstract** kernel, the median paired baseline/register
ratios at register lengths 12 and 14 were 3.49 and 31.63. Small abstract cases
were slower. The four already-expanded small knot cubes were also much slower
through the explicit-to-port bridge: ratios around 0.010. No end-to-end
recognition speedup is claimed. No full upstream checkout or production PD
corpus was executed here. See `integration/README.md` before any adoption.

## Reproduce the research record and PDF

```sh
python scripts/benchmark.py
python scripts/make_tables.py
sh build.sh
python scripts/checksums.py
```

`build.sh` requires pdfLaTeX and common TeX packages. `reproduce.sh` re-runs the
unit tests, validation, benchmarks, table generation, compilation, and checksums.
Use Python without `-O`; audit assertions are part of the validation.

A re-run changes timings and may change paired ratios. The generated article
tables and key inline ratios are updated from the new data. Conclusions should
be reviewed rather than copied mechanically from another host. Clean the TeX
auxiliary files before redistribution; they are excluded from checksums.

## Package map

- `article/`: PDF, TeX, generated measurement tables.
- `src/portkh/`: exact binary algebra, registers, port complexes, minimization,
  deterministic language domains, CLI, and a narrow explicit audit adapter.
- `tests/`: unit tests, randomized exact checks, CLI and malformed-input tests.
- `scripts/`: independent cube oracle, exhaustive validation, paired benchmarks,
  table generation, and checksum handling.
- `examples/`: exact inputs, replay certificates, language descriptions, and
  small figure-eight cube provenance.
- `data/`: full recorded test, validation, timing, and build evidence.
- `integration/`: conservative adoption plan and API boundary assumptions.
- `provenance.json`: inspected repository blobs, reference versions, and limits.

The article includes ten proposed research directions. The primary target is a
native producer that identifies near-contractible templates and low-complexity
couplings **before** explicit chain-object allocation. The source and article
are distributed under MIT-0; cited external papers are not bundled.
