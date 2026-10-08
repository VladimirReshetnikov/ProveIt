# Certified braid kernels and linear Markov descent

Research continuation for `ProveIt/Topology/UnknotRecognition`, prepared 8 October 2026.

The article is [`article/main.pdf`](article/main.pdf); its complete LaTeX source is
[`article/main.tex`](article/main.tex). No remote repository was modified.

## Mathematical results

For an explicit Artin braid word of `n` letters on `b` strands whose closure is a
knot, write `k = min(positive letters, negative letters)` and
`g_B = (n - b + 1)/2` (the genus of this word's canonical braid surface, **not**
necessarily the knot genus).

Splitting at **all** unsigned generator indices with exactly one occurrence
preserves the knot as a connected sum and leaves at most `4*g_B` crossings.
Testing the Bennequin inequality on every factor either certifies nontriviality
or leaves a closure-preserving kernel of at most `4*kappa <= 4*k` crossings and
`2*kappa + 1` strands, where `kappa` is the sum of the factors' minority counts.
The kernel producer is linear in word operations; the default independent
projection verifier adds a logarithmic factor. The small braid payload has
`O(k log(k+2))` bits for `k >= 1`. The full audit JSON also contains an
input-sized certificate and is **not** a small-payload claim.

Verified preprocessing costs `O(n log(n+2)^2)` bit operations; the complete
algorithm has the stronger additive bound `O(n log(n+2)^2) + 2^O(k)`.
Solving the factors separately by a complete exponential backend gives
`poly(n) * 2^O(k_star)` time after the local tests pass, where `k_star` is their
largest minority count. Thus `k_star = O(log(n)^2)` gives complete
`n^O(log n)` recognition on that presentation class. General explicit braid
inputs still have an exponential upper bound; no uniform small-parameter
reduction for arbitrary knot diagrams is proved.

A separate original-position linked-list routine performs cyclic free reduction
and singleton **endpoint** Markov descent in `O(n+b)` word operations, including
independent replay. It replaces the old helper's quadratic behavior on long
stabilization chains. It does not search all possible destabilizations or find
internal connected-sum cuts.

The singleton topological observation and occurrence counting have classical
antecedents, explicitly credited to Cornelia A. Van Cott (2007). The contribution
here is their certified all-factor formulation, local minority-sign accounting,
complete complexity reduction, implementation, and amortized-linear descent.
No exhaustive priority claim for the standalone `4*k` corollary is made.

## Run without installing anything

Python 3.10 or newer is required; the recorded runs used CPython 3.13.5.
From this directory:

```sh
python -m unittest discover -s tests -v
python -m braidkernel examples/local_bennequin.json
python -m braidkernel examples/stabilized_unknot.json --kernel-only
python -m braidkernel examples/figure_eight.json
```

Input format:

```json
{"strands": 3, "word": [1, 2, 1, -2]}
```

A positive/negative integer is the corresponding positive/negative Artin
crossing. Powers must be expanded. Links and invalid generators are rejected.
The public entry points revalidate braid records.

```python
from braidkernel import Braid, kernelize, recognize
from braidkernel.descent import linear_descent, verify_descent

source = Braid.checked(3, [1, 2, 1, -2])
kernel = kernelize(source)  # CORE means unresolved, never acceptance.
answer = recognize(source)
reduced, trace = linear_descent(source)
assert verify_descent(source, trace) == reduced
```

The reference reduced Khovanov oracle is deliberately small-instance and
independent of the production scanner. Its defaults are 12 crossings and
200,000 enhanced generators **per factor**. With caps disabled it is complete
but can use exponential resources:

```python
answer = recognize(source, max_crossings=None, max_generators=None)
```

`UNKNOT` and `KNOTTED` are decisions; `CORE` is a kernel needing a decision;
`UNKNOWN` is resource exhaustion. A matching polynomial or an unfinished
computation never becomes an unknot certificate. Time allowances are
cooperative, not hard real-time deadlines.

## Reproduce the saved checks and measurements

```sh
python scripts/validate.py
python scripts/benchmark.py
python scripts/render_tables.py
python scripts/generate_examples.py
sh article/build.sh
python scripts/verify_manifest.py
```

The last command verifies the delivered files. Re-running measurements or
rebuilding a PDF changes some files, so a subsequent manifest mismatch is
expected. Preserve the original archive when comparing a new run.

The final saved run passed **42 unittest methods**. The separate corpus has
**2,856 exhaustive short three-braid knot closures**, **32 planted internal-cut
knot inputs**, and **1,000 random comparisons of old/new endpoint descent**,
with **zero mismatches**. Original cube differentials were explicitly checked
for `d^2 = 0` on all 2,888 knot inputs in the first two populations. Full records
and seeds are in `data/`.

The endpoint stage benchmark includes producer **and replay** on the new side,
five paired randomized rounds, and an A/A baseline control. Its observed
baseline/new ratios were 3.61, 15.60, 60.57, and 238.45 on stabilization chains
with 64, 256, 1,024, and 4,096 strands. Tiny no-progress controls instead made
the verified new routine approximately 6.6x and 4.9x slower. These are local
stage measurements, not end-to-end production speedups. A separate raw-cube
comparison deliberately bypasses the production braid shortcuts and must not
be presented as a production speedup.

## Integration status

See [`integration/README.md`](integration/README.md). The callback adapter is
opt-in and was tested with controlled stand-ins. A full upstream checkout,
full upstream regression suite, and production pipeline benchmark were **not**
run in this environment. No automatic patch to an assumed current API is
included. Retain legacy certificate support and use the new versioned schema.

A suitable additive repository location is a named research directory such as
`Topology/UnknotRecognition/research/braid-minority-kernel/`, with production
modules promoted separately after review. No numbered report slot is assumed.

## Build the article

A LaTeX installation providing `pdflatex`, AMS packages, Latin Modern,
`microtype`, `booktabs`, `geometry`, `hyperref`, and the other standard packages
listed in `article/main.tex` is sufficient. Bibliographic entries are embedded;
BibTeX and network access are not needed. The two table inputs are included.

```sh
sh article/build.sh
```

## Provenance and limits

Inspected source commit: `8388b53680366eed81f8bc23d8db8cfbf2cd956e`.
Exact source paths and blob identifiers are in `PROVENANCE.json`.
`CLAIMS.json` separates proved reductions, imported facts, experimental checks,
and unresolved general claims. Certificate replay checks finite transformations;
it is not a formal proof assistant verification of the imported topology.
Third-party paper PDFs are cited, not redistributed. This package uses MIT-0;
the source-derived endpoint baseline retains its explicit upstream attribution.
