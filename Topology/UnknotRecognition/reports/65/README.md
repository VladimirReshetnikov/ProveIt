# Disk-Completion Kernels
## Optimal single-exponential representative families for surface frontiers

Research continuation for ProveIt, 9 October 2026.
Reviewed revision: `3a90fb34146c915328ab8eac6250cc2514f74ed0`.

The article is `article.pdf`; its complete LaTeX source is `article.tex`.

## Result

For disk pieces glued along **r actual, pairwise disjoint boundary intervals**, the disk-completion matrix has exact rank `2^(r-1)` over F2. The component-count grading has rank `binomial(r-1,c-1)`. A cost-ordered independent subset preserves the minimum cost against **every disk-union cap**, retains actual original witnesses, and admits a source-bound expansion certificate checked by separate code. These representative-subset bounds are sharp.

The topological ingredient is

    delta(S glued to T) = delta(S) + delta(T) + cycle_rank(attachment_graph),
    delta(S) = number_of_components(S) - Euler_characteristic(S).

The typed assembly theorem gives a single-exponential search in the actual live-arc width for a supplied finite grammar. Polynomial overhead and width O(log² n) would give a quasi-polynomial complete recognition route **if a complete, source-bound geometric grammar with those bounds is constructed**. That global construction is not delivered here.

This is a disk-specific application and sharpening of established rank-based / matroid representative-family methods, not a claim to have invented those methods or to have established global literature priority.

## Executed evidence

- 36 unit test methods pass.
- Independent audit: 813,297 direct compatibility-matrix entries; 1,000 weighted families / 14,014 completion queries; 1,000 literal triangulated-surface gluings; 200 complete grammar comparisons.
- Paired same-generator abstract grammar benchmarks at widths 6, 7, 8: median ratios 3.98x, 5.73x, 11.91x in favor of representative search.
- A no-reuse, single-cap control is about 4.69x slower with preprocessing. It is a single recorded timing per mode, not a median.

These are abstract assembly measurements, **not whole-knot or maintained fastunknot speedups**. No native regression suite was run and no upstream runtime was changed.

## Reproduce

Python uses only the standard library. Tests were run with CPython 3.13.5 on Linux. Python syntax is compatible with 3.10+.

```sh
make test
make audit
make example
make benchmark   # overwrites timing results with a fresh run
make tables      # rebuilds table fragments from retained JSON
make pdf         # pdflatex three passes; never reruns benchmarks
```

Without Make:

```sh
PYTHONPATH=code python3 -m unittest discover -s tests -v
python3 code/audit.py
python3 code/example.py
python3 code/benchmark.py --repeats 3
python3 code/make_tables.py
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

On PowerShell, set `$env:PYTHONPATH = "code"` before running the Python test command. Python itself can be invoked through the project's usual environment manager. The LaTeX source lists its standard package requirements.

## Code contracts

`code/disk_kernel.py` returns original `Candidate` objects and a certificate. `code/certificate_check.py` imports none of the producer modules and checks against caller-supplied partitions and costs. It verifies algebraic pruning, not geometry.

`code/assembly.py` contains complete exact and reduced solvers for a supplied finite layered grammar. `code/surface_model.py` independently triangulates and glues the selected polygonal disk pieces, checks manifold links, and computes surface topology. It does **not** certify an embedding in a knot exterior.

The reducer's default cap is 20 labels; the independent checker defaults to 16. These are resource guards. The layered prototype also checks the combined incoming/outgoing partition of each piece under its current width guard. A global cooperative time budget is not yet implemented for the grammar solver. No exception or incomplete search is a knot verdict.

`NO_DISK_IN_GRAMMAR` means only that the **supplied grammar** has no successful assembly. `FOUND_ABSTRACT_DISK` is not an unknot certificate. Arbitrary partition-dependent guards and point-incidence ports are outside this API's topological contract; the package includes counterexamples.

## ProveIt placement

Suggested destination: `Topology/UnknotRecognition/reports/<NN>/`, where intake assigns the next number. Remove the single archive wrapper as prescribed by the current incoming policy. This package is a report, not an automatically applied patch. No checksum-only manifest or third-party fonts are included.

The reviewed native project already has a source-checked compact exterior constructor and normal-component / compressing-disc certificate APIs. The missing integration is a complete, controlled arc-interface disk-assembly producer and embedded witness replay, not the diagram-to-exterior construction itself.

See `docs/CLAIMS.md`, `docs/INTEGRATION.md`, and `docs/SOURCE_AUDIT.md` for proof and implementation scope.
