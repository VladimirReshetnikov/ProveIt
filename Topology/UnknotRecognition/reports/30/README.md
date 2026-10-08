# Exact binary boundary tensors and compressed transport for unknot recognition

Research continuation prepared for Vladimir Reshetnikov's **ProveIt** project,
8 October 2026.

The article develops and proves three exact compression kernels, implements
them against a pinned repository snapshot, and records independent correctness
checks and controlled measurements. The strongest new implemented general
bound is `poly(n) * 2^O(sqrt(n))` **for full Jones computation**. This improves
the maintained faithful Potts implementation's bound; comparable general
Jones bounds are already known. A general quasi-polynomial bound for complete
unknot recognition remains unproved.

## Start here

- `unknot_binary_tensors.pdf`: complete research article.
- `unknot_binary_tensors.tex` and `sections/`: editable modular TeX source.
- `unknot_binary_tensors_standalone.tex`: the same article with all section
  inputs expanded into one compilable TeX file.
- `integration.patch`: source, tests, research drivers, and recorded data to
  apply from the root of the pinned ProveIt checkout.
- `fast/`: complete runnable maintained implementation with this continuation.
- `reports/`: small existing reference modules needed by the full test suite.
- `VALIDATION.md` and `validation/`: final gate, independent audits, baseline
  defect diagnosis, exact logs, and source provenance.
- `MANIFEST.json`: SHA-256 hashes of delivered files, excluding the manifest
  itself. `verify.py` checks them before replaying correctness checks.

The code and article are supplied under the repository's MIT No Attribution
license (`LICENSE`). Third-party works listed in the article are cited rather
than bundled. Retained baseline files preserve their own notices.

## Main results and limitations

1. **Binary Jones tensors.** An integral turning cochain is constructed from
   the spherical PD rotation system. Summing two orientations per smoothing
   circle realizes the Kauffman bracket. A frontier of `w` edges therefore has
   at most `2**w` keys without a common-disk assumption. Exact integer
   specialization and balanced reconstruction recover every Jones coefficient.
   The backend is optional because measured regressions occur on some inputs.

2. **Near-prefix compressed LCS.** If two compressed words have an exact
   common prefix `K` and remaining lengths `a,b`, all improvements reduce to
   `S=a+b-1` diagonals when `K>=S-1`. Small-period cycle automata evaluate the
   long shifted comparisons directly on the grammar. The implementation uses
   `S<=32` and preserves the complete fallback. It improves an explicit
   exponentially long input family; the measured whole-knot corpus never
   activates this branch.

3. **Boundary-lift transport.** A checked dihedral-cover query with point and
   whole-circle constraints returns every compatible isomorphism in at most
   two modular progressions. Cyclic canonical keys give exact marking counts.
   For a fixed component `C` and `k>=1` unparameterized boundary slots with
   fixed base labels, the count is at most `max(2,-chi(C))**(k-1)`. This gives
   a genuine local quasi-polynomial count under polynomial Euler complexity
   and logarithmically many slots. Presentation bit size, general gluings,
   and the number of generated pieces remain separate obligations.

The article provides twelve research questions, including cochain
optimization, charged backend selection, cyclic matching, grammar growth,
geometric continuation equivalence, encoded cutting and repair, and global
state-count and unary-work bounds. It does not infer complete recognition
from Jones polynomial identity.

## Run the code and correctness checks

Python 3.10 or later is required by the maintained project. The recorded
environment uses Python 3.12.14 on Linux. The new mathematical kernels require
only the standard library. Regina 7.4.1 is optional for ordinary use; install
it to reproduce the full integration environment without native-test skips.

```sh
python3 -m venv .venv
.venv/bin/python -m pip install 'regina==7.4.1'
.venv/bin/python -B verify.py --hashes
.venv/bin/python -B verify.py
.venv/bin/python -B verify.py --full
```

The default verification runs the focused tensor, matcher, transport, and
worker tests, followed by both independent literal-cover audits. `--full`
runs the complete maintained test suite and the two audits. Outputs from
replayed audits are temporary; archived measurements are not overwritten.
Missing Regina causes the existing native tests to skip. The full suite
needs the included sibling `reports/` references, so keep the archive layout.
Historical research drivers are preserved in the source; rerunning those
that require entire older report archives needs the full upstream checkout.
All drivers for this continuation and all maintained test dependencies are
included.

Example full-polynomial query, from `fast/`:

```sh
../.venv/bin/python -B -m fastunknot jones examples/trefoil.json \
  --backend spin-faithful
```

See `fast/BINARY_TENSORS.md` and the three research directories for interfaces
and more examples. In particular, `max_states=None, max_transitions=None` in
the Python Jones interface disables the local state and transition caps;
an external cancellation callback can still impose a deadline.

## Reproduce performance experiments

Run these commands from `fast/` with the selected Python interpreter:

```sh
python -B benchmark_spin_jones.py --output results/spin_jones_rerun.json
python -B benchmark_spin_jones.py --only grid-8-shuffled \
  --output results/spin_jones_shuffled_rerun.json
python -B near_prefix_research/benchmark_near_prefix.py --fast-dir . \
  --output results/near_prefix_rerun.json
python -B boundary_transport_research/benchmark.py \
  --output results/boundary_transport_rerun.json
```

The current Jones driver exercises the final implementation. Its results
will have a new source hash. The initial audit source, the supplied-order
correction, and the pre-normalization-validation source are all retained in
`fast/spin_jones_research/`. Read that directory's README before comparing
historical and final-source timings. The matching audit has an original
driver and a portable loader using a checked archived baseline; its README
records the unchanged mathematical kernel and original measurement hashes.

To replay the initial Jones policy, first copy `fast/` to a fresh directory.
In that copy, replace `fastunknot/spin_jones.py` and `benchmark_spin_jones.py`
with their namesakes from `spin_jones_research/initial/`, then run the copied
benchmark driver. To replay the recorded ordering follow-up, use the current
driver, replace only `fastunknot/spin_jones.py` with
`spin_jones_research/before_normalization_validation.py`, and select
`--only grid-8-shuffled`. The copied fixtures retain the paths expected by
each original driver, and the benchmark records the source hashes it uses.

The Jones measurements distinguish ordinary full queries from contraction
on a common prepared order. Boundary timings distinguish cover preparation
from prepared queries. All timing files retain raw samples and censored
statuses. An incomplete query is never used as a completed-time denominator.

## Integrate into ProveIt

The exact baseline is:

```text
8a95834940cf77cdab1b39571ffc102ca8b6bede
```

The most recent baseline commit affecting `Topology/UnknotRecognition` is:

```text
30d58bd311d96af1e49b6c98584b8da526b7adcc
```

From the target repository root, first review and check the patch:

```sh
git apply --stat /absolute/path/to/unknot_binary_tensors/integration.patch
git apply --check /absolute/path/to/unknot_binary_tensors/integration.patch
git apply /absolute/path/to/unknot_binary_tensors/integration.patch
```

The patch contains all modified and new maintained files, including the new
research directories. It does not replace the existing synthesis document.
If the target branch has moved, use normal review and conflict resolution;
the pinned baseline is the tested integration target.

For the article, a suggested new destination is
`Topology/UnknotRecognition/reports/binary_tensors_20261008/`.
Copy the PDF, the main TeX source, `sections/`, and `Makefile` there, or copy
the standalone TeX and PDF together. Copy `VALIDATION.md` and `validation/`
beside them if preserving the full research record in that report. Link the
new article from the existing synthesis at the repository maintainer's
preferred location. All TeX section labels are local to this standalone
article; merging its source into the synthesis requires normal label review.

The accompanying patch was checked against a fresh baseline extraction and
the resulting source compared with the delivered tree; the validation report
records the outcome. No remote branch, commit, or pull request was created.

## Build the article

Use a normal TeX Live installation with `latexmk`, pdfLaTeX, Latin Modern,
AMS packages, `microtype`, `booktabs`, `tabularx`, `enumitem`, TikZ, `fancyhdr`,
and `hyperref`. No external images or bibliography download is needed.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error unknot_binary_tensors.tex
```

The standalone source can instead be compiled with the same command using
`unknot_binary_tensors_standalone.tex`. The included PDF was rendered and
visually checked, with references resolved and no overfull boxes.

## Known boundaries

The Jones decoder checks normalization and coefficient bounds but presumes
its scalar came from the exact contraction. The independently checkable turn
certificate validates local weights, not a completed state sum. The
boundary solver handles all covering isomorphisms over a fixed base, not
prescribed orientation or fibre directions or arbitrary parametrized gluings.
The optional Regina stage retains its external-engine trust label.

A baseline worker-pipe defect was diagnosed and corrected during integration.
The wrapper's controlled worker must not leave descendants inheriting its
pipes. The correction was tested on Linux; it is not a general process-tree
supervisor. Historical failed or incomplete captures are retained and are
not counted as passing runs. None changes the mathematical complexity claims.
