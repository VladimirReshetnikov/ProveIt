# Compressed component certificates for unknot recognition

This archive contains a research continuation for
[`VladimirReshetnikov/ProveIt`](https://github.com/VladimirReshetnikov/ProveIt),
based on the exact source commit
**`274909dd8724e411ece14e47ac4addea717aeca6`**.

The complete article is
`article/compressed_component_certificates.pdf`; its main source is
`article/compressed_component_certificates.tex`.

The package makes two concrete improvements. A generation-checked periodic
merger scheduler preserves the historical reduction certificates while
limiting merger tests to a quadratic number per closure. An explicit family
has five complete AHT cycles and improves the historical cubic merger count
to a quadratic count. Classical weighted orbit replay then supports five
cellular weights that detect and count compressing-disk components inside a
supplied, possibly disconnected normal surface.

These are improvements to a compressed component kernel and its certificates.
**They do not establish a general quasi-polynomial unknot recognition
algorithm.** Surface discovery, diagram-to-exterior provenance, geometric
cutting, and a controlled global hierarchy remain separate obligations.

## Recorded results

The final maintained suite passed **1,047 tests in 135.788 seconds** in the
recorded environment. The independent normal-surface audit uses finite
literal component checks and Regina 7.4; its trefoil triangulation and normal
vectors are frozen in the archive.

The final paired benchmark records an old/adaptive time ratio of approximately
**15.56** on the constructed 256-pairing family and **1.51** for an interval
count on the 128-tetrahedron native meridian arc system. The latter excludes
construction of the geometry from the timer. Native gains here come from
avoiding repeated scans over nonperiodic rows: the adaptive native cases do
not switch to the queue and retain the historical merger-test count. These
are measured local workloads, not whole-recognizer speedups. The article
reports controls, raw sample retention, exact operation counts, and limits
on each inference.

## Archive layout

| Path | Contents |
|---|---|
| `article/` | PDF, complete TeX source tree, bibliography, tables, vector figures, and build instructions |
| `code/fast/` | Runnable source snapshot, production changes, maintained tests, and demonstration |
| `code/reports/` | Minimal pinned archived oracle dependencies used by the maintained suite |
| `reference/interval_orbits.py` | Exact historical interval producer for controlled comparisons |
| `experiments/` | Paired timing driver, independent normal audit, frozen trefoil fixture, and figure/table generator |
| `results/` | Recorded raw measurements, audit results, full test log, weighted-test summary, and demo output |
| `integration.patch` | Source/test/README/demo changes with paths relative to the ProveIt repository root |
| `PROVENANCE.json` | Source pin, identities, environment, and evidence-to-command mapping |
| `reproduce.py` | Independent reproduction jobs, with new output written under `rerun/` |

Existing source and archived oracle license notices are retained. New
production modules follow the maintained MIT No Attribution license.
Third-party mathematical papers are cited; their downloaded PDFs are not
redistributed in this package.

## Dependencies

Production code and the demonstration use **Python 3.10 or later and its
standard library**. The recorded Python version is 3.12.14. Running through
the convenience driver requires no installation of the local `fastunknot`
package: it selects `code/fast/` as the working directory.

Additional jobs have these dependencies:

| Job | Additional requirements |
|---|---|
| `demo` | None |
| `tests` | Regina is optional in the project; install it to reproduce the recorded full native coverage. Unavailable optional checks are reported by the suite. |
| `audit` | Regina; the independent audit requires it and fails clearly when it is unavailable |
| `benchmark` | None beyond the delivered Python source |
| `figures` | Matplotlib |
| `article` | pdfLaTeX and BibTeX, optionally driven by `latexmk`; the TeX packages listed in the main source |

The project's optional normal dependency is declared as
`regina>=7.4.1,<8` in `code/fast/pyproject.toml`. Its installed distribution
version and the native engine's `versionString()` need not have the same
patch suffix. The audit records the engine version directly. For a Python
environment needing the optional audit and plotting tools, install:

```bash
python -m pip install "regina>=7.4.1,<8" matplotlib
```

For the PDF, a standard TeX installation needs Latin Modern, `microtype`,
`cleveref`, and the other packages explicitly listed in the main source.
The driver uses `latexmk -pdf` if available; otherwise it runs pdfLaTeX,
BibTeX, and two more pdfLaTeX passes. It stops on a failed command.

## Reproduce individual jobs

Run these commands from the archive root, or call the script by its full
path from another working directory:

```bash
python reproduce.py demo
python reproduce.py tests
python reproduce.py audit
python reproduce.py benchmark
python reproduce.py figures
python reproduce.py article
```

The commands are independent; the driver does not silently launch other
expensive jobs. It prints each subprocess command, streams its output live,
and writes a combined stdout/stderr log. A nonzero subprocess status makes
the driver fail, so an unfinished computation cannot become a successful
reproduction summary.

New outputs go under `rerun/results/`. In particular:

- `component_demo.json` and `demo.log` record the small demonstration.
- `full_tests.log` retains the complete maintained-suite output.
- `weighted_test_summary.json` is copied from the diagnostic generated by
  the weighted tests. The driver then restores any original copy beside the
  research module, so delivered evidence is preserved.
- `independent_normal_audit.json` and its log record the finite Regina audit.
- `benchmark_orbits.json` and its log record the new paired measurements.
- Figure and article commands have their own logs.

Repeated invocations replace the corresponding **rerun** outputs. Files in
the archive's recorded `results/` directory are never overwritten.

### Demonstration

The dependency-free demo first checks a meridian disk together with a
boundary vertex-link disk in a hand-built solid torus. It finds two disk
components, exactly one of which compresses the boundary. It then represents
`2^5000` parallel meridian disks with one profile group. Both examples record
and verify certificates, including a JSON transport round trip. The printed
summary uses bit lengths and exact equality checks rather than a huge
decimal expansion.

### Timings

Collect benchmark timings without concurrent heavy jobs. The default is
seven measured rounds and seed `26100945`, matching the recorded experiment.
For an exploratory shorter run:

```bash
python reproduce.py benchmark --rounds 3 --seed 26100945
```

The reference is always the delivered `reference/interval_orbits.py`; the
driver checks its SHA-256 before running and does not fetch a moving Git
branch. Changed elapsed times are expected across hardware and environments;
the exact counts and certificate comparisons are the reproducible
mathematical invariants.

### Figures and article

The first `figures` or `article` invocation copies the entire manuscript
tree to `rerun/article/`. Subsequent invocations reuse that copy, preserving
any regenerated figures and tables. The original `article/` stays intact.

`figures` uses the recorded `results/benchmark_orbits.json` by default, so
rebuilding the article remains consistent with its discussion of the recorded
run. To explore fresh measurements, select them explicitly:

```bash
python reproduce.py figures --results rerun/results/benchmark_orbits.json
python reproduce.py article
```

The rebuilt PDF is
`rerun/article/compressed_component_certificates.pdf`. Using new timing
results regenerates numerical tables and plots; it does not automatically
rewrite the manuscript's prose discussion of the recorded experiment.
Review that discussion before presenting a rerun as an updated report.

## Integrate into ProveIt

The patch paths are relative to the **ProveIt repository root**, beginning
with `Topology/UnknotRecognition/`. From your target ProveIt checkout:

```bash
git apply --check /absolute/path/to/archive/integration.patch
git apply /absolute/path/to/archive/integration.patch
```

The patch was prepared against commit
`274909dd8724e411ece14e47ac4addea717aeca6`. On a later checkout, review the
changes and resolve any ordinary conflicts before applying them. A clean
textual application does not replace review of concurrent changes.

Use the patch to integrate the new source and tests. **Do not replace a newer
`Topology/UnknotRecognition/fast/` tree with this archive's complete source
snapshot**, because that could discard work added after the pinned commit.
`code/fast/` is included to make the research runnable and auditable.

Copy the complete `article/` directory, with all its subdirectories, to a
new manuscript directory such as:

```text
Topology/UnknotRecognition/synthesis/component_certificates_20261009/
```

Keep the main TeX file, `sections/`, `tables/`, `figures/`, and
`references.bib` together. Their relative paths remain valid when the whole
tree is copied. The manuscript is supplied as a complete folder rather than
inlining its sections into an existing synthesis file.

The archived oracle dependencies in `code/reports/` are pinned copies of
files already belonging to the corresponding reports. Their identities are
recorded in the provenance data. They support the supplied full test suite;
they are not new runtime dependencies of the normal-component API.
