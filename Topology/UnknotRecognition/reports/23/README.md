# Exact symbolic compression for unknot recognition

Research continuation for ProveIt, 8 October 2026.

**Main article:** `article/unknot_symbolic_compression.pdf`.
Its LaTeX source, generated tables, static figure, and build script are in the
same directory. The article includes full proofs, implementation contracts,
paired measurements, unsuccessful directions, and concrete research questions.

## Results and limits

1. **Exact graded transfer.** Contract the scalar differential and recover all
   residual cobordism maps by a finite quantum-ordered computation. The kernel
   uses at most `S * E_delta` typed coefficient compositions for `S` survivors
   and `E_delta` positive-weight entries, plus binary contraction and additions.
   It preserves the information needed for further gluing; it is not just a
   survivor-count shortcut. A source's quantum band has width at most `2k` at
   a `2k`-point frontier.
2. **Exact finite twist tails.** For one run of magnitude `m` in a context of
   `L` other crossings, the cap `L+2` determines a compact full homological
   profile for all longer runs. Total rank is affine already at `L+1`.
   For knot inputs the time is `2^{O(L)} poly(N)` in succinct bit length `N`.
   This backend forgets quantum grading. It computes a closed braid's homology,
   not a tangle replacement that may be substituted into arbitrary contexts.
3. **Succinct structural certificates.** Evaluate the existing signed-Seifert
   criteria directly on binary run input. The CLI handles enormous exponents
   without constructing their crossings; its independent verifier accepts
   emitted hexadecimal certificate fields after serialization.
4. **Conditional geometric target.** A weighted-path theorem bounds repairs
   in a fixed acyclic dependency graph. Logarithmic dependency depth and
   numerical polynomial counter bounds give quasi-polynomial event count.
   No suitable universal dependency graph for knot exteriors is established.

**No general quasi-polynomial unknot-recognition theorem is claimed.** State
volume, exact representation growth, and constructive geometric dependencies
remain open. Eager transfer regressed on the ordinary diagram controls and
stays optional. All dominant-run knots used in the tail timing experiment
were already structurally detected; those gains concern exact homology.

## Contents

| Directory | Contents |
| --- | --- |
| `article/` | PDF, TeX, build script, tables, PNG/SVG figure |
| `implementation/fast/` | Runnable baseline source/tests/examples plus the proposed extension |
| `patches/` | Integration patch against the pinned ProveIt snapshot |
| `verification/` | Regression logs, chain-identity checks, independent tail and repair-DAG verifiers |
| `benchmarks/` | Paired raw samples, summary tables, inputs, and portable drivers |
| `examples/` | Exact enormous signed-run inputs |
| `provenance/` | Baseline Git-blob manifest, baseline log, patch validation, and revision trace |
| `tools/` | Correctness runner and article-evidence regeneration |

The runnable source is self-contained. Historical upstream `fast/results/`
records and the other upstream research reports are not duplicated; they
remain available in the pinned repository. The new measurements are included
in full. All 114 source/report text files retrieved for the audit were checked
against their Git blob identifiers. `provenance/source_manifest.json` lists
those files and their immutable source commit.

## Run the implementation

Python 3.12.14 was used for the recorded runs. The recognizer and correctness
checks use the Python standard library; no third-party knot package is needed.
Run these commands from the archive root:

```bash
cd implementation/fast
python -m fastunknot khovanov examples/conway.json --reduction graded-adaptive
python -m fastunknot.symbolic_braid ../../examples/four_strand_tail.json --mode homology --check-d2
python -m fastunknot.symbolic_braid ../../examples/balanced_four_runs.json --mode certificate
```

The first enormous example uses `M = 10^100 + 1`, has context length six,
builds 1,650 basis elements, and returns exact reduced rank `3*10^100 + 1` as
eleven exceptional degrees and one constant interval. The balanced example
has four huge runs on five strands, writhe zero, and no dominant run; its
homogeneous Seifert graph certifies nontriviality directly.

The main scan modes `graded` and `graded-adaptive` preserve the default
`standard` mode. They support ordinary component coefficient composition,
but cannot be combined with shared scanners, homological windows, non-bit
coefficients, non-minimum-fill pivots, or multiple order races.

The symbolic CLI accepts a JSON object with `strands` and exactly one of
`runs` or `word`, optionally nested under `braid`. Runs are pairs of a
one-based unsigned generator index and a nonzero signed exponent. The path
`-` reads standard input. Integer fields accept JSON integers or signed
hexadecimal strings such as `"-0x10001"`. Very large result integers use the
same hexadecimal convention. No arithmetic is performed in floating point.

Recognition modes require a one-component input closure. Raw homology also
supports links. Resource exhaustion yields `UNKNOWN`; malformed input yields
`INVALID`. A structural `INCONCLUSIVE` result is not an unknot verdict.
The certificate verifier is
`fastunknot.symbolic_braid.verify_signed_run_certificate(strands, runs, certificate)`.

## Reproduce correctness

From the archive root:

```bash
python tools/verify_all.py
```

This runs the full integrated unittest suite, the graded contraction checks,
the independently written explicit-tail verifier, and the repair-DAG checks.
It writes logs and `verification/integrated_validation.json`. It does not run
benchmarks. The raw full transfer record contains 86 diagrams, 258 order
presentations, and 1,812 stage contractions with eight identities each.
All four modes agree in raw ranks; all three quantum-tracking modes agree in
quantum-resolved ranks. Counts of presentations are not counts of distinct knots.

The tail suite includes 240 full profile comparisons, 80 checks of the earlier
rank threshold, 32 literal matrix identifications, 24 independent cube checks,
certificate mutation tests, original/cap component parity, and huge exponents.
The separate tail referee checks 392 explicit complexes. The combinatorial
repair verifier checks 380 path/closed-form fixtures plus invalid inputs.

## Reproduce measurements

The delivered JSON preserves every sample, case, seed, and measurement scope.
Run these separately; timing values will change on other machines and under
different load:

```bash
python benchmarks/graded_transfer/benchmark_transfer.py
python benchmarks/benchmark_long_tail.py --rounds 7 --output benchmarks/long_tail_reproduced.json
python benchmarks/benchmark_signed_run_structural.py --output benchmarks/signed_run_structural_reproduced.json
```

The graded driver defaults to a separate reproduced output. The other commands
above also preserve the delivered measurements. See each benchmark's notes
for batching and A/A controls. The raw homology and raw scan timers bypass
recognition filters. The structural interface timer explicitly includes word
expansion and PD construction only in the expanded route, starting with the
same parsed run tuple in every arm.

The signed-run verifier was strengthened after its timing run to accept its
own emitted hexadecimal numeric fields. The timed certificate producer is
unchanged; the exact measured-to-final verifier patch and hashes are under
`provenance/structural_*`. The measured long-tail driver was changed only for
portable import/output paths; its patch is under `verification/`.

## Rebuild the article

```bash
python article/build.py
```

This uses a TeX installation providing `pdflatex`, AMS packages, `geometry`,
`lmodern`, `microtype`, `booktabs`, `tabularx`, `enumitem`, `listings`, and
`hyperref`. It consumes the supplied figure and generated tables and does not
require Python plotting packages. It runs enough LaTeX passes to settle
references. To regenerate the tables and static figure from the retained
JSON first, install Matplotlib and NumPy and run:

```bash
python tools/refresh_evidence.py
python article/build.py
```

Refresh currently reads the delivered benchmark filenames. To use new timing
records, intentionally replace those inputs or update the script's paths.

## Integrate into ProveIt

The patch is rooted at `Topology/UnknotRecognition/fast/` and targets commit:

```text
d54009df0ea3751b8662bb76549d3c1bb0eec19c
```

From a checkout of that snapshot, first review and check the patch:

```bash
git apply --check /path/to/unknot_symbolic_compression/patches/fast_symbolic_compression.patch
git apply /path/to/unknot_symbolic_compression/patches/fast_symbolic_compression.patch
```

On a newer checkout, inspect upstream changes and resolve overlaps before
applying. The included source tree is useful for comparison, but copying it
over a newer checkout could overwrite intervening work. Existing defaults
and release version remain unchanged. The top-level research material can be
placed in a report directory of the maintainer's choice; relative links and
verification scripts are organized around the bundle root.

The inherited implementation license is in `implementation/fast/LICENSE`.
The mathematical report states its dependencies and novelty boundaries;
finite computational checks supplement its proofs and are not a formal
proof-assistant certification.
