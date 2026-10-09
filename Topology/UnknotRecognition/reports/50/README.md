# Polynomial sparse incidence from certified interval orbits

Research continuation for `ProveIt/Topology/UnknotRecognition`, 8 October 2026.

**Read `paper/article.pdf`.** The archive contains its complete LaTeX source,
three additive implementation modules, native-style tests, an additive patch,
immutable native baselines, independently replayable examples, and retained
measurements.

## Result and scope

For an explicitly encoded interval-pairing system with arbitrary explicitly
listed interval-union ports, the positive component-incidence histogram has
polynomial size and can be recovered in polynomial bit time. Polynomial support
size follows from the **existing weighted Agol–Hass–Thurston theorem**. This
package realizes sparse recovery using the maintained **unweighted** kernel and
independent local proofs; it does not implement weighted AHT or claim a new
complexity classification for weighted orbit counting.

Recovery needs O(s*r) subset-sum requests for s positive signatures on r ports.
Optional balanced block deletion reduces the trial count for small signatures.
Certificates retain atom weights and retained-port zero witnesses. A parity
double has the same support, so per-signature consistency needs at most s+1
additional orbit counts rather than another support search.

**This is not a general quasi-polynomial unknot recognizer.** No ordinary
recognition dispatch is changed. The results do not supply attachment maps,
normal-surface or knot-exterior provenance, or bounded global hierarchy search.

## Quick verification, offline

Python 3.10+ is required; the recorded environment is CPython 3.13.5. All Python
code uses the standard library. No network access is needed.

```sh
python tools/check_manifest.py
python tools/bootstrap.py
python -m unittest discover -s tests -v
python tools/replay_examples.py
python tools/check_patch.py
python tools/audit.py
```

Check the manifest before regenerating any retained receipts.

The audit includes three deliberately adverse gapped-port controls; two were
censored at a five-second cooperative deadline in the retained run. It writes
new audit receipts and example certificates. The full maintained repository
suite was **not** run here. The local suite has 21 test methods, including loops
over 500 random graph instances under both strategies, 1,000 generic measures
under both strategies, and 300 signed graph instances. The separate audit adds
512 exhaustive native-dense/sparse comparisons and independent replays.

## Benchmarks

```sh
python tools/benchmark.py --repeats 2 --output results/benchmark_rerun.json
```

The retained main data are `results/benchmark.json`. They compare the exact
maintained dense interface with sparse linear, sparse split, an identical split
control, and split with proof production plus replay. Raw samples, query counts,
certificate byte sizes, seeds, environment, and source pins are retained.
`results/benchmark_followup.json` contains a separate longer-batch follow-up.
`tools/followup.py` regenerates that follow-up and overwrites its receipt.

The disjoint 10-port fixture drops from 1,024 orbit counts to 26 and from
2,498,706 certificate bytes to 26,538. Longer batches give about a 107-fold
uncertified query gain on that selected interval workload. The all-signatures
six-port control is slower under sparse split; widely separated singleton ports
remain costly. These are **local interval measurements**, not whole-knot timings.
Do not assign a speedup ratio to an unrun or censored dense baseline.

## Rebuild the article

```sh
python tools/make_tables.py
cd paper
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

The tables read retained JSON data; the main TeX file is not standalone without
`paper/tables/`. References are embedded, so BibTeX is not required.

## Integration

See `INTEGRATION.md`. `integration.patch` adds only three modules and one test
file below `Topology/UnknotRecognition/fast/`. Apply it from the ProveIt root:

```sh
git apply --check /path/to/integration.patch
git apply /path/to/integration.patch
cd Topology/UnknotRecognition/fast
python -m unittest discover -s tests -p test_sparse_incidence.py -v
```

The new sparse histogram is a list of `[mask, positive_count]` rows, **not** the
old dense positional array. Existing consumers must deliberately adopt the new
contract. The patch does not change CLI arguments or the package dispatcher.

## Directory map

| Path | Content |
|---|---|
| `paper/` | 22-page article, complete source, generated tables |
| `integration/` | proposed modules and native-style unit tests |
| `snapshots/` | exact maintained sources used for the comparisons |
| `tests/` | offline harness for the same local test methods |
| `tools/` | loaders, audit, benchmarks, patch check, replay, build helpers |
| `results/` | raw JSON, test and audit logs, build/review receipts |
| `examples/` | source-bound unsigned and signed certificates |
| `CLAIMS.md` | theorem, measurement, and non-claim ledger |
| `PROVENANCE.json` | Git blob identities and source locations |
| `MANIFEST.sha256` | SHA-256 inventory of delivered files |

New material and included repository code are MIT-0. Classical papers are cited,
not redistributed. The article is a research draft, not a peer-reviewed or
proof-assistant-verified result.
