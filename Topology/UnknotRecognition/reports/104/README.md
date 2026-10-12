# Private-cocore transport without passive matrices

Research delivery for Vladimir Reshetnikov's **ProveIt** project, 12 October 2026.

The article is `article/private_cocore_transport.pdf`; its complete LaTeX source is beside it. This is a standalone, source-pinned research package. It does not modify the repository or change the recognizer's default pipeline.

## Main results

The maintained private-cocore query asks whether a surviving column contains exactly one passive occurrence, and which curve owns it. It need not compute every passive row. The new producer propagates one of `q+2` exact states per column; a separately implemented verifier uses a saturated total plus a deterministic owner residue.

For sparse real and passive sources with `s` and `z` nonzeros, `m` real rows, `n` columns and `q` passive curves, complete mixed zero-real-fill schedules admit **O(s+z+m+n+q) structural work**. Binary input costs are charged separately in the article. Acyclic source-unit matchings can be normalized to such a schedule without changing the entire final passive matrix for that fixed matching, even when the original order creates fill.

A bounded-exception atlas answers every query omitting at most `k` passive owners after one O((k+1)L) preprocessing pass. A complete search uses at most `(k+1)(n+1)^k` nodes. This is an XP algorithm and is quasipolynomial when the encoded instance size is polynomial in N and k=O(log N). Exception optimization on arbitrary matrices already contains Dominating Set when each column has two unit entries. The article supplies full proofs, state-information lower bounds, and a topological residual two-handle factorization.

**Not claimed:** unrestricted quasipolynomial unknot recognition; a source-geometry authenticator; compressed transport of all exceptional attaching curves; hardness for the narrower native geometric family; a whole-knot benchmark improvement; exhaustive literature priority. Classical matching/peeling and the maintained geometric private-family theorem are attributed rather than claimed as new.

## Contents

| Path | Contents |
|---|---|
| `article/` | 18-page article, complete TeX, benchmark table source, build script |
| `src/private_cocore/` | Owner producer, source schedule compiler and matching normalizer, independent checker, exception atlas/search, narrow source adapter |
| `tests/` | 45 tests and independent dense reference implementations |
| `experiments/` | Exhaustive audits, graph-domination checks, isolated certificate replay, controlled benchmarks |
| `data/` | Original measured results, test output, saved proof and exception example |
| `integration/` | Source audit, claim ledger, integration contract, opt-in overlay installer, proposed synthesis section |
| `upstream/source-pins.json` | Inspected commit and exact relevant blob identifiers |
| `reproduce.py` | Portable runner; preserves original recorded data by using a temporary copy |
| `MANIFEST.sha256` | Integrity hashes of the delivered files, excluding the manifest itself |

## Reproduce

Python 3.10+ syntax and only the standard library are used. The actual tested Python version and environment are recorded in `data/benchmarks.json`.

```sh
python reproduce.py
python reproduce.py --benchmarks
python reproduce.py --pdf
```

The default run executes all unit tests, the two exhaustive audits, and producer-isolated saved-certificate replay. The runner copies the package to a temporary directory, leaves the delivered `data/` unchanged, and saves fresh outputs under `reproduction/`. `--benchmarks` includes the synthetic matrix timings; `--pdf` requires `pdflatex`. Each command returns nonzero on any failed subprocess. Do not run audits with Python assertions disabled.

For direct execution from the package root:

```sh
PYTHONPATH=src:tests python -m unittest discover -s tests -v
PYTHONPATH=src:tests python experiments/audit.py
PYTHONPATH=src:tests python experiments/domination_audit.py
python experiments/replay_saved.py
```

Direct experiment scripts overwrite their corresponding `data/` output; use the portable runner to preserve the original measurements. On Windows use `;`, not `:`, in `PYTHONPATH`.

## Minimal use

```python
from private_cocore import produce_certificate, verify_certificate
from private_cocore import compile_program, build_atlas, query_atlas, find_exceptions

# Zero-based columns and curve owners. Values are UNSIGNED occurrences.
real = [{0: 1, 1: 2}, {1: 1, 2: 1}]
passive = [{0: 1, 3: 1}, {4: 1}]
schedule = [(0, 0), (1, 1)]
n = 5

certificate = produce_certificate(real, n, passive, schedule)
assert verify_certificate(real, n, passive, certificate, require_complete=True)
assert certificate['least_private'] == [3, 4]

program = compile_program(real, n, schedule)
atlas = build_atlas(program, passive, k=1)
assert query_atlas(atlas, deleted=()) == (3, 4)
result = find_exceptions(atlas)
assert result['status'] == 'FOUND'
```

A missing private witness is `-1`. A certificate can describe missing witnesses accurately; `require_complete=True` additionally demands one for every passive row. `FOUND` from the exception search means only that the retained subfamily passes the fixed-disk-system query. It does **not** permit actual topological attachments to be discarded.

A positive exception result can be replayed independently by forming the retained source rows, producing an ordinary owner certificate for that subfamily, and invoking `verify_certificate(..., require_complete=True)` against those same retained source rows. Preserve the map from reindexed rows back to original attachments. The independent verifier does not rely on the atlas or on the exception search.

`produce_matching_certificate` accepts a complete acyclic source-unit matching and normalizes its order first. It does not support units created at source-zero entries. The caller must retain the established fallback for unsupported schedules, not turn rejection into a topological negative result.

## Validation and performance scope

All **45 named tests passed**. The exhaustive audit checked 8,748 source schedules, 25,344 passive differential cases, 486 source-unit matchings, 540 successful matching-order transfer replays, 26,244 signature addition identities, and 1,296 scalar identities. The graph audit checked all 1,100 simple graphs of order at most five and 33,867 graph/deletion-set pairs. A saved certificate replayed with producer modules absent from the import path of the isolated verifier.

The controlled matrix benchmark compared a separately written dense saturated baseline with the owner producer and producer-plus-independent-checker. On the 96-row sparse chain the recorded median dense/certified ratio was **198.37**; on the denser fixture it was **2.18**. The two tiny fixtures were slower with the new combined path, by approximately **2.7x** and **2.4x**. These are synthetic local-operator measurements, not native normal-cut or whole-unknot recognition timings. All seven samples per method are retained.

The full ProveIt suite, Regina source-geometry audits and native knot benchmarks were **not run** for this delivery. Follow `integration/INTEGRATION.md` before any production use.
