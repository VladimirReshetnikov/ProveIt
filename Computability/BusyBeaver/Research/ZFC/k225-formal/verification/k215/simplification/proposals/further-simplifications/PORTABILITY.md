# Portability and execution boundary

The release verifier runs only these authored programs, plus their stated sibling helper:

| Check | Bundled inputs | Regenerated result |
|---|---|---|
| `check_source_pins.py` | Topic source-pin records including the historical and phase-5 heads, all pinned source bytes, reviewed-artifact hashes | `SOURCE_PIN_CHECKS.json` |
| `recent_commits/verify_receipts.py` | Pinned source files and recorded compiler-receipt data | `STATIC_AUDIT.json` |
| `recent_commits/phase5_refresh/verify_phase5.py` | New-head source pins, saved receipts, complete comparison and historical topic inputs | Phase-5 `STATIC_AUDIT.json` |
| `runtime_contexts/factor_decoder.py` | Runtime inputs, decoder certificate; `symbolic_owned.py` | Factored certificate and result |
| `runtime_contexts/profile_home.py` | Same owned helper and literal runtime/source/site data | Home profile and cuts |
| `runtime_contexts/verify_home.py` | Same helper and inputs | Independent tape/accelerated-run result |
| `runtime_boundary_optional/check_boundary_optional.py` | Three owned sibling runtime helpers and their pinned inputs | Separately labeled optional boundary result |
| `calibration/check_fresh_padding.py` | Independently transcribed finite definitions | `finite_checks.json` |
| `wellformedness/check_wellformedness.py` | Pinned DAG/source literals | Derived summaries and check result |
| `terminal_contract/check_terminal_contract.py` | Self-contained finite transition systems | Stdout compared with `result.json` |
| `review/check_independent.py` | Terminal source/draft/result, literal TM table and DAG tables | Independent review result |
| `review/check_named_kernel.py` | Independently transcribed named-syntax semantics | Named-kernel result |

The optional owned negative suites are `runtime_contexts/test_rejections.py` and `tests/test_outer_verifier.py`. They modify only further temporary copies, run only the owned checker/verifier commands, and compare explicit rejection diagnostics. The outer suite prints deterministic JSON and does not write into the original release.

The verifier uses Python `-I -B`, removes Python path/home/optimization/startup environment settings, and disables bytecode writes. Runtime programs deliberately add only their own directory to import the pinned `symbolic_owned.py`. All input/output paths are derived from `__file__`. No executed script relies on a sibling historical research directory. Python durations are diagnostics only, not proof-assistant benchmarks.

Historical Python files such as `inputs/decoder_contexts.py`, `sources/graph_compress.py`, and the source-generation scripts under wellformedness are data-only. They are never imported or executed. The same applies to all upstream `.lean`, `.v`, `.patch`, TeX and build-receipt content. Their historical paths may appear in comments or metadata but are not replay dependencies. No incoming archive executable, shell command, package manager, network request, or proof assistant is invoked by the positive replay.

The source snapshot is intentionally not a complete proof-assistant distribution. Installing a toolchain and completing formal integration would be a distinct task with additional source dependencies and explicit acceptance gates. The current replay does not claim those gates have passed.
