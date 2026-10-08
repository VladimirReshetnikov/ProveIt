# Source and evidence manifest

Research date: 8 October 2026. Prepared as a continuation for Vladimir
Reshetnikov's ProveIt unknot-recognition project.

## Pinned source

- Repository: [VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt).
- Revision: `ea2abcb115aaa58f0b193ce1e045c2def983e1e6`.
- Inspected project: [Topology/UnknotRecognition at the pinned revision](https://github.com/VladimirReshetnikov/ProveIt/tree/ea2abcb115aaa58f0b193ce1e045c2def983e1e6/Topology/UnknotRecognition).
- Ordinary macro backend: [fast/fastunknot/twist/core.py](https://github.com/VladimirReshetnikov/ProveIt/blob/ea2abcb115aaa58f0b193ce1e045c2def983e1e6/Topology/UnknotRecognition/fast/fastunknot/twist/core.py).
- Independent crossing cube: [fast/fastunknot/twist/reference.py](https://github.com/VladimirReshetnikov/ProveIt/blob/ea2abcb115aaa58f0b193ce1e045c2def983e1e6/Topology/UnknotRecognition/fast/fastunknot/twist/reference.py).
- Relevant prior work: reports 10, 11, 12 and the corresponding synthesis at that revision.

`reference/fast/` preserves the source tree used for the integration baseline.
`fast/` is that source with the additive changes listed below. The package
does not claim that its reference is the repository's latest future revision.

The user-suggested [openai/math](https://github.com/openai/math) catalogue was
reviewed as research context. No theorem from it is a proof or runtime
dependency of this package.

## Implementation inventory

| Module or file | Role |
|---|---|
| `fast/fastunknot/twist/tail.py` | Exact signed finite-threshold recurrence, reference-rank extraction, compact profile, optional expansion, original-parity recognition wrapper. |
| `fast/fastunknot/twist/streaming.py` | Bounded-composition enumeration, two adjacent state indexes, compact local-map descriptors, bounded caches, exact column elimination, optional partial-rank recognition. |
| `fast/fastunknot/braid_profile.py` | Direct RLE/word specialization of existing Seifert and Rasmussen sufficient conditions; diagnostic signature-packing comparison and verifiers. |
| `fast/fastunknot/twist/continuation.py` | Validated RLE CLI/API for structural profiles, exact homology, and recognition. |
| `fast/fastunknot/recognize.py` | Additive production option `use_braid_profile`, default false. |
| `fast/fastunknot/__main__.py` | Additive `--braid-profile` production CLI option. |
| `fast/tests/test_braid_profile.py` | Structural and production integration checks. |
| `fast/tests/test_twist_tail.py` | Tail recurrence and resource checks. |
| `fast/tests/test_twist_streaming.py` | Streamed algebra, enumeration, storage, and decision checks. |
| `fast/tests/test_twist_continuation.py` | Frontend schema, modes, original parity, and error behavior. |

The original `twist/core.py`, `twist/reference.py`, and other source files
outside the explicit patch remain unchanged. `integration.patch` contains
nine additions and two modifications, including the new frontend documentation.
`results/patch_check.json` records successful application to the pinned layout
and a byte-for-byte comparison with the delivered source tree.

## Recorded execution evidence

| Primary artifact | What it records |
|---|---|
| `results/full_validation.log` | Complete integrated unittest output: 254 methods, zero failures or errors. |
| `results/full_validation_summary.json` | CPython 3.12.14, per-module test counts, 36.700 seconds of unittest time, and execution return code. |
| `results/independent_long_twist_audit.json` | Independent formula implementation: 104 contexts, 208 signed families, 832 macro comparisons, 220 crossing-cube comparisons, all passing. |
| `results/slope_audit.json` | 500 comparisons of the central-differential slope with ordinary homology of an independently extracted turnback sector. |
| `results/benchmark_tail.json` | Thirteen paired standalone full-homology cases, seven A/B/A rounds per case, separate A/A controls, raw times, dimensions, Python/platform metadata, and measured source hashes. |
| `results/streaming_benchmarks.json` | Paired ordinary/streamed/checking measurements, raw rounds, storage counters, traced Python allocations, budgets, and environment. |
| `results/streaming_summary.csv` | Readable table derived from the streamed benchmark data. |
| `results/benchmark_braid_profile.json` | Primary paired direct-profile and production-option measurements, batch policy, controls, checked source data, and environment. |
| `results/benchmark_braid_profile_pilot.json`, `results/benchmark_braid_profile_small_repeat.json` | Additional pilot/repeat evidence; keep distinct from the primary measurement table. |
| `results/patch_check.json` | Clean patch application and complete source comparison; no repeated regression run. |
| `results/article_qa.json` | All 34 pages visually reviewed; clean final LaTeX build, formula/table/figure checks, and corrected pagination. |
| `results/independent_braid_profile_audit.json` | Supplementary read-only source/PD, mirrored, link-rejection, and dominant-tail checks; separate from the primary regression suite. |

These are executed finite tests and measurements, not proof-assistant proofs,
claims of unique knot counts, or uniform end-to-end speed guarantees. Timings
are specific to the recorded environment. In particular, the large tail ratios
measure full homology computation; those long-run knots already admit cheaper
structural recognition.

Raw benchmark records retain their own source hashes. The separate
`reference/INDEPENDENT_AUDIT_PROVENANCE.json` records original and portable
independent-audit hashes, copied result provenance, and execution status.

## Mathematical dependency and review notes

The article supplies its full bibliography. The local twist normal form,
Bar-Natan cobordism cancellation, the Khovanov unknot detector, and the
Seifert/Rasmussen criteria are established results, not new claims here.
The finite-threshold recurrence and its explicit extraction are proved as a
continuation of the pinned macro model.

For the key slope identification, the characteristic-two weight-sliding
precedent is Thomas C. Jaeger's
[A Remark on Roberts' Totally Twisted Khovanov Homology, Theorem 3.1](https://arxiv.org/abs/1109.1805).
The independent review also records compatible point actions and homotopies
from Baldwin, Levine, and Sarkar's
[Khovanov homology and knot Floer homology for pointed links](https://arxiv.org/abs/1512.05422).
The proof uses explicit invertible local slides and dot-compatible macro
contractions; it does not rely on an unsupported principle that adding any
null-homotopic operator preserves homology.

`reference/INDEPENDENT_PROOF_AUDIT.md` reviews both signs, boundary maps,
marking, slope positivity, signature packing, and its domination. Its
computational script reconstructs the formula independently and never calls
the production tail module. General research priority for twist stabilization
is not claimed. Third-party papers are linked and cited, not bundled.

## API and encoding conventions

- Coefficients are in `F2`; returned profiles retain homological degree and
  forget quantum degree.
- Generator indices are positive and one-based; run exponents are nonzero
  signed integers. Explicit Python integers are exact.
- Original braid permutation parity determines component count. The shortened
  reference may have a different component count.
- The macro-to-scanner bridge uses the original positive crossing count:
  `h_cube = n_positive_original - h_macro`.
- A tail profile contains disjoint point values and at most one inclusive
  constant interval. Unbounded implicit intervals are never silently expanded.
- JSON follows Python's decimal digit ceiling and converts integer dictionary
  keys to strings. Convert point keys back to integers before using Python
  profile helpers after deserialization.
- Tail/macro use `Budget`; streaming uses `StreamBudget`. Reference-only
  checks, partial streamed homology, and resource `UNKNOWN` are explicitly
  labeled. Full homology mode always completes every degree or reports a
  resource failure.
- The raw frontend's structural-first default is separate from the ordinary
  production recognizer, whose new direct-profile option remains opt-in.

The preserved and added code/report material is distributed under the MIT
No Attribution terms in `fast/LICENSE`; the pinned copy is also retained in
`reference/fast/LICENSE`.
