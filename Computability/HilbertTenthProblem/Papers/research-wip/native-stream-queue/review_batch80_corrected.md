# Batch 80: corrected Tree Calculus, reset-net and sparse-lattice packages

**PASS.** The three corrected archives in commit `4e270aa46` repair the exact public-boundary defects recorded in the earlier reviews. They preserve every original mathematical report, PDF, literal program/table and mathematical fixture. No new arithmetic bound, changed zero-set theorem, or universality claim is introduced. The separate optional optimizations from the research tree are not applied.

The [portable checker](review_batch80_corrected.py) reads the immutable original archives at `aebfa386e` and corrected archives at `4e270aa46`, authenticates their bytes, checks every new manifest entry, and records all original/corrected member identities. Extraction and execution use private temporary directories. The [receipt](review_batch80_corrected.json) includes the precise changed-file sets, complete new member pins, source-AST comparisons, saved-JSON changes and targeted replay results.

| Package | Original / corrected members | Original members byte-identical | Repair |
|---|---:|---:|---|
| Eager Tree Calculus | 56 / 58 | 50 | Validate both exact natural application codes before cache lookup |
| Reset Petri nets | 84 / 87 | 78 | Validate duration flags, supplied markings and initial counters |
| Sparse lattice certificates | 49 / 52 | 42 | Require exact immutable canonical polynomial terms |

All 194 listed checksum entries match, and the three manifests cover every corrected member except themselves. Four implementation modules change. Removing exactly the new boundary guards, and restoring the old initial-counter assertion, makes their entire Python ASTs identical to the original modules. The new guards and their placement were read separately; AST equality of the remaining code is evidence of the limited change, not a proof that arbitrary new guards would be correct.

## Corrected contracts and preserved mathematics

**Tree Calculus.** `Evaluation.app` rejects negative, Boolean, floating, subclass and other noninteger arguments before cache or active-call lookup, budget checks, or state mutation. This closes both directions of the Boolean/integer cache collision and the negative second-argument escape. On the declared domain, exact nonnegative integers pass the new predicate, and the entire former body executes unchanged. The polynomial verifier was already strict. The fixed external proof-row bound, nonunique base witnesses, exact-size canonical uniqueness and enormous unmaterialized fixed codes retain their previous meanings. See the [original proof/source review](review_eager_tree_aebfa.md).

**Reset nets.** `compile_peak` now requires exact Boolean duration options before their values can choose a padding coordinate or affect the declared count. `fire` rejects non-dictionaries, unknown or nonexact place names, and any marking coordinate that is not an exact natural integer. `initial` enforces its two natural counters with explicit exceptions. Valid markings execute the same consume–reset–produce body, so weighted overlaps and debt accounting are unchanged. The schema parameter and caller-supplied net/transition structures are not comprehensively hardened by this narrow repair. The natural-only duration-padding qualification remains; the correction does not promote it to real-witness exactness. See the [original review](review_reset_petri_net_aebfa386e.md).

**Sparse lattice polynomials.** Direct `Poly` construction now requires exact tuples, exact integer indices and coefficients, sorted indices, nonzero coefficients and distinct sorted monomials. Negative indices remain free-parameter references, and repeated indices remain powers. `Poly.make` is still the canonicalizing interface; valid producer arithmetic is unchanged. Rejecting floats closes the demonstrated false zero at witness `2**60+1`, where the intended exact residual is −1 and score is 1. This does not change the already-strict bound-export verifier or establish authentication of a caller's intended problem instance. See the [original review](review_sparse_lattice_aebfa386e.md).

## What was replayed

The new correction suites were read and run normally and with `python -O`, all in private copies:

- Tree: all five test groups, covering 303 parameter scenarios per run. An additional isolated comparison executes the actual original and corrected evaluators on 180 valid pairs and compares their complete generated certificates, not just return values.
- Reset: each run rejects 64 calls, matches nine full schema hashes, checks 388 stored legal firings and 72 weighted reset/output overlaps. The review additionally regenerates all nine complete schemas from both actual producers and compares their complete serialized contents.
- Sparse: each run rejects the 24 malformed constructor categories and the float false-zero instance, checks exact arithmetic and mutation isolation, and compares all 2,700 expression coefficient lists with the actual original producer. The normal and optimized receipts match exactly.

The optimized runs establish the tested explicit boundary contracts. They do not certify assertion-dependent historical checkers under optimization.

Every changed old JSON receipt is checked structurally. The only altered old values are the four corrected source hashes and, in the sparse release summary, insertion of the new `poly-exactness` stage. Hash replacements must identify the actual corresponding old/new source bytes. No mathematical result is normalized away. All preserved fixtures remain byte-identical, including compressed fixtures themselves; no gzip normalization is needed for this delta comparison.

The unchanged full historical suites were already run on original and privately repaired packages in the linked reviews. They were not repeated here, and the corrected authors' claims of complete new-package replays are not substituted for a fresh run by this review. The narrow source changes, complete unchanged-artifact census, targeted new suites and actual baseline comparisons are the evidence for this correction audit.

## Reproduction

With a checkout containing both pinned Git objects:

```sh
python review_batch80_corrected.py \
  --repo /path/to/Proofs \
  --expect review_batch80_corrected.json
```

`--output PATH` writes a deterministic receipt. Saved JSON comparison is recursively type-sensitive and remains active under optimization. The review needs only the standard library; all subprocess tests use the invoking Python executable. No repository, original archive, maintained compiler or PDF is modified. A fresh replay reproduced the saved review receipt byte for byte.
