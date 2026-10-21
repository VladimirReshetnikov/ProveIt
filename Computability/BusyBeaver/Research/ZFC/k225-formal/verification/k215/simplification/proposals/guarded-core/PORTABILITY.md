# Portability and execution boundary

The only positive replay entry points are the following owned programs:

| Entry point | Regenerated outputs |
|---|---|
| `check_source_pins.py` | `SOURCE_PIN_CHECKS.json` |
| `affine/review_owned.py` | `GUARDED_CORE.json`, `GUARDED_CORE_COMPACT.json`, `CLEAR_ZERO_COUNTEREXAMPLES.json`, `OWN_AUDIT.json` |
| `checked/audit_received.py` | `INDEPENDENT_AUDIT.json` |
| `checked/check_decoder_prefixes.py` | `DECODER_PREFIX_RESULT.json` |
| `refinements/audit_refinements.py` | `radix_certificate.json`, `positive_trie_certificate.json`, `AUDIT_RESULT.json` |
| `refinements/verify_positive_trie.py` | `POSITIVE_TRIE_INDEPENDENT.json` |
| `guarded_review/independent_verify.py` | `ENTRY_SUFFIX_CERTIFICATES.json`, `LOOP_BINDINGS.json`, `INDEPENDENT_AUDIT.json` |

Output paths other than the root pin check are relative to the entry point's
topic directory. These checkers derive their inputs from `__file__`. All imports
are Python standard-library imports; no received module is imported. The
phase-five source comparison is mandatory and uses the bundled
`affine/current_sources/KSource215Data.phase5.lean`, not a sibling research tree.

`verify_release.py` copies the entire sealed package to a new temporary
directory, runs with `-I -B`, cleans Python startup/path/optimization settings,
and uses an unrelated current working directory. It verifies the complete file
set before and after each replay, rejects undeclared writes, compares every
regenerated output byte-for-byte with the sealed copy, then rechecks the sealed
original. No checker requires the original workspace or a network connection.
No current compiler availability is probed in deterministic outputs. The release was tested with Python 3.12 on Linux; other interpreter/platform combinations have not been executed in this review.

The sole optional negative entry point is `tests/test_outer_verifier.py`. It
runs the owned verifier/checkers in further temporary copies to test optimized
Python, environment-based optimization even under `-E`/`-I`, changed checker and
data bytes, changed manifest, added/missing files, symlinks, and corrupt direct
checker inputs. It emits deterministic JSON and makes no original-package
writes. It never runs received code.

`checked/test_portability.py` is a separate preserved owned test, not a default
outer entry point: its detailed receipt records hashes of Python tracebacks,
which may include temporary paths. Its original validation receipt remains
pinned, while the outer suite supplies deterministic controls for the release.

All received `.py`, `.sh`, `.cpp`, `.lean`, `.v`, patch, TeX, and archive files
are **data-only**. Historical README instructions are not invoked. The only
allowlisted shell-independent invocations are visible in the verifier and its
negative test. The source snapshot is not a complete proof-assistant build.

## Bootstrap integrity

The verifier contains the expected SHA-256 of `MANIFEST.json`; that manifest
pins every payload file except itself and the verifier. Those two bootstrap
files are covered by the final ZIP's checksum and by the delivery's external
checksum record. This is integrity binding, not a cryptographic signature or
independent proof of authorship. Replacing the verifier and all hashes together
cannot be detected without a separately trusted delivery checksum.
