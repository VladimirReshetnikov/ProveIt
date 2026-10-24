# Direct-checker local polynomial improvements and index-free CRT closure

## Ready artifacts

- `LOCAL_GADGET_PROOFS.md`: universal proofs, exact baseline comparison, natural-domain requirements, and formalization boundary.
- Eleven `*quartic.json` / `*sextic.json` files: complete ordinary local integer polynomials, variable lists, expression trees, full sparse coefficients and exact metrics.
- `INDEX_FREE_CRT.md`: universal index-elimination and reused-product-scale lemmas; explicit special-function obligations and conditional witness count.
- `section.tex`: report-ready combined component.
- `SOURCE_PINS.json`: exact baseline commit, source links and local source hashes.
- `upstream/INERT_PRIME_CLOSURE_WAVE10.md`: retained predecessor proof with its SHA256 pin; the new proof is self-contained.
- `LOCAL_CHECK_RESULTS.json`, `CRT_CHECK_RESULTS.json`: sealed author-check receipts.

## Offline replay

Python 3 and SymPy are required. No network, repository executable or external service is used.

    python build_local_gadgets.py --check
    python -O build_local_gadgets.py --check
    python check_index_free_crt.py --check
    python -O check_index_free_crt.py --check

`--check` compares every regenerated JSON byte with the sealed artifact and never rewrites it. Missing or changed files fail. Checks use explicit runtime exceptions, not Python assertions. Omitting `--check` regenerates the authored JSON files. Both scripts are working-directory independent.

The local checker establishes symbolic identities, tree/DAG/degree/expanded-monomial counts and 1,845,448 finite controls. The CRT checker establishes exact symbolic clearing identities and the fixtures stated in its proof document. The mathematical proofs, not finite replay, cover unbounded inputs. Neither component claims a new Lean theorem or a smaller completed Con(ZFC) polynomial.

An independent reviewer supplies separate sparse-ring and numerical checks under the release's review directory. Those are independent evidence, not imported by the author scripts.
