# Source identity and dependency

The report and its companion were prepared on October 2, 2026. `sources/inventory.json` records the exact bytes, SHA256 hashes, origin labels, and purpose of every source snapshot. Each source hash is also pinned in the reviewed verifier. These are local scientific provenance records, not cryptographic signatures or independent proof certificates.

## Typed historical check receipts

- `independent_extension_checks.json`: a factual receipt of separately performed bounded character, Gaussian, gamma-ratio, coefficient-conversion, and inverse-reversion checks
- `check_avoidance_recurrence.json`: a factual receipt of a separate finite recurrence cross-check of the first two avoidance corrections

The historical working scripts are not shipped. These receipts are schema-checked provenance, not independently regenerated results of the shipped commands. Report140's intended mathematical executable is `code/exact.py`, using the Python standard library; it independently recomputes the finite ranges and identities specified in `checks/fixtures.json` and compares every result with that fixture. The supported replay covers the first Gaussian avoidance correction and finite character, model-product, discrete Taylor, gamma, moment-conversion, shift, ratio, and inverse-reversion checks. It does not claim to rerun the separate avoidance-recurrence calculation or to prove analytic remainders.

## Frozen Report138 dependency

The included corrected ZIP is an unchanged separately delivered dependency. Its leading-only scope is preserved.

- Report138 TeX SHA256: `7d8c2a5a280658ef5f09ea2f7caea3f27b68206a7a3e99fa9c25ebebb7f8d428`
- Report138 PDF SHA256: `7624a807149ae5f898b3acc02f44709a1e6033aae7ff432172c6283b897b013a`
- Report138 corrected companion ZIP SHA256: `360c9db76eb482a21b75396b0b71941e1399ad27803441e25f945c6c03c2c484`
- Report138 nested manifest SHA256: `94f2d85f4ee8e08518bda16e51fcaf984e96deb673aeadb3b259f1faa10afb77`

The Report140 package manifest inventories all deliverable files, including this entire dependency ZIP. The verifier independently checks every nested manifest record and the two baseline document hashes. No public repository, webpage, or remote release is changed by any package command.
