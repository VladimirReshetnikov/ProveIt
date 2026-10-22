T4-4094: a fully materialized coefficient backend for Con(ZFC)

Result
------
The same blank-K215 Diophantine arithmetic interface can use B=2^(5^11),
rather than the previous T4 backend's B=2^(5^18). This is a factor 78,125
reduction in the bit length of B-1. The finite tile alphabet drops from
37,075 to 4,094. The four fixed coefficients have now all been expanded.
No polynomial variable-count or degree reduction is asserted here.

The four exact numeric ports are, in order:
  beta, K, MC, MF_source.

Do not confuse MF_source with the unshifted native field mask. The files
expanded/{beta,K,MC,MF_source}.bin are unsigned minimal-width big-endian
integers, with zero padding only in the leading partial byte. Their exact
bit lengths, byte lengths, SHA-256 hashes, and population checks are in
expanded/MANIFEST.json. The total uncompressed coefficient data is
25,421,252 bytes. No conversion of the multi-million-digit integers to
decimal is necessary.

Main files
----------
COEFFICIENT_PROOF.md: ordinary mathematical proof of the changed compiler.
COEFFICIENTS.json: exact fixed sparse recipe and all scalar parameters.
tiles4094.json: complete canonical finite alphabet.
verification.json: construction-side finite checks.
independent_count.json: independent center-class count.
independent_audit.json: independent language and coefficient audit.
expanded/MANIFEST.json: numeric coefficient receipt.
sources/k215_transitions.json: pinned literal transition data.

Reproduction (standard Python only)
-----------------------------------
python load_coefficients.py             # fast hash/size/bit-length check
python load_coefficients.py --rebuild   # complete re-enumeration and rebuild

For programmatic use: import load_coefficients; ports=load_coefficients.load()
This returns the four integers in the documented order.

Individual checks:
python build_coefficients.py
python independent_count.py
python audit_compact.py --materialize

The first two scripts are self-contained. The independent audit reads
only literal data and does not import the construction program. The
optional exploration subdirectory is not part of the final construction.

Trust boundary
--------------
The new finite geometry, language, coefficient arithmetic, and numeric
expansion are checked. Universal compiler/Pell lemmas and the exact K215
halting/ZFC-refutation endpoint are inherited mathematical theorems. No
new full Lean/Rocq formalization, K215 halting run, or proof of Con(ZFC)
is claimed.
