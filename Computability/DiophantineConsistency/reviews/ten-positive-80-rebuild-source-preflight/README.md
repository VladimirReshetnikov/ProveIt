# Observed-drift rebuild cone source preflight

The plan-only reverse-reachability survey found 114 modules from the five
observed producer-time drift seeds to the fixed symbolic iPRA endpoint.
`check.py` compares their unique repository source candidates with the
retained single-stage, multi-stage or nine-prefix producer source hashes.
All 114 match. For each source, its explicit direct imports also match the
captured serialized module header's import names after omitting implicit
`Init`. The ordered source paths, hashes, producer kinds and import lists are
in `observations/attempt01.json`, SHA-256
`62334c3072ee8415120b6d8f3a8bfd8e18a0012ca1df99ee8042456bc9e1b67a`.

This is a source-byte and import-name preflight, not a rebuild or a proof
that old producer dependency bytes were coherent. The 114-module cone is
derived only from the five known drift seeds; remaining unmatched historical
objects or other drift may enlarge it. A fresh provider union, exact direct
object and companion checks, stage warning policies, actual serialized
post-build closure and endpoint axiom reports are required for a coherent
replay. Package/dynamic and historical ancestry limitations remain.
