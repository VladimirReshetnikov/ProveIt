# Expanded 122-module source preflight

`check.py` constructs a topological plan for the reverse-reachable cone of
the five confirmed nine-prefix producer drifts and the two additional
byte-matched adaptive producer-record drifts. All 122 selected modules have
candidate source bytes matching a retained producer source hash: 114 from the
earlier source preflight, seven from the peer-matched adaptive manifest, and
one from a retained single-object receipt. Their explicit source imports match
their captured serialized header imports, excluding implicit `Init`.

The resulting ordered source paths, hashes, selected old object records and
import lists are in `observations/attempt01.json`, SHA-256
`9301af84fed06648711462da4b4a5b9524467442128f533e9846b7bee857fcb4`.
The adaptive manifest hash is checked against its independently matched peer
receipt. Source-byte matching does not prove unique producer ancestry.

This is only a source/import plan, not a fresh build. Remaining historical
producer mismatches can enlarge the cone, and the build would need a single
fresh union, exact direct-object/companion and warning guards, actual
post-build serialized closure and endpoint axiom reports. Package-transitive,
dynamic and historical ancestry are inherited.
