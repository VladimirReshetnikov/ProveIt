# Candidate K coefficient-to-byte bridge

The checked in-Lean Fin986 recipe expresses `K` as three separate sentinel
powers plus coefficients at positions 0–985 with exponent `1005 - i`. The
checked literal-vector union replaces those coefficients by fixed
in-Lean literals, but does not bind an external JSON file. The
independently audited external byte decomposition uses 2,021 little-endian
base-`2^47` digits, grouped eight at a time into 47-byte blocks plus a
five-digit/24-byte tail.

A candidate formal radix-digit layout is: 18 zero digits; digit 18 equal to
one; digit 19 zero; the 986 coefficients in reverse order at digits 20–1005,
with one added at digit 1004 for the separate `r^1004` sentinel; 1,014 zero
digits at 1006–2019; and digit 2020 equal to one. In particular the
`r^1004` collision must be accounted for explicitly. The `r^18` and
`r^2020` sentinels occupy separate digits. A proof must establish this layout
from the exact in-Lean coefficient recipe and handle all bounds/carries;
this paragraph is a proposed indexing derivation, not a Lean theorem. The
[external checker](check_layout.py) independently evaluated this layout
against the pinned coefficient array and decompressed K snapshot; its direct
author run exited 0, with 2,021 digits and the collision at index 1004.
Checker SHA-256:
`8b86dcde6572072ca3ac42b57149a6d57eaca6b84298bd067a202adb1046f228`.
This is external Python/snapshot evidence, not a Lean digit or file theorem.
An [independent external audit](../../reviews/nine-sharing-sign17-k-byte-bridge-design-independent/README.md)
also reconstructed the 2,021 digits directly by division and verified the
collision value `c[1] + 1 = 30099357829123` and all radix bounds. This
remains external evidence, not a Lean or filesystem theorem.

One route is a generic theorem relating `Nat.ofDigits` of a reversed finite
coefficient vector to the shifted finite power sum, followed by a separate
digitwise sentinel-addition identity and proofs that all resulting digits
are below `2^47`. The already checked [aligned-block composition](../nine-sharing-sign17-mc-compose-core-retry-check/README.md)
can then combine independently checked 47-byte/radix blocks and the 24-byte
tail. K has many distinct blocks, so a staged finite-block approach is
needed; no completeness, resource bound or Lean byte equality is asserted
here. External file/gzip/JSON correspondence remains an explicit boundary
unless separately formalized.
