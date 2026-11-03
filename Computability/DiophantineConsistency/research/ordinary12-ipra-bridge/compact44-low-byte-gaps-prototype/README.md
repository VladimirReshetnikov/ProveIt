# Six support-free runs of symbolic MC byte windows

`CompactLowByteGaps.gap_byte` proves in Lean that each symbolic low-mask
window `(lowNat / 2^(8*j)) % 256` is 255 when `j` lies in any of these
half-open intervals:

```
[7898,8225), [8317,8392), [8643,8895), [8920,9163),
[9179,18375), [18392,27596).
```

They contain 19,297 indices. The proof checks symbolically that both
adjacent base-`2^67` digits are in range and outside the concrete support;
the previously checked all-one window lemma handles every bit offset.
This is a parameterized symbolic theorem, not an equality to a byte literal
or an assertion about a filesystem payload.

The separate `check_gaps.py` external observation verifies that the
hash-pinned parent MC gzip payload decompresses to 255 in those six
intervals. It also independently checks that the six intervals, prior
prefix `[0,16)`, dense run `[17,7890)`, and tail `[27613,73751)` are
disjoint. Together these individual Lean results cover 73,324 of 73,759
symbolic byte indices. The exact nine still-uncovered half-open intervals
are `[16,17)`, `[7890,7898)`, `[8225,8317)`, `[8392,8643)`,
`[8895,8920)`, `[9163,9179)`, `[18375,18392)`, `[27596,27613)`, and
`[73751,73759)`, totaling 435 indices. This arithmetic coverage count is
external and the disparate theorem right-hand sides have not been joined
into a global Lean byte-literal equality.

The bounded mixed-provider author check `observations/attempt01` exited 0
in 3.304 seconds with no warnings or `sorryAx`; its direct dependency and
companion guards and separately inventoried generic provider remained
unchanged at the recorded points. Source SHA-256:
`a54eb7d7e0865d39e53eb633f68b6b1d23d3bfaff06a06005b403bc2f1d0cbab`;
object SHA-256:
`ce69f765958f676f45e375edbe68c025392661cbc7128e970a06a199fd2e9686`.
Lean reports `[propext, Classical.choice, Quot.sound]` as metatheory
dependencies, not iPRA axioms. The external checker SHA-256 is
`8bbf3d863a1d7d1087164a5c783c617e4ad2f10ace889fcdb8fefe9f548fab1a`
and its recorded output SHA-256 is
`5c0f25bfdc5c83ee3170e5a289c75d2412886971d2da50cb587e5280dc4922e4`.
This is an author-side check, not a paired replay or complete
symbolic/package/dynamic ancestry audit. External file/gzip correspondence,
the parent-to-supplement connection, PDF and iPRA result remain open.
