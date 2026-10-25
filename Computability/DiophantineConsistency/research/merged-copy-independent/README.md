# One monomial for both color-copy families

[PROOF.md](PROOF.md) gives the complete ordinary native proof and both
positive P66 witness maps for the length4049 tuple. The shared color-copy
term is exactly one `rho^18` monomial. It replaces the previous two terms
`rho^20+rho^30`; the only other local bare term copies selector0 to the
zero-weight marker1008. This is a reduction in the fixed recipe as well
as in the field length. The whole front still uses fifteen positive
variables,66 integer-leaf operations and degree157.

The new positions are south943..951, north961..969, west972..979,
east981..988, dummies970/971, and marker1008. The one shift18 copies
south to north tests961..969 and west to spatial tests990..997. Spatial
shift9 supplies east to those same spatial tests. Their complete unwanted
preimages are absent. Both clause blocks, at1998 and3007, retain exact
count/label decoding and reset predecessors `Aadj` and `Aadj+c_0*a`.

The clean clauses supply at most one selector and all copied labels before
alignment. In the forced Start cell, positive south bits give tests962..969
and copied selector0 gives test1008. After excluding fractional shifts,
any nonzero field offset lies in20..962. Offset20 forces tile942 and its
south bit0 to be one, contrary to its complemented south74. Every offset
21..962 requires two selectors in the same cell. The marker consequently
remains the shifted Start indicator `a_j=x_(0,j+width)`, with no all-one
occupation-flag assumption.

The proof gives a global carry bound29, the tighter low reset
`9+3*rho/4+29<rho`, and every changed predecessor, padding bit and origin.
The final product field4015 resets; all875 padding tests lie in18 full
zero fields4016..4033 plus29 low bits at4034. With `L=4049`, `d=190303`,
the exact safe increments have local/spatial/temporal maxima3977/979/970.
The full rank identity, strict representative bounds, whole-modulus
Boolean subset construction and positive outer maps are restated for
these exact parameters.

The separately authored final [verifier](certify.py) and
[certificate](certificate.json) discharge the complete finite Pcm18
condition. The proof author read the whole verifier and reproduced normal
and optimized read-only checks; explicit exception guards remain active
under `python3 -O`, and both generated JSON files compare byte for byte.
The earlier [finite probe](../merged-copy-probe/NOTE.md) remains preserved.
The support has980
physical positions and977 nonzero coefficients. It reports934
support-compatible offsets: zero,932 multiple-selector exclusions and
the single tile942 exclusion at20. Exact orders are23 and506=2*11*23,
spacing506, auxiliary prime `lambda=190763=377*506+1>d`, H residues
34,3240,43425 and lift quotient65850. The complete four-port tuple costs
95205 raw bytes,1841 fewer than marker1031's97046. The shared18 monomial
is explicitly checked to occur once in the kernel and all three complete
modular evaluations. The [independent mathematical and finite review](../../reviews/merged-copy4049-independent-peer.md)
reports no unresolved new gap, including a separate reconstruction of the
layout, copies, offsets and whole integers without project imports.
Printed-page measurements remain a separate check.

| Port | Bits | Minimal unsigned bytes | SHA256 |
| --- | ---: | ---: | --- |
| beta | 190303 | 23788 | `0e939f9aa81d78e1536799efbaee787ace37a7e76c1fae30b0f31ae395da4c0a` |
| K | 190727 | 23841 | `6919cc23600464c5c80262a3f9b68b93ed7dd1f6e945e7b86f73c4acebaaa7cc` |
| MC | 190303 | 23788 | `5d856922192b8e66cbf10b9f87629df165a4a40643e9002a3e3b331613a5ba28` |
| MF_source | 190304 | 23788 | `7a25246bf134cd1b95ef6bd2fc50e13b15e9f740d04fa4e11d5e4a02287c8990` |

The proof SHA256 is
`43fb060f197f352ed4b1fe9870ca8fa8a7a1f9a4cfae1967882981767167d64e`.
The final verifier SHA256 is
`0e1768e6e22373b0717f149994b62e24324909f0ad4843de217f96a16248f5b0`,
and the certificate SHA256 is
`6c575be486c16145c92d278086fcf3e7ab08342628b1070392b98bff73e672b3`.
The proof author is `/root/complemented47_review`; separate authors handle
finite implementation and independent review. Soundness uses no new
controller premise; completeness uses exactly Pcm18 in section11, now
discharged by the bound certificate. The theorem is relative to the
retained named ordinary arithmetic, complete syntactic-refutation and
foundational calibration contracts. No new transitive proof-assistant or
internal-ZFC replay, consistency decision, actual unsolvability or global
minimality is asserted. Accepted predecessors remain unchanged.
