# One weighted anchor and a selector-count copy

[PROOF.md](PROOF.md) gives the complete ordinary native argument and both
witness maps for a new tuple in the same fifteen-positive-variable,
66-operation, degree-157 P66 front. It uses one weight-three flag at
2079, clause centers 4161 and 5228, and `L=7309` fields at radix `2^47`.
The proof is relative to the retained ordinary arithmetic, complete
syntactic-refutation and foundational contracts. Its soundness uses no
new controller premise; completeness uses exactly Pc1 in section 11.
**Pc1 is now numerically discharged for this exact tuple** by the separate
certificate below. The complete
[independent mathematical review](../../reviews/one-anchor7309-independent-peer.md)
and [root review](../../reviews/one-anchor7309-root.md) pass within the
explicit retained contracts.

The main change is that `rho^1137 G_943(rho)` copies the entire selector
count to field 2079. In the forced Start cell, that count is one, and
the calibrated south-bit copy at field 1014 is one. Two odd temporal
tests exclude every fractional phase; their uniquely represented support
difference 1065 then fixes the whole-field offset. This recovers alignment
without assuming occupation and without a second physical anchor.

The count clause recovers the single flag through `1+3a=4`. The smaller
layout has 980 physical positions, 978 positive coefficient positions,
109 core tests and 871 padding bits. All labels, selectors, dummies, the
complete finite table, decoder and seed are retained. The 35 positive
control positions have the shared polynomial

    Psi(x,t)=x^1003*(x^20+t^17)*G_8(tx)
             +t^8*x^983*(x^30+t^17)*G_9(tx)
             +t^34*x^2079*(2t-1).

Its evaluations at t=2 and t=1 supply the weighted controls and their
exact support indicator. This changes the fixed coefficient recipe,
not the equation's fifteen witness variables or circuit operations.

The complete proof keeps a single global carry bound 29. The upper clause
predecessor has an additional `2^18*x_2079`; this term is explicitly
bounded, not assumed absent. All 871 padding bits lie in fields
6325..6342 and the low 25 bits of 6343, within the full zero band
6325..6364. The final field 7308 is zero after a bounded field 7307,
giving `F<q/rho`, the actual rank identities and ordinary safe-dummy
increments for every simultaneous controller subset.

## Complete finite discharge

The separately authored [certify.py](certify.py) binds the entire original
source page before decoding, the reviewed decoder, and the complete proof
below. It constructs every coefficient and all four integers, checks all
copies and both full clauses, retains the nonzero upper-clause predecessor,
and checks the entire padding band, top field and unique alignment
difference. It uses three routes for K: reciprocal Horner, direct positive
powers from the complete tiles and labels, and reduction of the whole
materialized integer. No preceding K-specific certificate is reused.

Trial division and all proper-divisor tests give the exact orders 23
and 1044 at 47 and 7309; `1044=2^2*3^2*29`, and the spacing is 24012.
The proof-only prime is `lambda=360181=15*24012+1>d=343523`.

| Modulus | B | K | H = 1+BK+B² |
| ---: | ---: | ---: | ---: |
| 47 | 25 | 1 | 40 |
| 7309 | 3446 | 4088 | 597 |
| 360181 | 149905 | 316516 | 144105 |

The auxiliary square is `B²=176616 modlambda`, and the exact lift is
`14875835482=1+lambda*41301`, with `0<41301<lambda`. Together these
discharge every Pc1 premise. The exact frozen verifier SHA256 is
`9e48fa6e071e279c271d4facc87aec2a7026369a2ab3b3056a68e33c41ae479d`;
[certificate.json](certificate.json) has SHA256
`f1d772729d85b1138205d8ab37297dcf79bfffd1338525fb59c22495adf325fd`.
After reading the entire separately authored verifier and its final
one-line magnitude-bound tightening, the proof author ran both read-only
commands below. Both exited zero and reproduced the complete certificate
and coefficient array byte for byte; no `--write` mode was used.

```sh
python3 -B Computability/DiophantineConsistency/research/one-anchor-independent/certify.py
python3 -B -O Computability/DiophantineConsistency/research/one-anchor-independent/certify.py
```

Explicit exception checks survive optimization. All four complete ports
use minimal unsigned big-endian encoding:

| Port | Bits | Bytes | SHA256 |
| --- | ---: | ---: | --- |
| beta | 343523 | 42941 | `20f6732d411098612ac394f2962db5121f827dbb2409e65fa3ec357013e3307a` |
| K | 345498 | 43188 | `9e1a87ef2fc452e0db904cb05cbcc7aa42de5a5f8fedec982f121e4129808536` |
| MC | 343523 | 42941 | `93ae05b0e97281e48f66abc1980354112282baa068867de4eb1a626c9edcf5d7` |
| MF_source | 343524 | 42941 | `8f6f0e32702dc10df78653561d76746dee3d4756e45fc8c934d9e422213bfc1b` |

Their total is 172011 raw bytes versus 180987 for accepted two-anchor7691,
a reduction of 8976. The separately rendered whole candidate instead
grows from 5083 to 5089 TeX bytes and from 2707 to 2710 extracted nonwhite
characters. The complete source and actual second visual check are in
the [page review](../../reviews/one-anchor7309-page-peer.md); raw-integer
and printed metrics are deliberately distinguished.

The proof's current SHA256 is
`62f9aba2726737f1e9a507f5d28468f402a1702d9b59e2179138382ffc75dd6b`.
The mathematical author owns this proof and README; a separate author
owns finite verification. Independent mathematical review is recorded
separately; author verification of the finite code is not that review.
The frozen proof retains its original conditional wording for provenance.
No preceding accepted artifact is changed, and no claim of
global minimality, actual unsolvability or a new proof-assistant replay
is made. Finite enumeration supplies no unbounded native or Pell lemma;
those are the ordinary proof and its retained contracts.
