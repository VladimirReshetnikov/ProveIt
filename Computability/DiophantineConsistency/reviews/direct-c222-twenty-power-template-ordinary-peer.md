# First full ordinary review: twenty-coordinate C222 power successor

Verdict: **PASS_ORDINARY_PROOF_RELATIVE_TO_RETAINED_CONTRACTS**. There is
no unresolved finding or requested source change. This is the first full
independent ordinary review of the exact frozen successor below, not a
finite, physical-page, proof-assistant, or endpoint acceptance.

Reviewer: `/root/intake_e13`. I did not author either mathematical source
or the old page plan. ROOT supplied the successor's conceptual lead and
the author checked its proof; neither is counted here as this independent
review. No successor program, evaluator, coefficient artifact, or runtime
certificate was used.

The reviewed source directory is
`Computability/DiophantineConsistency/research/direct-c222-twenty-power-template/`.
Its complete three-member set is:

| File | Lines | Bytes | SHA-256 |
|---|---:|---:|---|
| README.md | 415 | 17106 | `3f99d14596cdd84ff49a37fcedbbd01c419d0949c01fbdd9bd2adfa5e756469d` |
| SOURCE_PINS.md | 111 | 6317 | `1bab1821e2d095ae975b1955873ed8fa78675fb06ab1af6f3eb37cd362eb1a14` |
| MANIFEST.json | 45 | 1936 | `a8dec16d8e0c5b18ed21ca394c365e4c24e413bb26cd5b06690adff58e8016bf` |

The manifest's two payloads total 23423 bytes. I authenticated exact member
names, complete bytes, hashes, line counts, and declared totals. Its latest
actual Git association observed during this review was
`4bfd6cd87f99a9f83460edccdddf807c6591fd6f`; that observation is not a
commit or acceptance made by this reviewer.

I read all 415 lines of the successor, all 111 lines of its pins and all
45 lines of its manifest. I also freshly reread the complete 510-line
parent proof, its 80-line pins and 38-line manifest. The exact mathematical
parent is `research/direct-c222-one-page-template/`, at actual commit
`674fbc315ac72fc8d2a66428f4d736a17ddc00ae`:

| File | Bytes | SHA-256 |
|---|---:|---|
| README.md | 22327 | `11280fd509b34641e500a8b733778f663bce713c83958d18fb457ed19cb5acb2` |
| SOURCE_PINS.md | 5761 | `39ba11616a9ea6d10b5ea0d08a5e57e3249aa7bce20d06f09988810596a640f3` |
| MANIFEST.json | 1464 | `5fd0b9115ec010c0bb626d0ff7f97cc9a23583d0a10705cf37c4972f5c9913bf` |

Its complete current three-file tree and the three actual Git blobs agree.
The earlier full parent peer MD/JSON remain unchanged. Their substantive
review covered the ordinary positive-power interface, both all-primes
binomial-CRT directions, explicit label majorants, beta gluing, logical
flow and fresh completeness. This review does not turn that earlier peer
report into an unqualified endpoint or formalization acceptance.

## Complete local polynomial and natural maps

I independently compared all twenty private coordinates with the old
twenty-seven-coordinate tuple. The successor keeps nineteen common
coordinates and replaces the old natural quotient by
`f = f_old - 1`. Its six definitions are exactly

\[
 A=a_0+2,\quad Y=k+y_0,\quad V=Y^2(d+1),\quad
 B=1+4Y(f+1),\quad \tau=m+g+1,\quad W=n+w_n.
\]

These six names are local polynomial abbreviations, not coordinates. In
particular the local `B,S,R,g` are independent of the arithmetic front
and of every other private copy. The new tuple has twenty distinct
coordinates; no common frame or witness has been silently shared.

At fixed natural `n,m` and `k>=1`, an old zero has `Y=k+y0>=1` and
`B=b0+2>=2`. Its defining equation `B=1+4Y*f_old` excludes `f_old=0`.
Consequently projection to `f=f_old-1` is a natural map, and all six new
definitions recover the old values. This argument requires no power
semantics or binomial decoding.

Conversely, the new tuple restores the six definitions, `f_old=f+1`,
and `b0=B-2=4Y(f+1)-1`. Since `Y>=k>=1` and `f+1>=1`, `b0>=3`.
Every restored coordinate is natural. There is no rational witness,
quotient division, or extra bound such as `W>=m`.

I checked the full ordered residual correspondence, not only a norm:

| Old row | Residual | Under the inverse map |
|---:|---|---|
| 1 | A-a0-2 | identity zero |
| 2 | Y-k-y0 | identity zero |
| 3 | B-b0-2 | identity zero |
| 4 | N(A,X,Y) | new 1 |
| 5 | N(A,U,V) | new 2 |
| 6 | N(B,S,R) | new 3 |
| 7 | B-1-4Y*f_old | identity zero |
| 8 | V-Y^2(d+1) | identity zero |
| 9 | B+U*bplus-A-U*bminus | new 4 |
| 10 | S+U*splus-X-U*sminus | new 5 |
| 11 | R+4Y*rplus-k-4Y*rminus | new 6 |
| 12 | X+Y*n+tau*xplus-Y*A-m-tau*xminus | new 7 |
| 13 | 2*A*n-tau-n^2-1 | new 8 |
| 14 | tau-m-g-1 | identity zero |
| 15 | W-n-wn | identity zero |
| 16 | W-k-wk | new 9 |
| 17 | N(W+1,A,W*Z) | new 10 |

Here `N(a,x,y)=x^2+y^2-1-a^2*y^2` denotes the norm polynomial, not
the outer amplification coordinate. Thus seven old residuals vanish
identically and the other ten are exactly those printed in the successor.
The sum-of-squares pullback identity `P27 o iota = P20` is a polynomial
identity over the integers. Its natural-witness conclusion uses the stated
positive-index restriction; no zero-index extension is claimed.

The local composites are identities on their respective natural zero
sets. Projection after inverse sends `(f+1)-1` to `f`; inverse after
projection sends `(f_old-1)+1` to `f_old`, recovers `b0=B-2` by the old
row, and recovers every other deleted coordinate by its old defining row.
All retained coordinates are fixed. For positive base and index the exact
retained old power theorem therefore supplies both new power directions.

## Eighteen slots and both complete global maps

The complete arithmetic front, all constructor formulas and all twenty-six
outside residuals match the parent. I checked the four denominator indices,
eleven numerator indices and denominator selectors in their printed
order. They remain

\[
 (t,t+1,y+1,x),\quad
 (F^2+t,C,a,b,c,d,S,T,u,v,J),\quad
 (0,0,1,1,1,1,2,2,3,3,1).
\]

The slot ledger is complete and its dependency order is sound:

| Slots | Base and index | Reason before that use |
|---|---|---|
| 0 | 2(t+1), t | t=16+h>=16 |
| 1 | B, x | B=1+beta>=1; first slot gives F>=1 and endpoint gives x>=F+1>=2 |
| 2 | BH, x | H=2+sum of nine positive representatives>=11; same x bound |
| 3--6 | q; t,t+1,y+1,x | q=2+g>=2; y=F+1+e>=1 and preceding bounds |
| 7 | q+1, F^2+t | q+1>=3 and F^2+t>=16 |
| 8--16 | q+1; C,a,b,c,d,S,T,u,v | every representative is 1+xi>=1 |
| 17 | q+1, J | constructors are nonnegative; J has its explicit final +1 |

For a new global zero, restore only slot 0 first. Its already positive
arguments license the retained power theorem and yield F. This licenses
the remaining local inverse maps; it does not presume all eighteen power
meanings in advance. An old zero has the identical first-slot bootstrap.
The proof uses no later carrier digit, local C222 row, rank, CRT meaning
or consistency assumption to obtain call positivity.

The global projection fixes all sixty-eight front/digit coordinates and
projects all eighteen private blocks. The inverse fixes the same entire
front and restores all eighteen old blocks after that bootstrap. Every
outside residual is literally unchanged; every private residual vanishes
by the full local table. Both global composites are identities on every
named coordinate, and the whole pullback identity follows from the local
identity plus the unchanged outside squares. These are full witness maps,
not a selected-port or existence-only comparison.

Uniformly replacing each natural free coordinate by a positive coordinate
minus one conjugates both maps by a domain bijection. It does not require
the shifted quotient map to be valid on arbitrary ambient tuples.

## Retained ordinary proof, exact census and limitations

After restoring the full old zero, the specifically retained parent
sections 5.1--5.5 apply without a changed premise: the true binomial carrier,
all ten ranges, strict u,v bounds, full derived J range, both endpoint
rows, explicit C222 growth bounds, row-wise prime-power coverage, beta
states, large-evaluation label balance and rule closure. In the converse,
parent section 6 constructs the complete old front and eighteen fresh
private witnesses. Applying the global projection then constructs the
entire new zero. No private quotient, prime controller, seed tuple or
unrelated source polynomial is transferred across constructions.

The retained inherited foundations remain the positive-power Pell-index
criterion/classification and the exact calibrations
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`. The earlier parent
review read the whole retained primitives/calculus texts and specified
the limited reading of other inherited texts. Their exact bytes were
reauthenticated here. No claim is made to a freshly read or rebuilt
transitive Lean closure, a new object-ZFC proof, or an opaque incoming
quartic audit. The historical ZIP association is to the actual Git blob;
it remains absent from the current incoming tree and was not restored.

The hand census is exact for the printed unquadraticized family:
`20+15+33=68` unchanged coordinates plus `18*20=360` private coordinates
gives 428; `18*10=180` private residuals plus `4+1+10+11=26` outside
residuals gives 206. This is a reduction of 126 in each hand count from
the original 554/332 family. It is not an emitted polynomial census,
arithmetic-operation count, minimum, or physical-page result. Substitution
can increase degree: the actual second norm includes
`-A^2*Y^4*(d+1)^2`. Exact expanded degree/support/height, a possible later
degree variant, finite materialization and page layout remain out of scope.

## Inert authentication and preservation

The complete source and parent trees were authenticated, including the
parent's actual Git blobs. The three preserved page-plan bytes also match
their pins; this is preservation only, not a physical-layout premise.
The historical primary archive and all eleven named member hashes were
reauthenticated by read-only Git/plaintext member access, with no member
extraction or incoming-code adoption. The complete original first peer
pair, thirteen observed main/prior-draft files, both mathematical sources
and page plan were unchanged at final readback.

The companion JSON contains the exact file tables, full residual and
slot ledgers, preservation records and provenance. The initial inert
authentication record was made after the full source reads and before
the review writeup; it is not represented as a pre-read snapshot.
One preliminary `cat` requested nonexistent `MANIFEST.md`; reading the
actual `MANIFEST.json` resolved that harmless metadata-reader error.
No source was repaired or generated. No application, import, AST, helper,
mathematical evaluation, coefficient collection, Pell/prime/residue search,
Lean, TeX/PDF/render/visual tool, source/main edit, commit, runtime release
or promotion occurred. ROOT retains separate acceptance authority.
