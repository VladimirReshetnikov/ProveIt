# Independent review of the two-anchor L=7691 construction

**Result: pass for the complete new ordinary argument and finite certificate,
relative to the explicitly retained ordinary arithmetic, machine-calibration
and syntactic-refutation contracts.** No unresolved gap was found in the new
weighted-clause, alignment, carry, padding, canonical-slack or controller
arguments. This review does not turn the inherited contracts into an
end-to-end proof-assistant or internal-ZFC formalization.

The reviewer read all 565 lines of the final
`research/two-anchor-independent/PROOF.md`, the complete README, the entire
new `certify.py`, and the complete certificate. The proof was authored by
`/root/complemented47_review`; ROOT authored the new finite code. This
reviewer authored the earlier hash-pinned parent decoder/three-anchor
verifier, whose reuse is explicit below. Thus this is independent review
of the new proof and implementation, not a claim that the complete decoder
was independently implemented twice.

## Complete tuple and weighted decoding

The source fixes every old tile/action/seed datum and preserves the same
componentwise complemented color bijection. The new coefficients make the
two physical flags at 1095 and 2195 have weights M and 2M, where
`M=2^44`. Removing the old M at 3296 leaves the full coefficient sum
unchanged. The maximum is now **2M**, not M. There are 979 nonzero
coefficients and 981 physical positions including both dummies.

The count proof covers every incoming carry 0..29. Since `n+k<1024`, the
nine count bits force n<=1. The payload congruence then gives W=0 and both
flags zero in an empty cell, or the complete complemented label payload
and `a+2b=3` in a genuine cell. Boolean a,b therefore both equal one.
This individually recovers the flags without a prior equality premise.
The occupied raw clause is `2^46+1<rho`, with zero outgoing carry.

The complete mask recipe is coherent: one copied-anchor test disappears,
the core population becomes 109, and 872 padding bits make the native
population 981. The source mask is shifted by exactly one beta. The
closed and positive-sum padding expressions agree. The scalar boxes and
origin residues are sufficient for the retained presemantic outer recovery;
no old K-specific native interpretation is silently transferred.

## Carry bound and all-phase alignment

I checked the possible overlap in the extra upper-dummy allowance carefully.
The Boolean reflected contributions sum to at most Csum: two uses of a
single coefficient would require an absent support difference 1102. The
three bare terms and spatial term contribute at most four. An extra 0/2
dummy has bare/spatial output positions at most 2163, while any reflected
dummy output is at least 3261. These cannot overlap. Within either family
the extra dummy cannot hit two coefficients at the same output. Its full
allowance is therefore **4M**, including the heavy 2M anchor coefficient.

The stated Csum bound consequently gives
`Uraw<(231/8)*rho+965474`. Adding an arbitrary temporal phase and carry29
still gives a total below `30*rho`. The finite monotone cyclic carry map
therefore has a fixed point in 0..29. This argument permits arbitrary
temporal offset and fractional phase, and soundness only identifies its
digits with F after the outer argument has already supplied strict F.

The decisive new geometry is that reflection starts at **2198**. For every
position 0..2197, three bare terms plus the spatial term are at most 12,
even before using the decoded cell structure. Together with any temporal
digit and carry29 this is below rho. Thus every outgoing carry in this
whole band is zero before alignment. A refined carry11 estimate is neither
assumed nor needed.

The recovered Start south color is 510. Its bit1 is one at physical984,
which contributes alone at target1014. The current flag1095 contributes
alone at target2195. Both tests receive zero incoming carry and demand odd
temporal digits. Phases1..45 give even temporal digits; phase46 permits an
odd spill at only one residue, from the upper dummy. Hence the phase is
zero. The only E2 difference1181 is `2195-1014`, so the remaining digit
offset is also zero. This uses the actual decoded Start bit, without
assuming occupation, unique Start, or a chosen soundness stride.

## Every tested field, the interior padding and nonzero final digit

The full support checks establish all nine temporal and eight spatial
label-copy fields, the single anchor field, both full clauses and both
clause predecessors. Once aligned, the copy fields are exactly sums of
two Boolean bits with zero incoming carry.

Both clause predecessors are Aadj. The missing differences1103 and1101
exclude the other reflected band. The heavy anchor has no supported
immediate predecessor, so it does not increase Aadj:
`Aadj<=2M-1024<rho-29`. Thus both clauses receive zero incoming carry.
No assertion of global carry-freeness is made.

The padding predecessor6707 is exactly
`c_983*x_2195=2^35*x_2195`, rather than c0 times a flag. Its incoming29
cannot overflow. Every field6708..6747 is formally zero: the only possible
large input2195 would require coefficient982 down through943, all absent.
This establishes all eighteen full tested fields and the low26 bits at6726.

The last field7690 is exactly `c0*x2195` before incoming carry. Since
`c0<M`, its digit is at most M+29 and its outgoing carry is zero. This
resets the next cell origin even though the last digit is usually nonzero.
The proof consistently uses **M+30** for the full-number bound; it does
not rely on an obsolete carry11 or a zero top tail.

Spatial equality propagates occupation from forced Start through the
one-cell rotation cycle because all genuine complemented colors are
positive. Full temporal label equality rules out zero stride at Start.
The inverse color bijection then reaches exactly the retained marked
computation/refutation contract.

## Fresh canonical subsets, actual rank and controller

Canonical words are rebuilt at E2 rather than reused from the old tuple.
The fixed point is constructed before choosing strict F. Occupied clauses
give positivity, and the highest-field bound gives
`0<F<q*(M+30)/rho<q/7`. The C word has 5495 absent top fields, giving
`C<q/rho^5495` and hence `2C+F<q/3`. These estimates apply to every
simultaneous safe low-dummy subset. They are strong enough for all retained
outer-converse uses.

The binary rank identity uses the actual defining R and the once-shifted
source mask. Disjointness gives `pc(R)=3t+2`, and the separate low-origin
calculation gives `R=3 mod4`. Neither fact is inferred from a claim that
the entire native convolution has no carries.

For each interior dummy increment, the exact local degrees are at most
6558,1105,1063. Kernel residues are distinct, all coefficients are below
rho, and the relevant cells lie strictly inside the word. Thus
`0<deltaRaw<q/rho^2<q/7`. Since `F_old<q/7`, the ordinary sum remains
below q-1; congruence therefore lifts to the exact equality
`F_new-F_old=deltaRaw` at every intermediate subset. The resulting
`deltaR=-Gamma*B^j` is a difference of actual ranks.

Under Pc2, Gamma is a unit at every prime divisor of dN. The proof checks
both new d-prime orders, and the new H at all three primes; it does not
transfer a controller unit from the old K. LTE and CRT give the full
orbit modulo dN. The consecutive-coordinate subset argument uses an a0
coprime to the pure lambda-power orbit length, and the stated bounds keep
every selected physical bit, spatial translate and width translate inside
the word. The optional B^3 cell is distinct from the other selected cells.
Consequently the final actual R, rather than an independently selectable
rank, has the required residue. The resulting positive w,z obey the exact
transport equation.

The final P66 soundness and completeness maps retain their original
positive bridges and coefficient-independent arithmetic hypotheses. In
particular `T_old=f*T` and `i_ordinary=Delta*i` are positive multiplication
bridges, not divisions of supplied witnesses. Since d,N,R remain odd, the
required square conditions survive. Completeness correctly gives actual
`Ns=Delta` and the other five factors one. The unchanged symbolic front
therefore remains degree157 with fifteen positive inputs and 66 integer-leaf
operations; the differently specialized old and new polynomials are not
claimed to be pointwise equal.

## Finite code, one resolved issue and independent executions

The new verifier reconstructs the complete seed/action/tile data through the
previously reviewed parent, changes exactly the stated anchor coefficients,
builds all four integers, checks the whole finite support/copy/clause/padding
geometry, and verifies the controller through three agreeing K evaluations:
dense reciprocal Horner, direct selector/control expansion, and reduction
of the complete integer K. Prime checks use deterministic trial division;
order tests cover all prime factors, with separate base2 tests and gcds.

I raised one provenance issue in the first reviewed version: hashing the
parent Python file alone did not bind the TeX seed input when its decoder
was called directly. ROOT fixed it before the final runs. The final model
also verifies the exact source-page SHA-256 before decoding, and the new
certificate records that page hash. This issue is resolved; it changed no
constant or numerical result.

After reading the complete code and its final change, I ran:

```sh
python3 Computability/DiophantineConsistency/research/two-anchor-independent/certify.py
python3 -O Computability/DiophantineConsistency/research/two-anchor-independent/certify.py
```

Both executions passed and matched the saved certificate byte-for-byte.
Every check uses an explicit exception rather than a Python assertion.
The commands did not regenerate the certificate or edit sources. The code
imports the explicitly hash-pinned reviewed decoder; it does not execute a
native compiler, an incoming paper program, Lean, TeX or a PDF builder.

The finite results include
`lambda=2122441=12*176870+1>d=361477`. Primality is checked through the
complete trial-division bound1456. The lambda square residue is1613482,
and the valuation-one certificate is

```text
B^(lambda-1) mod lambda²
  = 2326944557674
  = 1 + lambda*1096353,   0<1096353<lambda.
```

| Modulus | B | K | H=1+BK+B² |
| ---: | ---: | ---: | ---: |
| 47 | 42 | 11 | 18 |
| 7691 | 4045 | 5146 | 6993 |
| 2122441 | 1600611 | 926333 | 1324284 |

The complete minimally encoded unsigned big-endian ports use respectively
45185,45432,45185,45185 bytes for beta,K,MC,MF_source: **180987 bytes**
total, 26227 fewer than the three-anchor tuple's207214. This is a raw
four-port size comparison, not an expanded-polynomial or rendered-page
metric.

## Reviewed versions and limits

| File | SHA-256 |
| --- | --- |
| two-anchor-independent/PROOF.md | `6df09c6637d32be89b60f767a876f70c1b2be5cf9d047b1add07252a257abe23` |
| two-anchor-independent/certify.py | `85cf6b14aab797c3b607b800ebbb3d6e9b51f1be2a3dedf08b8a56fe5da4116c` |
| two-anchor-independent/certificate.json | `7d3db2089a55cefed6afa9e7df8ee5ffcc64d94a628cbffc261abf352dfa5c3e` |
| complemented47-controller-independent/certify.py | `318665c36d7600a99dbddbacca11ef9a2d30f65e04a761efe25d1f3653e662ed` |
| pinned radix55 equation.tex | `440cf0853ec2f992db7aa6146aec42c189368375d8db725d3df085ca27dc4dff` |

The new finite Pc2 condition is discharged for these concrete constants.
The complete new native bridge and its canonical converse pass this
ordinary mathematical review under their explicit retained contracts.
This is not a consistency decision, proof of actual unsolvability, global
minimum theorem, new end-to-end formal-kernel replay or automatic approval
of a separately generated page. No proof, verifier, maintained page or
coefficient file was edited by this reviewer, and no commit was made.
