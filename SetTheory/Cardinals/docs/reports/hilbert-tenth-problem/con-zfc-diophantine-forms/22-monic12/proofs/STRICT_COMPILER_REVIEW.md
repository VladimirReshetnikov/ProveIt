# Independent review of the strict four-cell compiler

Reviewed files: `code/strict_compiler.py`, `data/strict_windows.json`, and
`strict_compiler_checks.json`, together with the pinned package 11 T4
predicate, ordered alphabet and bridge proof. This is a mathematical
review and an independent finite audit, not a formal verification.

## 1. Soundness of the smaller alphabet

An independent filter, applied to the existing list of 37,075 T4 windows,
gives exactly 5,251 windows. These are exactly the new strict predicate's
windows. Adding the old globally impossible forbidden selector E gives
the claimed 5,252-element ordered alphabet. The first two selectors are
S=(434,435,436,1) and E=(438,0,0,438); the remainder are in canonical
lexicographic order. Every new selector, including E, belongs to the old
T4 alphabet.

The additional restrictions are symmetric compatibility of adjacent
phase/H classes, no working heads or written bits in a neighborhood
containing a vertical wall, no initial phase or nonhalting head adjacent
to an outgoing H cell, and the endpoint phase requirements beside a wall.
None introduces a new local behavior. Therefore every globally admissible
strict plane is a globally admissible old T4 plane. Forbidding E remains
harmless; E cannot occur in any globally admissible old plane because its
left H is adjacent to a non-H non-wall center.

This subset argument immediately transfers the old soundness theorem for
arbitrary cyclic stride. It does not assume a rectangular tableau, a
unique Start in arbitrary solutions, a coprime stride or absence of
residue collisions. Once the unchanged three overlap equations reconstruct
the pullback plane a[-x-h*t], the old marked-plane extraction applies.

## 2. Completeness and helical seams

For a finite blank halt, choose a strip with at least two unvisited blank
cells between every visited tape position and each vertical boundary.
Choose an arbitrarily long constant halted tail, an H row, then the
L...L Q R...R initialization row. The width and height can still be
chosen independently as sufficiently large powers of five.

The strengthened local predicates hold on this construction:

* The H and initialization rows are horizontally homogeneous in their
  classes, with phase edges LL,LQ,QR,RR. The first/last phase adjacent to
  a wall is L/R as required.
* Ordinary run rows have no phases or H cells; exactly one head lies in
  the interior. An outgoing H row follows only the halted configuration,
  so every head in every triple has halt state 215.
* Every triple containing a wall sees only zero ordinary symbols, L/R
  endpoints, H, or another wall position. Two unvisited blank cells are
  enough because a triple containing a wall reaches at most two interior
  cells from that wall. The construction actually used by the finite
  seam check leaves an additional cell of margin.
* At the helical wall seam, the left and right edge neighbors may come
  from consecutive time rows. Their possible codes are still only
  zero,L,R,H. The transition H-to-phase and phase-to-run seams respect
  the same endpoint restrictions: the right neighbor of a wall can be L,
  and the left neighbor can be R. Ordinary edge cells are always blank.

Thus the canonical finite halt has a strict cyclic witness, with one S
and no E. Padding its width and halted tail preserves all these facts,
so the old five-adic tuning construction remains available.

## 3. Support and shortened anchors

The new parameters are

    k=5252, a=439, ell=13, p=1075, m=7013,
    dummy positions 10520 and 10521,
    M=11839, Emax=11*M=130229,
    Hc=19*M+3*a+1=226259,
    T1=487157, T2=747619,
    b=5^7=78125, L=5^9=1953125,
    d=b*L=5^16=152587890625.

The native support has 7014 points: k selectors, four a-element copy
groups, two low dummy positions and four anchors at M,3M,5M,11M.
The bare shifts 4M and 8M test M against 5M and 3M against 11M.
The only support pair separated by 6M is (5M,11M). All non-anchor
positions lie below M, and the other anchor differences are not 6M.
The actual circular set check confirms that the two anchor-hit rotation
sets intersect only at rotation zero modulo L.

The original copy shifts and labels are retained. Root's finite target
checks verify all 3a+2=1319 convolution positions. The clause-band
separation is greater than 2Emax and equals 2 modulo 4, and both circular
separations exceed Emax. Clause terms cannot reach the low copy/anchor
tests. These are exactly the separation hypotheses used in the old
carry-free decoder; the special powers 9 and 27 in the historical
anchors had no independent semantic role beyond those properties.

## 4. The two-dummy issue

The recipe must assign clause coefficient zero to both dummy positions.
The extra high binary bit must remain permitted only at the FIRST dummy:

    MC=B-1-sum_{e in support, e != 1} rho^e-2*rho^10520.

There are m cleared low bits after omitting forbidden selector 1, plus
one cleared high bit, so pc(MC)=d-m-1=d-7014. The high mask has two
mu bands, 3a copy targets, two anchor targets and the source low bit:

    pc(mu)=2847,
    pc(MF)=2*2847+3*439+2+1=7014.

Their population sum is exactly d. There being two LOW dummy positions
does not create two upper spill bits. For a nonaligned bit rotation,
the original parity argument still leaves at most one odd radix digit
in the exceptional rotation b-1, because only the first dummy has the
extra binary bit. The two anchor tests still exclude that rotation.
After an aligned rotation, the unique anchor difference gives zero
rotation modulo the cell circumference.

The mass bound retains npos+2=m+3: npos binary low positions plus the
possible extra contribution two at the first dummy. The independently
reconstructed support count and the original algebra of this bound
agree. Root's exact finite integer calculation checks the numerical
inequalities 4*mass+8<2^b and 2*mu+4<2^b.

## 5. Five-adic tuning

The clause terms cancel modulo 5 because b is odd and T2-T1=2 modulo4.
The independent bare-shift computation gives

    2*DC-DR = 3 modulo5.

Consequently the original actual-rank tuning coefficient is a unit
modulo the required power of five. One can use the first low dummy for
the entire inherited Boolean subset argument and leave the second low
dummy zero. The additional free dummy therefore creates no completeness
obligation. The canonical marked-cell test is unchanged because neither
dummy changes the selected tile or a low source bit.

## Verdict

The strict compiler's smaller alphabet and shorter anchor geometry have
the required semantic and finite-arithmetic properties. The key trust
boundary is the same inherited native compiler theorem. The independent
audit found no new soundness or completeness gap. Its finite checks are
recorded in `strict_independent_checks.json` and can be reproduced with
`check_strict_independent.py`; the unbounded implications are the subset,
padding and proof-interface arguments above.
