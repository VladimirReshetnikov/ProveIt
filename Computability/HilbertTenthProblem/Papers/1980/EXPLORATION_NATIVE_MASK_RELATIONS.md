# Two direct mask identifications fail in the current native interface

The two masks in the [76-operation certificate](FIXED_RAW_UNIVERSAL_76_PROOF.md)
cannot simply be made equal or complementary while retaining the interfaces
specified below. Equal masks conflict with exact population saturation and
the reused Pell power's cell alignment. Complementary masks conflict with
the unique unit-bit Start marker and its actual overlap constraints.

These are **scoped compiler obstructions**, not a lower bound on arithmetic
certificates or on arbitrary local encodings. They do not exclude a different
scale, packed layout, marker encoding, temporal multiplier, or an encoding
whose carries themselves implement additional constraints. No new operation
count is claimed; the published complete bound remains76=41M+35A.

The [checker](../verification/explore_native_mask_relations.py) and
[receipt](../verification/explore_native_mask_relations.json) test the exact
population formula, the complete singleton parity convolution in both shift
conventions, and the actual fixed Start window and overlap implementation.

## 1. The retained interfaces

Let B=2^d, q=B^N, J=(q-1)/(B-1), and retain the two-field packing

    S=Z+qF, M=(MC+q*MF)J,
    r=(q^2-S)(q^2-1)+M, D0=q^3.                         (1)

The field bounds are 0<Z,F<q, and the fixed cell masks satisfy
0<MC,MF<B, as in the complete certificate.
The inverse-packing inequality is

    popcount(r)<=2dN+popcount(M).

Equality holds exactly when the paid masks vanish, including the separate
argument that an overflow of S+M cannot attain equality. The retained proof
uses the kernel condition popcount(r)>=3dN to saturate that inequality.

The temporal multiplier is the recovered main Pell power

    X=2^j0, j0=2r+1.

The synchronized native compiler forces this binary rotation to align with
whole cells. In particular d divides j0. This conclusion does not require
X<q, nor does it require choosing a particular representative of its exponent
modulo dN. Since j0 is odd, **d must be odd** in every such solution.

For the complementary-mask obstruction also retain the following facts.
After decoding, a cell's unit bit is1 precisely for Start; Start occurs
exactly once, and all other bits in its cell are above the unit position.
End is separately inserted, as in76. The actual local field is carry-free
between cells and has the exact form

    f_i=DC*c_i+DR*c_(i-1)+c_(i-h), 0<=f_i<B.             (2)

Its successor coefficient is1. The constants DC and DR may be redesigned;
the proof below uses only their parities. The current compiler satisfies
stronger internal radix bounds, but those are unnecessary here. N>=3 follows
in76 from the raw endpoint2x<N and x>0.

## 2. Equal masks cannot retain exact q-cubed saturation

Suppose MC=MF=A, and let m=popcount(A). The two disjoint q-sized mask fields
each contain N copies of A. Hence

    popcount(M)=2mN.

Keeping the exact upper threshold in (1) equal to log2(D0)=3dN requires

    2dN+2mN=3dN, or d=2m.                              (3)

Thus d would be even, contradicting the oddness forced by d|j0. This
contradiction is independent of the five-adic dummy-control construction;
choosing a different modulus for that construction does not repair it.

The equality assumption in (3) is material. If2m<d, even the population
upper bound is too small for the retained kernel. If2m>d, the old kernel
threshold no longer forces saturation and therefore does not establish
the paid masks by the existing proof. This note does not infer that every
system in the latter case is unsound; it rejects the direct substitution
while retaining this exact mask-recovery interface.

## 3. Complementary masks force a degenerate temporal shift

Suppose instead MC+MF=B-1. For two integers in[0,B), this says precisely
that their d-bit supports are complementary. Since the unit Start bit
is permitted by MC, MC is even and MF is odd. Every masked field digit
f_i is therefore even.

Let s_i be the indicator of the unique Start cell, and put

    a=DC modulo2, b=DR modulo2.

Taking (2) modulo2 gives, for every i modulo N,

    a*s_i+b*s_(i-1)+s_(i-h)=0 in F2.                    (4)

Rotate indices so that s_0=1. The three possible nonzero terms in (4)
are then supported at0,1,h respectively. Summing (4) around the cycle
gives a+b+1=0, so exactly one of a,b is1. Consequently the only possibilities
are

    a=1,b=0,h=0; or a=0,b=1,h=1 modulo N.               (5)

This includes every possible choice of the constant coefficients' parities.
It is not merely the observation that the present DC and DR are both even.
There is no ambiguous sign convention: if the spatial neighbor is instead
indexed i+1, the second possibility is h=-1. In invariant terms the temporal
successor word must equal either the current word or the chosen spatial
neighbor word.

The argument would also apply to signed coefficients if (2) were established
as the exact bounded cell equation without intercell carries or borrows.
It does not cover a different encoding that uses such carries as data.

## 4. Both possibilities contradict the actual Start window

Use the exact three-by-three lift and fixed stationary-first-step Start
window from the76/81 construction. Write H for its boundary tile and I
for the headless initialization tile. Its top and middle rows are

    H H H
    I I Q.

Here H differs from I and from Q. The bottom row is fixed too, but is not
needed for these contradictions. In the implementation, horizontal overlap
means center[row,col+1]=right[row,col], and vertical overlap means that the
center's bottom two rows equal the successor's top two rows.

If h=0, the successor of Start is Start itself. Vertical overlap would
identify its middle row with its top row, already contradicting I!=H.

If h=1, the temporal successor is exactly the right-neighbor window T.
Horizontal overlap with Start forces T[0,0]=H. Vertical overlap with Start
forces the same entry T[0,0]=I. No possible window T can satisfy both,
regardless of which additional windows the machine alphabet contains.

For the opposite spatial convention, let T be the left neighbor instead.
Horizontal overlap of T with Start forces T[0,1]=H; vertical overlap of
Start with T forces T[0,1]=I. Thus the same contradiction applies, with
no dependence on indexing orientation.

Therefore complementary masks cannot encode any genuine marked computation
in this unchanged carry-free, coefficient-one-successor, unique-unit-Start
interface. Moving the distinguished bit, adding another marker mechanism,
or changing the local transport falls outside this conclusion.

## 5. Reproducible checks and limits

The checker enumerates equal fixed masks at small widths and directly
computes the actual packed population on disjoint masked fields. It checks
the exact saturation parity and odd-index divisibility independently. For
the complementary case it exhausts every coefficient parity and temporal
offset for bounded cycle lengths, several marker origins, and both spatial
orientations. It obtains exactly the two cases in (5).

The semantic checks call the existing fixed-marker and overlap functions
for actual stationary-first-step machines. They also enumerate completions
of a spatial neighbor from the finite tile set appearing in those markers;
every completion is rejected as a simultaneous temporal successor. The
proof's single-entry contradiction covers the full machine alphabet, not
just those finite completions. Sparse checks of the current compiler record
its odd width and the unique selector unit bit without materializing B.

No published source is modified. No new full Pell tuple or universal compiler
alphabet is materialized, and no obstruction to general computational-model
replacement is claimed. Default verification compares the saved JSON;
regeneration requires `--write`.

Review status: author and independent complete proof/source reviews pass.
Fresh default verification matches the saved receipt. The independent
review covers both spatial orientations and the exact scope of saturation.
