# Removing the doubled zero coordinate: a formal100 construction remains open

Deleting the positive supplied Z and its equality Z+D=H from the
verified101 construction gives an exact **100-operation schedule:
55 multiplications and45 additions/subtractions**, with34 positive
unknowns and22 equations. This is only an arithmetic candidate.
Complete semantic soundness remains **OPEN**. Neither an improvement
of the verified101 architecture nor a full counterexample is claimed.

The source/checker is `../verification/explore_doubled_zero_grid_open.py`,
with its adjacent JSON receipt. The predecessor
`EXPLORATION_DOUBLED_GRID_COMPLEMENTS.md` is unchanged.

## 1. Exact source elimination

The101 schedule already computes its packed word without reading Z:

    P=(q-1)X+(1+q²)(H+q^4 t)+q^8H(S+q²z),
    X=Kminus+q²[D+q²(A0+q²(A1+q²(C+q²V)))].

Substitute the expression H-D for Z in the source and remove the
supplied variable, the one addition zero_flag_sum=Z+D, and its
comparison with H.
The first four conceptual fields are now Kplus,Kminus,H-D,D.
Every other source and instruction stays unchanged.

For G=q-J-1 and Fsign=Kplus+Kminus-H, the computed packed register
differs from its literal conceptual concatenation by -GX-Fsign.
The former zero-pair residual vanishes under the substitution. The
checker verifies all22 new comparisons, including that correction and
the retained auxiliary-norm correction. This establishes the formal
count100, not a decoding theorem.

## 2. The kernel bootstrap survives without bounding D

The paid grid condition still gives R>=27, W=R³, q>=R³ and
H=2(q-1)/(R-1). The positive sign pair remains, so the time equation
still implies

    0<A0+A1<WH/(W-1)<(q-1)/4.

The factored P is positive because all of its inputs and coefficients
are positive, independently of the sign of the reconstructed H-D.
Writing L=q^12, the packed sources give

    2r+1=L+P, r+beta=L,
    0<P<=L-1, L/2<=r<L.

Consequently L>=81, r>=27, r<2L and L<r². These are all preliminary
hypotheses of the same general43-operation kernel. It may therefore
be applied before attempting to bound D,t or C. It recovers powers
of three, the full row and grid geometry, and the normalized0/2
packed mask exactly as in101.

One further old bound survives: the positive top contribution obeys

    P>=q^10[(q-1)V+zH].

Thus V<=q, including the still possible endpoint q. The bound on C
does not follow: the route now contains the uncontrolled term hz*D.

This proof order isolates the unresolved issue as joint field and
controller recovery. It is not an obstruction to invoking the kernel.

## 3. A doubled counter-subsystem alias

The lower-field family in `EXPLORATION_UNBOUNDED_NOZERO_GRID_FIELDS.md`
transfers exactly under doubling. This is useful because it excludes
recovering D<H from the counter equations and their masks alone.

Choose even m>=4 and write

    R=3^m, k=(R-3)/6, x=(k+1)/2,
    u=6(x+1), q=R^u, h=(q-1)/(R-1).

Here k is odd and4x<R. Use the finite six-state counter path from
the referenced construction. Let a0,a1,kplus,kminus be its old raw
track and sign words. At its first row, choose a0=k+1 and a1=0;
the later rows use the ordinary Boolean splitting. The complete raw
time equation and all source values are as proved there.

For the doubled source put

    H=2h, Ai=2ai, Kplus=2kplus, Kminus=2kminus,
    D=2(q+h)=H+2q, t=2k(q+h), Zformal=-2q.

The sign, head, top and time equations double homogeneously. Use
the strictly positive new input slack R-4x. The first eight formal
fields normalize to exactly

    2kplus, 2kminus, 0, 2(h-1),
    2(kh-a0+1), 2(a0+k), 2(kh-a1), 2(a1+k).                (1)

Each is less than q and has only ternary digits zero or two. This
follows both from the explicit original Boolean formulas and from
the fact that doubling a Boolean ternary word causes no carry.
The carries between the eight base-q fields are

    0,0,-2,2,2k,0,2k,0.

In particular there is no outgoing carry into the program fields.
All supplied counter coordinates are positive, but D>q and the
reconstructed Z is negative. The initial raw doubled track has
residue2(k+1)=R/3+1, whose ternary digits are not all zero or two.
Thus this is a genuine lower-field alias, despite every normalized
lower mask passing. All of these raw coordinates are already even;
proving evenness of D alone would not eliminate the family.

The finite receipt freshly checks the underlying complete lower cases
at m=4,6,8, and verifies the homogeneous source and doubled packed
identities symbolically. The corresponding inputs are7,61,547 and
the heights are48,372,3288. The family also permits arbitrarily large
even grid-aligned m; finite examples are not claimed to meet the fixed
full program's enormous width threshold.

There is no remaining parity barrier specific to this family. It has
q=1 mod4, H=0 mod4, and2t=0 mod4. The sum of all twelve formal
fields, regardless of C and V, is2H+2t+(S+z)H, hence is divisible
by four. Thus P=0 mod4, and any completed packed index
`r=(q^12+P-1)/2` would be even. This is conditional bookkeeping,
not an assertion that the missing program masks can be completed.

## 4. What is still missing

The family in Section3 does not supply C,V, the two program complements,
or the full cyclic route. It therefore supplies neither all twelve
masks nor a complete Pell witness. It is not a counterexample to the
formal100 source.

Conversely, the existing doubled-zero-fusion proof does not establish
this candidate. That proof retained a supplied positive original guard
parameter, which bounded D before recovery. Here only its positive
gap t is supplied; it can grow with D. The101 proof's ability to pass
the zero and guard pairs without outgoing carries used D<H and
t<(q-1)/3. Section3 shows why those premises cannot simply be restored
by doubled parity.

A proof of100 would have to use the full ROM and global grid to control
these aliases, while accounting for possible state-pair and junk-pair
overflow. A refutation would have to extend such an alias to all of
those equations and masks. Both possibilities remain open in this
artifact. All verification statuses explicitly distinguish the exact
100-operation arithmetic from this unresolved semantic question.
