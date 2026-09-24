# The tag masks and transports do not recover radix divisibility

Review status: author and two independent complete proof/source reviews and
fresh verification runs passed without findings. The proof and arithmetic
are frozen; the weakened system's halting semantics remain open.

Deleting the single multiplication and equation `q=R*v` from
[generic105](EXPLORATION_GENERAL_SCALED_TAG_TRANSPORT.md) leaves a formal
**104-operation source: 52 multiplications and 52 additions, with
33 positive unknowns and20 equations**. The remaining source has a full
positive solution family in which `q` is a power of three but `R` is not,
and `R` does not divide `q`.

The family satisfies both actual transport equations, all ten conceptual
Boolean masks, every other outer equation, and the complete positive Pell
kernel. It therefore disproves recovery of the deleted equation from the
remaining system. It also rules out restoring the old coordinate `v` while
keeping the other coordinates fixed.

**This is not a counterexample to halting semantics.** Its fixed specified
input actually halts after one step. A different proof might conceivably
show that the weakened104 system still defines halting without recovering
`R|q`; that question is left open. No104 halting or universal bound is
claimed, and no published105 file is changed.

## 1. Exact deletion and the unchanged kernel interface

The removed instruction is `radix_product=R*v`, whose sole consumer is the
free equality `radix_product=q`. The coordinate `v` has no remaining use.
All other instructions and source equations are retained, including

    R=C*A, H(R-1)=q-1,
    2r+1=q^10+2P, r+betaP=q^10.

The deleted positive coordinate is not replaced by an uncharged quotient.
Both compile-time branches of generic105 have exactly the stated104 count.
There are nine outer comparisons and eleven kernel comparisons. Removing
one outer source shifts the retained kernel norm correction from combined
index18 to index17; its polynomial and prerequisite are unchanged.

Some bounds still follow without `q=R*v`: positive `H` and
`H(R-1)=q-1` imply `q>=R`. Thus the predecessor's preliminary size bounds
do not fail merely because this multiplication is absent. The substantive
problem is the lost implication that `R` is a power of three after the
kernel recovers that property for `q`. The family below satisfies the
stronger kernel bounds directly.

## 2. Fixed program and an infinite nonpower geometry

Fix deletion number `beta=3` and the appendant `u=010`, in the established
little-endian convention. The rules are `0 -> 0` and `1 -> 010`. Their
constants are

    K=27, Kh=9, B=9, U=3, c=4, C=81, Cbar=9, U3=1.

Use the fixed original input parameters and terminal values

    Ninit=27, Linit=81, Nfinal=1, Lfinal=9.              (1)

The initial word is `0001`. One legal step deletes its first three zeros
and appends one zero, leaving `10`. Its length is two, strictly less than
the deletion number, so this specified computation halts after one step.

For every integer `k>=5`, put

    h=3^k, q=h^4,
    R=h^3-h^2+h, H=1+h, A=R/81.                        (2)

These are positive integers. The useful exact identity is

    R*H=q+h,

which proves `H(R-1)=q-1`. Also `R=81A` and `A>81`, so the retained
input slack is positive. But

    R=3^k(3^(2k)-3^k+1),

where the parenthesized factor is greater than one and congruent to one
modulo three. Thus `R` is not a power of three and cannot divide
`q=3^(4k)`. There is no positive integer that could restore `q=R*v`.

The geometry alone is not the result: the following sections give all
remaining outer coordinates and the full kernel extension.

## 3. All ten fields and positive adapters

Choose the fields in their unchanged conceptual order as follows:

| Field | Value |
|---|---|
| `Gstar` | `1+4h+3^(4k-4)+3^(k-4)` |
| `Q` | `4h` |
| `S0` | `1` |
| `S1` | `h` |
| `M0` | `81` |
| `M1` | `9h` |
| `Ebar` | `4(1+h)` |
| `E` | `0` |
| `Nbar` | `13+3h` |
| `N` | `27+h` |

Set

    Nsum=40+4h, L=81+9h, T=9.                          (3)

For `k>=5`, every entry in the table is a Boolean ternary word below
`q`. For example, `4h=h+3h`, `13=1+3+9`, and

    A*H=3^(4k-4)+3^(k-4).

The five positions in `Gstar` are `0,k,k+1,4k-4,k-4`; they are distinct
and less than `4k`. Its unit trit is one. The remaining support checks
are equally literal sums of distinct powers of three.

All structural equalities hold:

    S0+S1=H, 2Q+S1=M1, M0+M1=L,
    2Nsum+H=L, N+Nbar=Nsum, E+Ebar=cH,
    Gstar=Q+AH+S0, N=3T+S1.

The positive supplied adapters are `F_Q=Q+1`, `F_S1=S1+1`, `F_T=10`,
`F_E=1`, and `F_Nfinal=2`. The retained slacks are

    alphaI=A-81>0, alphaH=18>0.

Together with the positive `Nsum,A,H,R,L,q,Lfinal` from (1)--(3), this
supplies every non-kernel coordinate except `r,betaP`, given below.
In particular the zero raw prefix word uses a positive adapter; no
zero supplied unknown is admitted.

## 4. Both complete transport equations

For this appendant the shared register is `D=R/Kh=R/9`. The two new
output expressions simplify to

    T-E+U3*M1=9+9h=9H,
    L+(B-1)M1=81+81h=81H.

Using `RH=q+h`, the two generic105 transport equations become the exact
identities

    D*9H=q+h=N-Ninit+q*Nfinal,
    D*81H=9q+9h=L-Linit+q*Lfinal.                     (4)

The retained paid radix comparison holds because `Kh*D=R=CA`.
Equivalently, the old unscaled transport equations also hold, since
`N-3E-S1+U*M1=27H`. No digitwise interpretation of a nonpower `R` is
used in this verification.

This establishes every remaining outer equation apart from the packing
index and its positive bound. It is stronger than merely satisfying
`H(R-1)=q-1` and a few low masks.

## 5. Packing and the full positive Pell extension

Let `P` be the ten-field concatenation in the displayed order and set

    D0=q^10=3^(40k),
    r=P+(D0-1)/2, betaP=D0-r.                         (5)

All ten fields are Boolean and below `q`, so `P` is Boolean below
`D0`, with unit trit one. Its maximum is `(D0-1)/2`. Hence `r<D0`,
`betaP>0`, and both retained index equations hold.

Adding the all-one ternary word `(D0-1)/2` gives a native word `r`:
its unit trit is two and every other trit is one or two, with exactly
`40k` positions. Doubling it has a carry at every position. Therefore

    v3(binom(2r,r))=40k,

and the complete kernel divisibility condition holds. We also have

    D0>=81, r>=27, r<D0<2D0, D0<r^2.

The scale is a power of three. The full converse of
[EXPLORATION_PARITY_FREE_PELL_KERNEL.md](EXPLORATION_PARITY_FREE_PELL_KERNEL.md)
now supplies all seventeen positive auxiliaries, for either parity of
`r`. Its hypotheses involve `D0,r` and their exact divisibility, all
proved here; they do not require `R` to be a power of three. The
acyclic norm correction identifies its equations with the retained
straight-line kernel checks.

Thus (1)--(5) extend to a complete positive solution of the weakened104
source for every `k>=5`. This is a proof of existence of the large Pell
coordinates, not a claim that the checker materializes them.

## 6. Exact source and fresh finite evidence

[explore_tag_radix_divisibility_omission.py](../verification/explore_tag_radix_divisibility_omission.py)
checks the one-instruction deletion over frozen generic105. It verifies
all20 source residuals for each fixed-leading-symbol branch, the shifted
but otherwise unchanged norm correction, disappearance of every use of
`v`, and the exact104 count.

It materializes the entire non-kernel tuple for `k=5,6,7,8,12,16,24,32`.
Each case checks all nine actual outer comparisons, all ten Boolean
fields, the original unscaled transports as well as (4), all supplied
non-kernel positivity conditions, `q mod R != 0`, both index equations,
the exact native valuation and all positive-converse hypotheses. The
valuations are respectively `200,240,280,320,480,640,960,1280`.

The first case has `R=14290101`, `q=3486784401`, `A=176421`, `H=244`,
and uses the same fixed input `(Ninit,Linit)=(27,81)` as every later case.
The checker also performs its actual one-step tag computation and verifies
that it halts. The distinction between failed implicit radix recovery
and an unresolved halting-semantic claim is therefore explicit in both
the proof and receipt.
