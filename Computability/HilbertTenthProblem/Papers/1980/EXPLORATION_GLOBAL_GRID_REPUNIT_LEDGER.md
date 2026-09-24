# A global grid repunit gives an arithmetic tie

This bounded exploration changes only the grid parameterization of the
complete state-top100 construction. The direct new schedule still costs
**100 operations = 55 multiplications + 45 additions/subtractions**, with
34 positive unknowns and22 equations. It supplies no99-operation reduction.
Full semantic equivalence of the reparameterized source is not proved.
The frozen state-top100 source and its established theorem are unchanged.

Put b=B0-1, Z=Zon, and introduce a positive global grid word G in place of
the positive scalar z. Retain q=J+1 and H(R-1)=2J, but replace the width
equation b(Z+z)=R-1 by

    bG=2J.

In a canonical old solution, G=(Z+z)H, so the desired allowed-grid word is
G-ZH=zH. Replace the conceptual junk pair by (G-ZH-V,V). The exact packing
is now

    X=Kminus+q²[D+q²(A0+q²(A1+q²(V+q²C)))],
    P=JX+(1+q²)(H+q^4t)+q^8[G+H(q²S-Z)].

The identity with the old packed value under G=(Z+z)H is unconditional.
The checker evaluates the complete new source and all22 comparisons,
including the earlier-source corrections, rather than merely counting
these displayed expressions.

## Exact operation comparison

The six old q/head/grid instructions use2M+4A: form2J, J+1, R-1,
Z+z, b(Z+z), and H(R-1). The new version drops Z+z, keeping the other
five computations with bG in place of b(Z+z). This saves one addition.

With q² and q^8 already shared, the old high base q^8H(z+q²S) costs
3M+1A. The new high base q^8[G+H(q²S-Z)] costs3M+2A. Its extra addition
exactly spends the geometry saving. Every other operation is unchanged.

One possible fusion uses the grid equation J=bG/2:

    JX+q^8G = G[(b/2)X+q^8].

The fixed b/2 is an integer numeral. But distributing the formerly shared
outer multiplication by q^8 leaves the full JX-plus-high portion costing
5M+3A, compared with4M+3A in the direct new layout. That fusion adds a
multiplication. These are exact counts for the displayed layouts; they
are not a lower bound on all possible straight-line programs.

## Bounds that no longer follow from geometry

The positive scalar z previously gave R-1>bZ immediately, before using
the Pell kernel or any mask. A merely positive G does not supply this
bound. Its allowed-grid difference G-ZH can be negative, so the new
factored P is not automatically positive. The old pre-kernel top-state
bound cannot simply be cited for this changed formula.

The row-grid conclusion also needs a new argument. Even after q is a
power of three, bG=2(q-1) controls the exponent of q, not by itself the
exponent of the row radix R.

For the maintained B0=9 example, the positive partial tuple

    R=27, W=27³, q=27^4, J=q-1,
    H=40880, G=132860, x=1,
    A0=A1=2, D=1, t=4,
    Kplus=20438, Kminus=20442, alphaI=23

satisfies q=Wv with v=27, both new head/grid equations, the sign equation,
the gap equation, the raw time equation and the paid input bound. Yet
R-1 is not divisible by8, and G-ZH<0 for the actual fixed forbidden Z.
With positive C=V=1 the new factored P is negative. The checker verifies
all nine stated residuals and this sign directly at the actual constants.

This tuple deliberately does not satisfy the route or packed/Pell
equations. It demonstrates failure of the preliminary implications, not
a false positive for the full source. A different joint mask argument
could conceivably recover the lost bounds. Without an arithmetic saving,
that broader semantic problem is left open here.

The companion is `../verification/explore_global_grid_repunit_ledger.py`
with an adjacent receipt. It performs symbolic source/packing checks,
exact ledger checks, and the stated partial-tuple check. No canonical
whole-history or Pell computation is needed for this scoped conclusion.
The author and an independent complete review of this scoped proof,
source and fresh verification pass without findings. This audit establishes
the displayed arithmetic tie and failed preliminary implications only.
