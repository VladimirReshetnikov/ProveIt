# Merging the two tag head masks admits a full false halt

The reordered93 source cannot in general replace its separate S0,S1 masks
by a single Boolean word F=S0+3S1=H+2S1. The formal saving is real: the
proposed source has **92 operations = 50M+42A**, with29 positive unknowns
and18 comparisons. A full positive counterexample refutes it, including
the fixed-plus43 kernel. This is separate from valid optimizations that
retain both head masks; no improved bound is claimed here.

Author and two independent complete proof/source reviews and fresh
verification runs pass. The [checker](../verification/explore_merged_tag_head_flags.py)
and [receipt](../verification/explore_merged_tag_head_flags.json) contain
both complete symbolic sources and the full positive outer tuple.

## 1. Exact proposed source

Keep every outer comparison and positive coordinate of
[the reordered93 source](EXPLORATION_REORDERED_STARTUP_TAG.md). In particular
S1 remains a supplied positive scalar, M1=2Q+S1, and both prefix masks
E,Ebar remain. So do the content mask GN, true radix geometry, the input
bound, and the fixed endpoint Nfinal=0,Lfinal=3.

Replace the two first fields S0,S1 by one field F=H+2S1. The eight fields
and their exact packing are

    F,Q,G,M0,M1,Ebar,E,GN,
    P=F+q[Q+qG+q^2 Rest],
    Rest=L+(q-1)M1+q^2[ccH+(q-1)E+q^2 GN].          (1)

Computing F replaces the old pair H+(q-1)S1 at the same one-product,
one-addition cost. The new nesting uses the same number of packing
operations. The scale q^8 requires only q^2,q^4,q^8, saving the old
q^9 multiplication. Thus the count is92=50M+42A. Both leading-symbol
branches are checked against all18 source polynomials; the computed-u
norm correction is at zero-based comparison16. This is a complete
source ledger, not a soundness theorem for the proposed packing.

## 2. The local selector hole

At a selected length marker L=3^ell, choose a hole V=3^e with
2<=e<ell. Set

    Q'=(L-1)/2-V, S1'=1+2V.

Then

    2Q'+S1'=L, F'=1+2S1'=3+4V.                    (2)

Q' and F' are Boolean, while S1' has a forbidden digit2. With A>L,
G'=Q'+A is also Boolean. Thus all three new local masks accept the
modified selector without changing M1.

If V is divisible by K, the deleted prefix3E+S1 increases by2V,
decreasing the next content by2V/K. In the particular case where the
ordinary next content has trits0,1 at the affected adjacent positions,
this subtraction moves a1 one position toward the head and leaves the
content Boolean. Consequently retaining GN does not automatically expose
the changed transition.

## 3. A certified nonhalting input and one false bit move

Use beta=2 and the appendant0100, with0->0. The genuine input001001
has the exact orbit

    001001 -> 10010 -> 0100100 -> 001000
            -> 10000 -> 0000100 -> 001000 -> ... .

Every word in the displayed cycle has length at least2. The input never
halts. Its initial symbols are001; the appendant has even length, starts01,
and has0 at every even position. These facts do not make this a Neary
Table2 instance; in particular its deletion number is2, not10p.

At the source10010, the ordinary ternary content is28 and the length
marker is243. Take V=9 in(2). The effective selector becomes19,
instead of1. The actual deleted prefix is1, so the prefix quotient Erow
remains0. The content transport gives

    (28-19+3*243)/9=82,

instead of the true output84. Thus the false successor is1000100,
while the true successor is0100100. The merged field is39=3+4*9,
which is Boolean. The modified Qrow is112, and the content adapter's
row contribution is(28-19)/3=3>0.

Following genuine transitions after that one false step gives this full
23-row source sequence and the terminal0:

    001001, 10010, 1000100, 001000100, 10001000,
    0010000100, 100001000, 00010000100, 0100001000,
    000010000, 00100000, 1000000, 000000100, 00001000,
    0010000, 100000, 00000100, 0001000, 010000,
    00000, 0000, 000, 00 -> 0.

The checker verifies every ordinary transition in this sequence except
the designated false one, and verifies the exact modified scalar content
equation at every row, including that row. Every displayed content is
Boolean. All length transitions are the ordinary transitions for the
row's original selector bit; equation(2) preserves the corresponding M1.

## 4. Complete outer tuple, masks and positive kernel extension

Choose fixed C=3^11, A=3^12 and R=CA=3^23. Set q=R^23 and
H=(q-1)/(R-1). This C also satisfies C>K^2*Linit, and A exceeds every
source length marker. Recompute the fixed constants C/k and
j=(C-C/K)/2 accordingly; these are fixed numerals in the source.

Pack the displayed ordinary contents into N and their length markers
into L. Pack their selectors into S1, except replace the second row's
selector1 by19. Pack the usual selected-marker intervals into Q, except
subtract9 in that same row. Let E contain the genuine prefix quotients,
and set T=(N-S1)/3. Every row's numerator is nonnegative and divisible
by3; the whole Q,S1,E,T are all strictly positive.

The resulting M1=2Q+S1 is exactly the ordinary selected-marker word.
Both E and Ebar=ccH-E are Boolean. Every content fits below A, so the
unchanged GN=N+jAH is Boolean. G=Q+AH remains Boolean. F is Boolean
on every row, with unit1 because the first selector is0. All eight
retained fields are nonnegative and belowq.

Supply alphaI=A-Linit>0 and v=q/R. The complete content and length
equations, geometry, input bound and fixed zero endpoint hold. The
derived S0=H-S1 is even positive as a whole integer; retaining its
global positivity alone would not rule out this tuple.

For the packing in(1), set

    D0=q^8=3^4232, r=P+(D0-1)/2, betaP=D0-r.

The new r is even, native1/2 with unit2, and has exact central-binomial
valuation4232. The checker verifies27<=r<D0, D0<r^2 and betaP>0.
The [general-scale fixed-plus43 converse](EXPLORATION_UNIT_TWO_TERNARY_KERNEL.md)
therefore supplies sixteen fresh strictly positive auxiliary values.
This completes a false solution of the entire18-equation proposed source.
The enormous auxiliary values are proved to exist, not materialized.

The fresh receipt covers both symbolic92 schedules,30 local hole cases,
the complete genuine nonhalting cycle, all23 modified scalar content
transitions, all eight whole-source outer comparisons, all eight masks,
positivity and the new kernel valuation. This refutes the stated merge
in the general encoded-input interface. It does not exclude a different
construction using additional full Neary-specific restrictions.
