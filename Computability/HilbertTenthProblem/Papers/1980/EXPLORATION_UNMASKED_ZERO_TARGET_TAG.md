# A fixed zero endpoint does not replace the tag content guard

Removing the content guard from the complete nine-field104 tag certificate
admits a full positive false halt, even when both prefix masks remain and
the terminal content and length are fixed to0 and3. The rejected source has
an exact **94-operation schedule, 48M+46A**, with30 positive unknowns and
19 equality comparisons. Using the fixed-plus43 kernel instead gives
**93 operations, 47M+46A**, with29 positive unknowns and18 comparisons.
The same even-index tuple refutes both. The93 variant is the direct
content-guard deletion from the fixed-single-zero99 source. Neither
rejected count is an improved bound; the valid104 and99 certificates
are unchanged.

Author and two independent complete proof/source reviews and fresh
verification runs pass without findings. The maintained [checker](../verification/explore_unmasked_zero_target_tag.py)
and [receipt](../verification/explore_unmasked_zero_target_tag.json) contain
all four complete symbolic sources and the exact positive outer tuple.

## 1. Exact proposed source and count

Start with [the single-content-guard104 source](EXPLORATION_SINGLE_CONTENT_GUARD_TAG.md),
restrict beta>=2, and use its fixed constants and original encoded-input
parameters. Keep true radix geometry, the input bound, both prefix masks,
and the original content and length transports. Fix

    Nfinal=0, Lfinal=3.

Remove only the ninth conceptual field GN=N+jAH. The remaining fields are

    Gstar,Q,S0,S1,M0,M1,Ebar,E,
    P=Lo6+q^6[ccH+(q-1)E], D0=q^8.                 (1)

Retain the positive coordinates F_Q,F_S1,F_T,F_E, defining
Q=F_Q-1,S1=F_S1-1,T=F_T-1,E=F_E-1. As in104,

    M1=2Q+S1,
    N=3T+S1       for a zero-leading appendant,
    N=3T-2Q       for a one-leading appendant,
    D=(C/k)A, k=K/3.

The eight outer comparisons become

    kD=R,
    D(T-E+Ut*M1)=N-Ninit,
    D[L+(B-1)M1]=L-Linit+3q,
    Linit+alphaI=A,
    H(R-1)=q-1, Rv=q,
    2r+1=q^8+2P, r+betaP=q^8.                       (2)

For the94 variant there are seventeen additional positive kernel
auxiliaries and eleven kernel comparisons, using the unchanged
parity-free44 kernel.

Deleting GN removes its three construction operations and its two packing
operations; q^8 instead ofq^9 removes one power multiplication. This takes
104 to98, saving4M+2A. The fixed zero endpoint removes the Nfinal adapter,
the product q*Nfinal and its addition into the content endpoint. Fixing
Lfinal=3 removes the terminal-bound addition and its comparison. The
product3q is still charged. These further savings are1M+3A, giving

    94 = 48 multiplications + 46 additions/subtractions.

The supplied F_Nfinal,Lfinal,alphaH are removed, giving30 positive
unknowns. The original terminal comparison becomes identically zero under
alphaH=K-3; beta>=2 ensures this restored value is positive. The checker
verifies all19 source polynomials in both fixed leading-symbol branches.

The direct93 variant uses the positive-sign43 kernel from
[the general-scale unit-two kernel](EXPLORATION_UNIT_TWO_TERNARY_KERNEL.md).
It has sixteen supplied auxiliaries and ten comparisons. The internal
quantity u is computed as jc+2r+1, rather than supplied as pell_u. The
outer schedule, all eight fields, the scale, and the index are identical.
Equivalently, delete the same4M+2A content/scale operations directly from
[the fixed-single-zero99 source](EXPLORATION_ZERO_TERMINAL_TAG_PARITY.md).
This gives93=47M+46A,29 positive unknowns and18 comparisons. Its full
symbolic source is checked independently in both leading-symbol branches;
the change is not justified merely by subtracting1 from an operation count.

For both variants the retained kernel norm correction is at zero-based
comparison16. It uses the supplied u in94 and the computed jc+2r+1 in93.
Products by fixed constants remain in this generic DAG even when a
constant happens to equal1 in the example below.

## 2. The genuine nonhalting input and the false length schedule

Take beta=2 and the productions0->0,1->01. Thus

    K=9, k=3, B=3, U=3, cc=1, C=2187.

The actual input111 has Ninit=13,Linit=27. One genuine step produces101,
which is then a fixed point. This input therefore never halts.

Choose

    A=81, R=CA=177147=3^11, b=R/9=19683,
    q=R^10, H=1+R+...+R^9,
    S1=1+R+...+R^7,
    Q=13S1, M1=27S1,
    M0=27R^8+9R^9, L=M0+M1,
    E=R^3+R^4+R^9, Ebar=H-E.                       (3)

This chooses eight one-channel rows and then two zero-channel rows. Their
length markers are

    27,27,27,27,27,27,27,27,27,9,

with terminal marker3. Every scalar length transition is exact, so the
whole length comparison in(2) is exact. The prefix rows are

    0,0,0,1,1,0,0,0,0,1.

Both E and Ebar are positive Boolean words supported on row heads; they
satisfy E+Ebar=ccH exactly. In particular, the example does not exploit
either of the separately refuted prefix-mask deletions.

Define the unmasked content through

    T = [b(E-M1)+(S1-13)/3]/(b-1),
    N = 3T+S1.                                      (4)

Both divisions in this mathematical definition are exact. First S1=1
mod3. For the second division, modulo b-1=19682 the relevant residues are

    E=7291, M1=9838, (S1-13)/3=2547,

whose signed sum is zero; b=1 modulo b-1. Also E>M1 and S1>13, so T>0.
These divisions define a concrete counterexample tuple; they are not
unpaid operations in the proposed DAG, which supplies F_T=T+1.

Equation(4) gives exactly

    R(N-3E-S1+3M1)=9(N-13).                         (5)

This is the full content transport with terminal0. It imposes only
N=Ninit mod(R/K) at the initial boundary. In this tuple the ordinary
base-R residues of N are

    59062,6571,739,118189,111555,12403,1387,163,27,3.

The first is13+3b, not13. These are not genuine tag contents, and no
rowwise content transition is asserted for them. The whole source
comparison(5) nevertheless holds. Its quotient T is strictly positive,
so the retained positive content adapter does not exclude the tuple.

## 3. Every remaining mask and positive outer coordinate passes

All the first eight fields in(1) are individually Boolean and belowq.
The projector is canonical for the displayed selectors and length
markers. On the first eight rows Gstar is Qrow+A=13+81; on the remaining
two it is1+A=82. Both are Boolean, and Gstar has unit trit1.
M0 and M1 are disjoint marker words. Ebar and E are complementary
head words. Thus all eight masks pass separately, without any packing
carry between fields.

Supply

    F_Q=Q+1, F_S1=S1+1, F_T=T+1, F_E=E+1,
    alphaI=A-27=54, v=q/R,

together with A,H,R,L,q from(3). These are all strictly positive.
The omitted guard N+jAH is not Boolean. No remnant of that condition is
silently used in this candidate.

The proof does not merely check a local inconsistent row: the complete
positive outer tuple satisfies both full transports, both true geometry
comparisons, the original input bound, and the index and packed bound
below. The fixed terminal is exactly content0 with length marker3.

## 4. Full positive Pell extension and evidence scope

Use the eight fields in(1) and set

    D0=q^8=3^880,
    r=P+(D0-1)/2, betaP=D0-r.

The Boolean fields give a native ternary1/2 index with unit2. Its exact
central-binomial valuation is

    v3(binomial(2r,r))=8*11*10=880.

The checker verifies that r is even and satisfies27<=r<D0 and D0<r^2.
Consequently betaP>0, and every hypothesis of the established
[parity-free44 positive converse](EXPLORATION_PARITY_FREE_PELL_KERNEL.md)
holds. That theorem supplies fresh strictly positive values for all
seventeen kernel auxiliaries, completing the19-equation false witness.
Because this same index is even, the positive-sign43 converse in
[the general-scale unit-two kernel](EXPLORATION_UNIT_TWO_TERNARY_KERNEL.md)
also applies and supplies sixteen fresh positive auxiliaries. This
completes the18-equation93 false witness with all outer coordinates,
fields and the index unchanged. There is no claim that an arbitrary
44-kernel auxiliary tuple can simply be reused in the43 source. Neither
set of enormous auxiliary values is claimed to have been materialized.

Fresh verification checks all four complete symbolic sources, the exact
generic operation counts, all eight numerical outer comparisons, all
eight individual masks, positivity of every supplied outer coordinate,
the valuation and required even parity, both positive-kernel interfaces,
and the genuine nonhalting fixed point. The separate
23-row exploratory example is not needed for this maintained result.

This refutes replacing the content mask by a fixed zero endpoint in the
stated general tag interface. It does not settle a different source that
uses further restrictions on Neary's particular appendants or encoded
inputs, and it makes no lower-bound claim against other encodings.
