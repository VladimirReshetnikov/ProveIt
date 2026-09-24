# Conditional tag-mask packing, parity, and index costs

This is an interface ledger for the eleven words in
`EXPLORATION_TAG_QUEUE_HISTORY.md`. It records exact packing formulas,
an equal-cost parity treatment, and a restricted deletion-two saving.
The general complementary-pair formula ties ordinary Horner packing;
no lower-bound claim is made. Neither this ledger nor the conditional
tag verifier is a complete universal certificate.

## 1. Available words and shared relations

The eleven nonnegative words, each strictly less than q, are

    Q0,Q1,S0,S1,M0,M1,G,N,Nbar,E,Ebar.

Use the joint-marker conclusions and the additional content/prefix
relations:

    Q0+Q1=Qsum=N+Nbar, S0+S1=H,
    M0+M1=L=2Qsum+H, E+Ebar=cH,
    G=Qsum+AH, c=(3^(beta-1)-1)/2.

Here c is a fixed numeral, A=R/C with fixed C a power of three,
q=R^t, and H is the row-head repunit. The registers Qsum,H,L,cH,AH,G
are already computed by the conditional verifier. If complementary
packing uses q-1, that register is assumed shared with row geometry.

The initial length satisfies Linit>=3^beta and Linit<A. Consequently
Qsum has unit trit one and A>1, so G has unit trit one. These initial
hypotheses are necessary for using G as the first packed field in the
unit-two index construction; no initial selector value is assumed.

The range and nonnegative-word assumptions are explicit. Proving or
encoding those ranges before the mask, and adapting possible zero words
to a strictly positive supplied domain, remain composition obligations.

## 2. The general complementary-pair formula is a twenty-operation tie

For the order

    Q0,Q1,N,Nbar,S0,S1,E,Ebar,M0,M1,G,

put

    X=Q1+q²[Nbar+q²(S1+q²(Ebar+q²M1))].

The exact packed word is

    P=(q-1)X+(1+q²)Qsum
      +q^4(H+q²(cH))+q^8(L+q²G).                         (1)

X costs four products and four additions. Scaling by q-1 costs one
product. The three base terms cost respectively two, three, and three
operations, and joining all four terms costs three additions. The total
is **20=10M+10A**, exactly the ordinary eleven-field Horner cost. The
extra joins must be counted. Equation(1) does not put G first and does
not by itself guarantee the unit trit; it is an arithmetic comparison.

For the general index ledger below, simply put G first and use Horner
on the eleven words. This still costs20 and guarantees the required
unit trit. Substituting L=2Qsum+H or G=Qsum+AH into the pair formula did
not produce a lower general-c count in this bounded investigation.
That observation is not an impossibility proof for other DAGs.

## 3. An extra parity field has no net cost against the parity-free kernel

The sum of the eleven fields is

    3Qsum+L+(c+1)H+AH = 5Qsum+(c+2)H+AH.

After power geometry A is odd, so this sum is congruent to

    Qsum+(c+1)H modulo2.

For even c, append a duplicate G; for odd c, append Qsum. Both are
Boolean by the joint-marker theorem. The resulting twelve-field sum
is even. Keep G first, so the packed word still has unit trit one.
This requires no assumption on the number of tag steps or selectors.

For twelve fields let D0=q^12 and impose, using the kernel's existing
register tr1=2r+1,

    tr1=D0+2P, r+betaP=D0.

The doubled P, its addition to D0, and the positive upper-bound sum
cost three additions. The powers q²,q^4,q^8,q^12 cost four products.
The masks give r=P+(D0-1)/2 with native ternary digits and unit digit
two. The new P is even, and (q^12-1)/2 is even for every odd q, so the
fixed-plus43-operation kernel has a positive converse.

Alternatively retain eleven fields, use D0=q^11, and use the parity-free
44-operation kernel. The chain q²,q^4,q^8,q^10,q^11 costs five products.
It needs no parity property of P. The exact comparison is:

| Variant | Raw packing | Powers | Index and upper bound | Kernel | Total |
|---|---:|---:|---:|---:|---:|
| Eleven fields, parity-free | 20 | 5 | 3 | 44 | **72=41M+31A** |
| Twelve fields, even index | 22 | 4 | 3 | 43 | **72=40M+32A** |

Thus the duplicate costs no net operation relative to the parity-free
variant. The counted kernel schedules are the existing general-scale
43 and44 components. A full source must still establish their pre-mask
bounds and the individual field ranges. This note does not present a
new complete source certificate by merely summing these components.

## 4. A restricted deletion-two packing saves two operations

When beta=2, c=1 and both the selector and prefix pairs sum to H.
The parity field is Qsum. Use the twelve-field order

    G,Qsum,Q0,Q1,S0,S1,N,Nbar,E,Ebar,M0,M1,

and define

    X=Q1+q²[S1+q²(Nbar+q²(Ebar+q²M1))].

Then

    P=G+q Qsum+q²[(q-1)X
                  +(1+q^4)(Qsum+q²H)+q^8L].             (2)

Equation(2) costs **20=10M+10A**, with every final join included.
Its powers are already in the four-product q^12 chain. G is first,
so the unit condition does not rely on the unknown selector. The
twelve-field parity argument applies. The resulting conditional
packing/powers/index/kernel ledger is **70=39M+31A**.

For general c, the matching pair sums are absent; restoring that
difference consumes the two saved operations. No universality theorem
for the restricted binary deletion-two system is assumed here, so the
restricted ledger is not an improvement of a universal bound.

## 5. Composition bookkeeping and verification boundary

The separately paid row geometry is exactly four operations:

    qm1=q-1, Rm1=R-1, head_product=H*Rm1, radix_product=R*v,

with comparisons head_product=qm1 and radix_product=q. The marker
verifier already pays for R=CA. Positivity gives R>=C>=3 and q>=R.
Once the kernel proves that q is a power of three, R dividing q makes
R a power of three too. The divisibility R-1 dividing q-1 then gives
q=R^t with a positive integer t. Thus this geometry costs **4=2M+2A**;
it does not need a separate J or the equation q=2J+1. The raw packing
and shared-index equations above do not use such a register.

The currently safe conditional tag verifier costs33 operations. Adding
the general72 ledger and this four-operation geometry gives **109**
before positive-domain adapters and ordinary raw-input conversion.
Those missing interfaces must not be silently treated as free.
A different single-projector history construction has its own
word count and proof obligations; this eleven-field ledger does not
settle that variant.

One local geometry fusion is also only a conditional tie in this safe
composition. If RH is already computed by equivalent row geometry
RH=H+(q-1), then C(G-Qsum)=RH replaces CA=R,AH,G=Qsum+AH with two
operations instead of three. After power geometry, H is prime to three,
so this recovers C dividing R and A=R/C. However the safe initial bound
Linit+alphaI=A still uses A. Removing A replaces that bound by
C*Linit+alpha=R, costing one extra operation and consuming the apparent
saving. No safe32-operation successor is claimed from this fusion.

`../verification/explore_tag_mask_packing.py` checks both packing
identities symbolically, every power chain, all DAG histograms, and the
actual imported43/44 kernel counts, and the four-operation geometry.
Finite valid joint-marker tuples
cover both parities of c, both choices of parity word, unknown initial
selectors, and zero auxiliary fields. Their native index digits and
the restricted formula are checked exactly. These tuples are packing
tests, not complete tag histories or an optimality search.
