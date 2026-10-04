# Independent audit: paid residue endpoint selector

## Verdict and scope

**Pass, relative to the pinned 174-operation bounded ant-history relation.**
The proposed three-positive-witness selector is equivalent to the single
endpoint condition

    x mod 481238074400 = 481225262775,
    y mod 576000 = 29948,
    final incoming heading = east.

The conventional free-fixed-numeral source costs **43 operations = 37M + 6A**.
A fully explicit source that constructs its two large numeral values from
literal 3 costs **101 operations = 94M + 7A**. Both sources are acyclic,
share their power constructions, and require exactly three additional
supplied positive witnesses. These are upper bounds for the displayed
sources, not minimality claims.

This audit neither executes upstream code nor re-proves the 174 theorem.
It reads the pinned statement and independently checks the endpoint
attachment. The literal atlas/load-layer admission and coordinate rotation
are premises supplied by the parent task. It does not settle the raw-input
compiler, positional dilation, periodic-background generator, or final
single-polynomial combination. No universal operation total is claimed.

Source read:
`/workspace/shared/literal-turmite-interface-20261003/sources/EXPLORATION_ANT_CHECKERBOARD_HISTORY.md`,
particularly sections 1, 2, 5, 6, 7, and 10.

## 1. Exact system and domains

Set the fixed integers

    u = 481238074400,  x0 = 481225262775,
    v = 576000,        y0 = 29948.

They obey 0 <= x0 < u and 0 <= y0 < v. Both periods are even; x0 is odd
and y0 is even. In the 174 relation, W=3^w with odd w>=3, Q=W^h with even
h>=2, and FinalHead=3^j with 0<=j<wh. The unique board coordinates are
x=j mod w, y=floor(j/w).

Supply only the positive witnesses HxPlus, HyPlus, BoundCol. Compute

    Hx = HxPlus - 1,
    Hy = HyPlus - 1,
    K = 3^x0,
    C = 3^u - 1,
    U = 1 + C*Hx,
    V = 1 + (W^v - 1)*Hy,
    Acol = K*U,
    T = W^y0.

Add the three equalities

    Acol + BoundCol = W,
    FinalHead = (Acol*T)*V,
    FinalSignPlus = 1.

The last equality does not require another subtraction: the 174 component
already computes FZ=FinalSignPlus-1. Gate outputs are arithmetic expressions,
not additional independently quantified witnesses. Hx and Hy, and some
intermediate products, may be zero; only the three supplied witnesses are
required positive. This is exactly the positive-adapter convention of 174.

## 2. Soundness

Hx,Hy>=0, and K,C,T,W^v-1 are positive. Thus U,V>=1. Since

    3^j = K*T*U*V

is a positive power of the prime 3, every positive integer factor on its
right is a power of 3. Write U=3^a and V=3^b for integers a,b>=0. This is
prime-factorization reasoning; no uncharged factorization operation is
part of the source.

The defining equations imply

    3^u-1 divides 3^a-1,
    3^(wv)-1 divides 3^b-1.

For d>0 and k>=0, the exact elementary criterion is

    (3^d-1) divides (3^k-1)  if and only if  d divides k.

To see the nontrivial direction, divide k=qd+r with 0<=r<d. Reduction
modulo 3^d-1 leaves 3^r-1, which lies between 0 and 3^d-2; it can be zero
only when r=0. The case k=0 is included because every positive integer
divides zero. Consequently a=um and b=wv*n with m,n>=0.

Put x*=x0+um and y*=y0+vn. The head equation becomes

    j = x* + w*y*.

The positive column slack proves Acol<W, hence 3^x*<3^w and 0<=x*<w.
Therefore this is the canonical row-major decomposition of j, so x=x*
and y=y*. Since j<wh, also y<h. This proves both required coordinate
residues. The 174 bound FinalHead<Q supplies the row bound; the selector
needs no separate row slack.

No conditions such as u|w, v|h, gcd(u,w)=1, or divisibility of W-1 by
3^u-1 were used. The selector is valid for every existing odd width and
even height capable of containing the selected site. In particular,
Acol<W deliberately implies w>x0; because w and x0 are odd, w>=x0+2.

The column slack is essential. For the small example u=v=2, x0=1, y0=0,
w=3, Hx=10, Hy=0, the unbounded product has exponent j=5. Its canonical
coordinates are (2,1), which fail the desired residues, while Acol=3^5
has carried past the row width. BoundCol>0 excludes this false endpoint.

## 3. Necessity and zero quotients

Suppose a 174 history ends at an east-heading site whose canonical
coordinates satisfy the displayed residues. Because the residues are
canonical and board coordinates are nonnegative,

    x=x0+um, y=y0+vn for some m,n>=0.

Choose

    Hx = (3^(um)-1)/(3^u-1),
    Hy = (W^(vn)-1)/(W^v-1),
    HxPlus = Hx+1,
    HyPlus = Hy+1,
    BoundCol = W-3^x.

These are integers by the finite geometric-sum identity. The first two
quotients are nonnegative and become zero exactly at m=0 or n=0,
respectively. Their positive adapters then equal 1, so endpoints in the
first permitted residue column or row are not accidentally excluded.
BoundCol is strictly positive because x<w. All three new witnesses are
positive and all endpoint equalities hold. They are in fact uniquely
determined by the history's W and final endpoint.

This proves necessity without an extra positive quotient, root, exponent,
divisor, row-bound, or parity witness.

## 4. Heading and checkerboard parity

x=x0+um is odd, and y=y0+vn is even. Thus x+y is odd and the selected site
is white. Equivalently j=x+wy is odd since w is odd. In the 174 convention,
on white squares sign zero is east and sign one is west; on black squares
the same signs instead mean north and south. Therefore fixing
FinalSignPlus=1, hence FZ=0, selects east precisely here.

The initial 174 head has even flattened index. Each ant step changes
checkerboard color. Therefore every accepted selector history has an odd
number of ant steps. This is a derived consistency check; the separate
claim about which loaded CA layers are admissible is supplied by the
literal simulation/rotation interface and is not reconstructed here.

## 5. Exact conventional fixed-numeral ledger

This model follows the 174 note: fixed integer numerals are free inputs,
but multiplication by them is charged. The ports K and C have exactly the
specified values above. They are not arbitrary or existential parameters.
A source file that accepts unconstrained user-supplied values at those
ports would not implement this selector.

The JSON source records exact recipes for the two fixed integers. It does
not materialize their enormous decimal or binary expansions. This is a
precise description of two free fixed numeral ports, not a claim that
constructing them from literal 3 is free in a stricter source language.

For variable W, build the shared ladder

    P[0]=W; P[i]=P[i-1]*P[i-1] for i=1,...,19.

This is 19M, with P[i]=W^(2^i). Then use ordinary product chains on:

    29948:  bits {2,3,4,5,6,7,10,12,13,14}, 9M;
    576000: bits {9,11,14,15,19},           4M.

Thus both variable powers together cost exactly 32M.

The remaining acyclic source is:

| Instruction | Class |
|---|---:|
| Hx=HxPlus-1 | A |
| Hy=HyPlus-1 | A |
| CxHx=C*Hx | M |
| U=1+CxHx | A |
| VPowerMinusOne=WToV-1 | A |
| VIncrement=VPowerMinusOne*Hy | M |
| V=1+VIncrement | A |
| Acol=K*U | M |
| ColumnBound=Acol+BoundCol | A |
| AT=Acol*T | M |
| EndpointHead=AT*V | M |

The three assertions are ColumnBound=W, EndpointHead=FinalHead, and
FinalSignPlus=1. Under the 174 source convention, equations and aliases
are free; subtraction used to build an asserted residual is not silently
added. Combining the equations into one polynomial is a separate task.
The non-power ledger is 5M+6A=11, and total is 37M+6A=43.

## 6. Fully paid fixed-numeral construction

This alternate compact source has only literal ports 1 and 3. It computes
K and 3^u using a shared multiplication DAG, then computes C=3^u-1.
All fixed and variable powers are paid. The exponent values in names,
comments, or verification metadata are labels, not arithmetic input ports.

Build B[0]=3 and B[i]=B[i-1]*B[i-1] for i=1,...,38: 38M.
The relevant bit positions are

    x0: {0,1,2,4,5,7,9,10,14,15,17,22,24,25,27,36,37,38},
    u:  {5,10,14,17,18,26,27,36,37,38}.

Their common part has eight positions

    {5,10,14,17,27,36,37,38}.

Form the product of these eight B[i] in 7M. Multiply that common product
by the ten x0-only B[i] in 10M to obtain K. Multiply the same common
product by the two u-only B[i], at positions 18 and 26, in 2M to obtain
3^u. The common partial product is shared, not recomputed.

Thus both fixed powers cost 38+7+10+2=57M, followed by one subtraction
for C. Add the same 32M variable-power DAG and 5M+6A non-power source:

    fixed numeral construction: 57M+1A = 58,
    variable power construction: 32M+0A = 32,
    remaining selector:          5M+6A = 11,
    total:                     94M+7A = 101.

A less-shared square-ladder construction would use 38+17+9=64M for the
two fixed powers, hence 108 operations altogether. That is also valid,
but the explicitly supplied 101-operation source shares the eight-bit
common product. Neither figure is asserted to be optimal.

## 7. Independent reproducible checks

Run only the newly authored local audit:

    python /workspace/shared/literal-turmite-endpoint-20261003/review/audit_endpoint.py

It reads no upstream Python and evaluates neither giant fixed power.
It produces:

- `endpoint_fixed_numerals_source.json`: all 43 gates and three assertions
- `endpoint_paid_numerals_source.json`: all 101 gates and three assertions
- `endpoint_audit_receipt.json`: exact ledgers, exponent checks, and hashes

The checker verifies every source reference is available before use,
proves the multiplication DAG exponents by integer addition, checks all
four power targets, and recounts each opcode. A separate small-domain
arithmetic regression checks 17,280 candidate endpoints for even periods
2,4,6, canonical odd/even residues, odd widths 3,5,7,9, and even heights
2,4,6,8. It finds 900 accepted endpoints, including 600 instances each
with Hx=0 and Hy=0, confirms uniqueness and white parity, and verifies
the row-carry counterexample when the column bound is omitted.

The regression is supporting finite evidence. The prime-factorization,
divisor, canonical-coordinate, and positive-witness arguments above
establish the arbitrary-integer equivalence.
