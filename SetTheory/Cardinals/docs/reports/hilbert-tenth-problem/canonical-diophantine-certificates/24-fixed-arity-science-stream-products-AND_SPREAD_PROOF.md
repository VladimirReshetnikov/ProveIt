# Paid fixed-arity AND and arbitrary-digit stream spreading

Own derivation, 4 October 2026. This module uses only the explicit polynomial POWER macro in the inherited mathematical dependency and the fully proved MaskSubset module in `MASK_SUBSET_PROOF.md`. No bitwise operator, geometric-series function, division operation, or variable exponent remains unexpanded in the stated arithmetic implementations. Bitwise notation below states semantics and proofs only.

The ledger convention is the one in `MASK_SUBSET_PROOF.md`: inputs are external, every internal variable is strictly positive, zero-capable values use positive adapters, and expression nodes are not additional quantified variables.

## 1. Bitwise AND with one MaskSubset call

### Inputs and equations

Given nonnegative input integers `x,y,z`, introduce three positive witnesses `aPlus,bPlus,T`. Set the expressions

    a=aPlus-1,  b=bPlus-1.

Impose

    x=z+a,
    y=z+b,
    POWER(2, x+y+1, T).

Form the two nonnegative expressions

    M = x + T y + T^2(a+b),
    Q = z + T z + T^2 a,

and impose one call

    MaskSubset(M,Q).

This is the complete arithmetic implementation of `AND(x,y,z)`. In particular, three independent subset calls are unnecessary.

### Proof

The first two equations give `a=x-z>=0,b=y-z>=0` and `z<=x,y`. Let `h=x+y`. All six block values `x,y,a+b,z,z,a` lie in `[0,h]`. Since `T=2^(h+1)>h`, each is a valid single base-`T` digit. As `T` is a power of two, the three base-`T` blocks occupy disjoint binary bit intervals. Thus the one MaskSubset call is equivalent to the conjunction

    z is a binary subset of x,
    z is a binary subset of y,
    a is a binary subset of a+b.

For any nonnegative `a,b`, the last condition is equivalent to `a & b = 0`: if `a` is a binary subset of `a+b`, subtracting its set bits entails no borrowing, so `b=(a+b)-a` has no binary 1-position in common with `a`; conversely, disjoint supports make addition carry-free.

Likewise, the first condition says that `x=z+a` is a union of the disjoint binary supports of `z` and `a`; the second says the same for `z` and `b`. With `a` and `b` disjoint, the common binary support of `x` and `y` is exactly that of `z`. Hence the arithmetic relation implies `z=x & y`.

Conversely, if `z=x & y`, choose `a=x-z,b=y-z`. These residuals are nonnegative, disjoint from `z`, and disjoint from each other. The three block subset conditions hold; after choosing the true value of `T`, completeness of MaskSubset supplies all remaining positive witnesses. The case `x=y=z=0` uses `a=b=0,T=2` and is valid without an exception.

### Exact AND ledger

Outside the called modules, use the following nodes:

- `aPlus-1,bPlus-1,z+a,z+b,x+y,(x+y)+1` [6 A]
- `T^2,Ty,Tz` [3 M]
- `a+b` [1 A]
- `T^2(a+b),T^2a` [2 M]
- `x+Ty,(x+Ty)+T^2(a+b),z+Tz,(z+Tz)+T^2a` [4 A].

The outer cost is `5 M + 11 A`, three positive witnesses, and two equations. One POWER adds `31 M+39 A`, 25 witnesses, and 15 equations. One MaskSubset adds `96 M+127 A`, 83 witnesses, and 48 equations. Therefore AND uses exactly

    132 M + 177 A = 309 operations,
    111 positive internal witnesses,
    65 polynomial equations,
    four POWER calls in total.

Input positive adapters, if required, are additional. The output `z` is an input port of this graph; quantifying it as `zPlus` adds one external positive witness and charging `zPlus-1` costs one A. We make no global optimality claim; the point is one MaskSubset invocation rather than three.

## 2. SPREAD for unrestricted radix digits

### Semantic theorem

Let `B=2^k` with `k>=1`, `n>=1`, `s>=n+1`, and `0<=U<B^n`. Write the unique base-`B` expansion

    U=sum_{i=0}^{n-1} u_i B^i,   0<=u_i<B.

There is a fixed-arity polynomial relation asserting precisely

    W=sum_{i=0}^{n-1} u_i B^(s i).

The digits are unrestricted full base-`B` digits, not just binary digits. Neither `n`, `s`, nor `B` changes the number of equations or witnesses.

### Arithmetic implementation when B is a supplied power of two

Inputs are `B,n,s,U,W`, with `B>=2` a power of two, `n,s>=1`, and `U,W>=0`. The relation itself enforces both `U<B^n` and `s>=n+1`.

Introduce seven positive outer witnesses

    P,C,E,G1,G2,sigma,g.

Use exactly three fresh POWER calls:

    POWER(B,n,P),
    POWER(B,s-1,C),
    POWER(C,n,E).

Form the expressions

    D=B C,  F=E P.

Impose four outer equations:

    (C-1) G1 = E-1,
    (D-1) G2 = F-1,
    U+sigma = P,
    s = n+g.

Finally impose the single complete AND module

    AND(U G1, (B-1)G2, W).

All displayed powers have been explicitly accounted for. The expression `s-1` is nonnegative because `s=n+g` with `n,g>=1`, and indeed `s-1>=n>=1`. Therefore `C=B^(s-1)>=2`, so the third POWER call has a valid base. The geometric-series denominators `C-1,D-1` are strictly positive.

If the radix is not already certified, introduce positive `B` and one additional POWER call `POWER(2,k,B)`, where the external input `k` is strictly positive.

### Geometric-series identification

The powers force

    P=B^n,
    C=B^(s-1),
    E=C^n=B^(n(s-1)),
    D=BC=B^s,
    F=EP=B^(ns)=D^n.

Since `C,D>=2`, the first two outer equations uniquely force

    G1=sum_{j=0}^{n-1} B^((s-1)j),
    G2=sum_{j=0}^{n-1} B^(s j).

Both values are positive because `n>=1`. The remaining two outer equations enforce exactly the required strict size and stride bounds.

### Distinctness and no-carry proof

In the product `U G1`, a coefficient `u_i` occurs at exponent

    i+(s-1)j,   0<=i,j<n.

All these `n^2` exponents are distinct: equality of two implies

    i-i'=(s-1)(j'-j).

The left-hand absolute value is at most `n-1`, strictly less than `s-1`, so both sides must vanish. Consequently every base-`B` digit of the product is either a single `u_i` or zero; there are no overlapping contributions and no carries. This uses only the full-digit bound `u_i<B`.

The integer `(B-1)G2` has base-`B` digit `B-1` at exactly the positions `s ell`, `0<=ell<n`, and zero elsewhere. As `B=2^k`, this mask selects exactly all `k` binary bits of each of those radix digits.

For a selected exponent `s ell`, the equation

    i+(s-1)j=s ell

can be rewritten

    i-ell=(s-1)(ell-j).

Again `|i-ell|<=n-1<s-1`, so necessarily `i=ell` and `j=ell`. Therefore the selected digit is exactly `u_ell`. Applying the verified AND relation yields precisely

    W=sum_{ell=0}^{n-1} u_ell B^(s ell).

This proves soundness. Conversely, given the desired stream spreading, take the indicated powers, geometric sums, and the positive slacks `sigma=B^n-U` and `g=s-n`; all outer equations hold, and the exact bitwise identity just proved supplies the AND witnesses. This proves completeness.

The case `n=1` works unchanged for every `s>=2`: both geometric sums equal 1, and the output equals U. The module intentionally has `n>=1`. An application needing empty arrays can pad to one zero digit, or add a fixed-size empty/nonempty branch; no unclaimed zero-length denominator convention is used.

### Exact SPREAD ledger

Besides the three POWER modules and one AND module, use these nodes:

- `s-1` [A]
- `D=BC,F=EP` [2 M]
- `C-1,E-1` [2 A], and `(C-1)G1` [M]
- `D-1,F-1` [2 A], and `(D-1)G2` [M]
- `U+sigma,n+g` [2 A]
- `B-1` [A]
- `U G1,(B-1)G2` [2 M].

The outer cost is `6 M + 8 A`, seven positive witnesses, and four equations. The three POWER modules cost `93 M + 117 A`, 75 witnesses, and 45 equations. AND costs `132 M + 177 A`, 111 witnesses, and 65 equations. Thus, for a supplied power-of-two B, the complete SPREAD relation costs exactly

    231 M + 302 A = 533 operations,
    193 positive internal witnesses,
    114 polynomial equations,
    seven POWER calls in total.

If B is internally created using `POWER(2,k,B)`, add 70 operations, 26 positive witnesses (the POWER internals plus the B output), and 15 equations. The total then is

    262 M + 341 A = 603 operations,
    219 positive internal witnesses,
    129 polynomial equations,
    eight POWER calls in total.

Positive input/output port adapters are additional exactly as described for MaskSubset. The constants 2 and 4 can be shared globally; if only literals 1 and 3 are initially free and neither is already constructed, two additions suffice to construct both.

## 3. Nested block application

SPREAD acts on any digit-block radix that is a power of two, not just a small fixed base. For example, if a row contains `Lx` base-32 cells, then an entire row is a digit in radix `32^Lx=2^(5Lx)`. A stream of `Ly` such rows can therefore be spread at any integer stride `s>=Ly+1`. The output row spacing in base-32 positions is `s Lx`.

After rows have been spread, one may treat a whole plane as a digit in a sufficiently large power-of-two radix, then apply the same fixed SPREAD formula to the stream of planes. Choosing desired physical spacings as suitable multiples ensures integral strides. In an application, explicitly verify the digit-count `n`, the block radix, `s>=n+1`, and the packed-input bound for each stage. This note does not assert a particular multidimensional layout without those checks.

## Validation scope

`verify_and_spread.py` independently checks the AND block-packing equivalence on small triples and the SPREAD multiplication/mask identity on finite streams. It tests semantic arithmetic identities without materializing the fantastically large nested POWER witnesses from the AND mask formula. No upstream code is executed. The universal no-carry and uniqueness arguments above, not the finite tests, establish the theorem.
