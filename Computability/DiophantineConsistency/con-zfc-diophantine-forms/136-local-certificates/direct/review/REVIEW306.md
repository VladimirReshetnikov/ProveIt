# Independent mathematical and literal review of the 306-integer equation

## Verdict and exact scope

The reduction from the pinned 324-integer equation to the supplied
306-integer equation is valid under the unchanged parent frame, anchor,
and power-congruence interfaces. The two explicit witness transformations
in `../PROOF.md` establish equivalence of zero existence.
I found no unproved sign premise, omitted zero-index case, or circular use
of a deleted representative guard in this new reduction.

This review independently re-derived the unbounded orientation and signed
power arguments and checked their actual polynomial ports. Its checker
imports no constructor code and re-expands all 206 residual squares by an
unordered-pair algorithm. It is a separate review within an AI-assisted
workflow, not external human refereeing or a proof-assistant kernel check.
The retained parent C222/ZF/ZFC calibration is inherited; the current
review does not rebuild that calibration or its transitive formal source.

The reviewed parent is the centered equation of package 131 at ProveIt
commit `1c5367452a0bd4dd7e9e4bceb1508b62dbd2ff61`. Its canonical JSON hash is
`32618060c22765f54423b53f9faef437d736494da82aef309efe96210d6cbadd`.
The reviewed successor hash is
`d51d75d2c6398fa3410b19ae43ba8d80f86c668ad670a803f6777a2af221c189`.

## 1. The anchor remains available before all removed signs

The nine deleted predicates concern only the encoded CRT representatives
minus one. They are not inputs to the parent square-frame argument, the
full indexed Pell anchor, or the absolute ordinate cap. The retained frame
contains the complete actual affine base, exponent, and output expressions,
including the expressions that may now have either sign. Consequently it
still gives

    W >= 258,  A > W^W,  A-1 > 4W^3,
    |k_i| < W,  |n| < W,  |m| < W.

All fifteen principal norms can therefore be classified as

    x_i = sigma_i X_{j_i}(A),
    y_i = epsilon_i Y_{j_i}(A),  0 <= j_i < W,

with independently signed coordinates. The bound on the actual index
comes from the retained ordinate cap, not the changed pool row. This
separation is essential: one must not invoke the old signed-index
conclusion from a pool equation that has just been changed.

For clarity, the inherited anchor is also compatible with signed private
coordinates. Its cap gives C>W. Its positive common multiplier gives
J=C^2(e+1)>0. Classification yields C=Y_i(A), J=Y_l(A), and squared
divisibility gives C|l. The comparison center is 1 modulo 4C and A modulo
its trace modulus. The trace and ordinate residue arguments then force
i=+/-W modulo 2C. Since 1<=i<=C and W<C, only i=W remains. This argument
uses none of the nine removed encoded-coordinate predicates. Their
deletion does not alter any literal anchor row or retained anchor graph.

## 2. The linear orientation argument is an unbounded theorem

For the selected nine pairs let

    S = sum_selected (1-x_i).

The new pool equation is

    sum_all15 (y_i-k_i)^2 + S = (A-1)q0.

The congruences X_j(A)=1 and Y_j(A)=j modulo A-1 give divisibility by
A-1 of the *different*, bounded integer

    E = sum_all15 (epsilon_i*j_i-k_i)^2
          + sum_selected (1-sigma_i).

Each orientation term in E is zero or two. Thus

    0 <= E <= 60(W-1)^2 + 18 < 4W^3 < A-1.

The strict middle bound is immediate for W>=258; for example the left
side is less than 61W^2, while 4W^3 is at least 1032W^2. Hence E=0.
Every ordinate has its intended signed index, and every selected trace
has positive orientation.

It would be an error to assert that S, or the actual left side of the
new pool, is nonnegative or smaller than A-1. Neither assertion is
needed or generally true. The proof concerns the bounded residue
representative E only. In particular q0 must remain unrestricted.
Inspection confirms that no nonnegativity graph is imposed on q0.

This linear tail has a sound constructive converse. For true selected
traces, each 1-X_k(A) is divisible by A-1. Its contribution may be added
to or subtracted from the unrestricted old quotient without changing any
other row. There is no additional existence problem for Pell witnesses.

## 3. Signed power recovery, including index zero

For 2<=n<W set T=2An-n^2-1. Since n<A and this expression is increasing
in n on the relevant interval,

    T >= 4A-5 > W^W.

For j>=1 define

    H_j = X_j(A)+(n-A)Y_j(A),
    J_j = X_j(A)-(n-A)Y_j(A).

The exact recurrence gives H_j=n^j modulo T, and the exact norm identity
gives H_j J_j=1+T Y_j(A)^2. The retained request equates the corresponding
signed expression to m modulo T.

If the intended index is -j<0 and the trace is positively oriented, the
request gives m*n^j=1 modulo T. But

    |m*n^j-1| <= (W-1)^W+1 < W^W < T,

so m*n^j=1 as an integer equality. This is impossible for n>=2 and j>=1.
The same estimate excludes a negatively oriented trace at a positive
index, since that case gives m*n^j=-1. No sign hypothesis on m is used.

At a positive index and positive trace, the small ordinary difference
m-n^j must vanish. At index zero, y=0 and the selected trace is x=1,
so m=1 by the same modulus bound. Thus the precise conclusion for each
newly oriented pair is k>=0 and m=n^k. In particular this theorem does
not imply k>=1; the separate zero-index arguments in the construction
are necessary.

The nine actual selected requests all have n=q+1. The retained front
already gives q>=2, so n>=3. Their actual bases, outputs, and signed
indices are all in the frame ledger. I checked the literal request
membership at calls 5,7,8,9,10,12,13,15,16.

## 4. Early bootstrap and the ninth zero-index exclusion

The unchanged front guards give r,s,o>=0 and x>=0; the cofinal horizon
row gives t>=16. Hence B=r+s+1>=1 and q=B+o+1>=2 without using any of
the nine removed graphs. The t pair has its positive requested index.
The genuine q-base call at t excludes the negative trace branch by
the preceding argument and orients the t pair positively.

The same pair then gives V0=(F^2+1)^t. This remains valid when its base
is one: the canonical Pell expression is 1 modulo 2A-2, and the output
bound gives the exact value 1. The literal ceiling rows imply

    FB=V0+s>0.

Thus F>=1. Writing b=F^2+1 gives b>F and b^(t-1)>F, so

    FB >= b^t > Fb,  hence B>b>0.

The reciprocal-index rows give

    B*index_quotient = F^2+k_index+1.

If k_index=0, their right side is b, strictly between zero and B. No
integer quotient can satisfy that equality. Thus k_index>=1. This
argument does not assume a sign for the reciprocal quotient and does not
use any factorial or binomial interpretation.

The preliminary output-residue proposal had needed q>36. The final
306-variable construction does not need that threshold: its orientation
modulus is A-1 and its bounded alphabet is {0,2}. The retained q>=2 is
sufficient. A stronger bootstrap bound B>=2^t is true but unnecessary.

## 5. The eight-factor guard restores strictness safely

The eight remaining requested indices have first been shown nonnegative
without using their product guard. The six monic rows compute P2 through
P7 exactly. The final row says

    P7*k_vq - 1 = a^2+b^2+c(c+1).

Its right side is nonnegative at every integer triple. Therefore the
product of the eight nonnegative indices is at least one; every factor
is consequently at least one. Applying this inference before establishing
nonnegativity would be invalid, but the construction uses the correct
order.

Conversely, positive factors make the left side nonnegative. Legendre's
three-square theorem represents every n>=0 as a^2+b^2+c(c+1): apply it
to 4n+1, whose residue modulo four forces exactly one of the three squares
to be odd. This supplies the required fresh triple. The last multiplication
is already quadratic in P7 and k_vq, so no separate P8 coordinate is needed.

## 6. Literal charts, privacy, and the quotient map

The source-to-parent projection and final centering certificates give the
following actual requested-index and positive-trace ports:

| Requested index | Centered expression | Trace coordinate |
|---|---|---:|
| a | z10-1 | 174 |
| b | z11 | 180 |
| c | z12 | 184 |
| d | z13 | 188 |
| S | z14 | 192 |
| Sp | z15 | 200 |
| u | z16 | 204 |
| vq | z17 | 212 |
| index | z18 | 216 |

The old nonnegative variables are these expressions minus one. In
particular the first old guard is z10-2>=0, while the first product
factor is z10-1. Confusing those two offsets would give the wrong equation.
All nine selected traces have zero centering shift.

Only old row 180 changes, by the addition of

    9-z174-z180-z184-z188-z192-z200-z204-z212-z216.

The removed rows are 184 through 192, and their complete private triples
are old coordinates 252 through 278. Each such coordinate occurs in its
own deleted row only. Old coordinate 242, the pool quotient, occurs only
in row 180. The main center is A=z151+1, so A-1=z151>0 at every zero.

With S denoting the added trace tail, the forward map is

    q_new=q_old+S/(A-1),

and the reverse map is

    q_old=q_new-S/(A-1).

Both fractions are integral after orientation. The signs in the two maps
agree with the literal residual E+S-(A-1)q_new. All other retained
coordinates stay fixed. Old deleted triples must be freshly chosen from
the recovered nine nonnegative scalars; they cannot in general be copied
from the new product triple.

I also checked the earlier monic projection certificate: all nine raw
guard rows survived projection, and none of its 216 restoration
polynomials depends on any of the deleted 27 guard coordinates or the
changed raw pool quotient. Thus deleting the private triples and changing
the private quotient does not break restoration of a frame, norm, power
port, or other body coordinate. This strengthens the privacy argument
beyond checking final-coordinate occurrence sets alone.

## 7. Independent exact finite results

The checker `review306.py` compares all 199 retained rows,
the exact trace-tail modification, all seven new product/guard rows,
the retained-coordinate map, all nine raw selected power ports, and the
entire collected quartic polynomial. Its receipt is
`REVIEW306_CHECK.json`.

The independently measured result is:

| Quantity | Value |
|---|---:|
| Unrestricted integer variables | 306 |
| Quadratic residuals | 206 |
| Exact degree | 4 |
| Collected monomials | 6,259 |
| Coefficient height | 128,446 |
| Residual coefficient height | 256 |

For an explicit degree-attainment witness, the coefficient of z0^4 is
85. The variable/row counts also follow structurally:
324-27+6+3=306 and 208-9+6+1=206. The support is larger than the parent's
5,808 monomials; the claim is a dimension and row reduction at unchanged
degree and coefficient height, not dominance in every measure.

## 8. Excluded speculative variants

This review approves the displayed 306-variable construction only. It
does not approve deleting the strict-product row and allowing zero CRT
representatives, or replacing the positive-radix guard by an odd-square
parameterization. Either change would need an additional complete
semantic or completeness proof and a separately bound literal equation.
Neither speculative improvement is used in the present theorem.
