# Independent review of the calibrated determinant construction

Reviewed 23 October 2026. This is an independent AI-assisted mathematical and
implementation review, not external human peer review or a proof-assistant
certificate. The reviewer did not import the builder's polynomial engine.

## Conclusion

The final determinant guard has a valid soundness proof and a valid
canonical-completeness argument under the explicitly inherited source 34
native compiler theorem. It uses the two power-of-two scales
`cone_A=2^1113`, `cone_B=2^666104`, with the literal coefficient 1 on `q`.
There is no `cone_r` port. It gives a quartic in 38 unrestricted integers
with 25 quadratic residuals. The centered monic projection yields 32
integers at degree 6, and the second projection yields 27 at degree 8.
No mathematical or transcription defect was found in the final reviewed
files. This review supersedes the earlier review with three new ports.

## 1. Independent mathematical derivation

Write `A=2^1113`, `B=2^666104`, and use

    q=beta*J+1, C=q-F-alpha,
    U=A*F, V=B*C, W=q-U-V.

The new row is `UV-W^2=1+t1^2+t2^2+t3(t3+1)`.
Its right-hand side is always positive. Therefore UV>W²>=0, so U,V have
one common nonzero sign and |W|<sqrt(UV)<= (|U|+|V|)/2. The sum
q=U+V+W has the same sign, and

    |q| > (A|F|+B|C|)/2 >= |F|+|C|,

because both fixed scales are at least 2. Thus F,C,q,alpha have the same
nonzero sign. The old two product guards can be restored using the
ternary representation of every positive integer. This step assumes no
early positivity of q and applies to arbitrary signed integer assignments.

For completeness let rho=2^121 and B_native=rho^8801=2^1064921.
The coefficient proof's canonical words have leading native digits C_j:1
at exponent 3296 and F_j:c0 at exponent 8791, where

    c0=105534389824824194647382298625.

Their lower terms are carry-free: independent re-evaluation of every c_e
gives the exact mass bound 6*S+18 < 991(2*S+6) and
4*991(2*S+6)+8 < rho. There are no higher nonzero terms, and the rank
controller's dummy at 1063 does not alter these leading digits. The
cyclic transport is by a whole native cell, so all blocks retain the same
leading-digit bounds. For each canonical native block,

    c0*rho^8791 <= F_j < (c0+1)*rho^8791,
    rho^3296 <= C_j < (1+1/rho)*rho^3296.

Let q=B_native^N, N>=1, and J_N=(q-1)/(B_native-1). Then
q<=B_native*J_N<q*B_native/(B_native-1). The fixed scales obey

    1113+121*8791  =1064921-97,
    666104+121*3296=1064921-1.

Also 2^96<=c0, c0+1<=3*2^95, rho>=8, and B_native>=16. Consequently

    q/2 <= U < (3/4)*(16/15)*q =4q/5,
    q/2 <= V < (9/16)*(16/15)*q=3q/5.

These bounds are uniform in the number of occupied native cells. Put
s=q/2, U=s+x, V=s+y, so 0<=x<3s/5 and 0<=y<s/5. Now W=-(x+y), and

    UV-W²=s²+s(x+y)-x²-xy-y²
          >s²-(9+3+1)*s²/25
          =12s²/25=3q²/25>0.

The new Pos witnesses therefore exist. This argument chooses fresh
canonical accepting witnesses. It does not claim that every old Q41 zero
already satisfies the determinant guard. That distinction is essential.

## 2. Exact independent checks

`check_integer_independent.py` implements an AST parser and sparse polynomial
arithmetic independently, using only the Python standard library. It imports
none of the builder modules. It checked:

- all retained Q41 rows against Q38, plus the exact new determinant row;
- all and only listed variables live, and the exact residual counts;
- every coefficient of all three expanded sums of squares;
- every monic defining row, triangular centering and elimination step;
- all 25 Q38 residuals restored exactly by each projection;
- degrees 4, 6, 8 using respective coefficients `[tau^4]=1`,
  `[r^2*c^4]=4`, and `[a^4*f^4]=1`, independent of fixed-port values;
- all six actual fixed integer payloads, reconstructed from the native
  recipe without importing the coefficient builder;
- the selector-zero value c0, 989-position support, leading-position gap,
  uniform carry bounds, the two scale exponents and the c0 interval.

The expanded symbolic term counts are 628, 586, 707 for Q38, S32, O27.
These counts include fixed ports as coefficient symbols and are not
arithmetic circuit sizes.

It also ran 48 arbitrary signed-integer restoration assignments with small
substitute port values and 15,625 bounded sign cases. These are explicitly
diagnostics; the exact polynomial checks and written inequalities carry
the universal claims. Normal and optimized Python runs pass.

## 3. Remaining inherited proof obligations

The new proof relies on source 64's Q41 existence equivalence and source 34's
canonical native compiler, rank controller and K215/refutation calibration.
This review read their relevant retained statements and checked compatibility;
it does not independently reconstruct every transitive Pell or logical proof.
Finite arithmetic checks do not establish Con(ZFC), find a consistency witness,
or supply a new formal derivation in an object-language ZFC calculus.

The hashes of the literal reviewed packets, all six reconstructed port
hashes and exact-check counts are in `INTEGER_INDEPENDENT_REVIEW.json`.
