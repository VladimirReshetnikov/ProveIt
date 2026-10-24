# A determinant guard from the canonical native leading digits

This note is an independent mathematical derivation for replacing source 64's
two common-sign guards on `F*alpha` and `F*C` by one ternary-Pos guard.
It applies specifically to the whole source-34 coefficient tuple
`mixed-parity-unrounded-1064921`, at ProveIt commit
`9cca523d9f27ad39d52993f4065cbd7e58f8bdd4`.

## 1. Fixed constants

Use the native constants

    rho = 2^121,
    L = 8801,
    B = rho^L = 2^1064921,
    c_top = 3296,
    next_C = 2195,
    d_top = 5495,
    f_top = 8791 = 3296 + 5495.

The coefficient of `rho^5495` in `D_C` is the selector-0 clause coefficient

    c0 = 105534389824824194647382298625
       = 0x1550000500015514150001001.

The source tile 0 has ordered labels `(2,435,3,1)`. In the formula of source
34 this gives

    c0 = 1 + sum_{t=0}^3 sum_{j=0}^9
                    bit_j(label_t+512) * 2^(10+2(10t+j))
           + sum_{j=40}^{43} 2^(10+2j).

In particular the following fixed finite bounds hold:

    2^96 <= c0 < c0+1 <= 3*2^95 < 2^97 < rho.

Define the two new fixed scales

    A = 2^1113,
    D = 2^666104.

The symbol `D` in this note is a fixed scale, not the source's Pell-root
coordinate named `D`; the final equation should rename this fixed scale,
for example to `scale_C`. These coefficients are fixed finite numerals,
with no consistency oracle. Both `A >= 2` and `D >= 2` hold. The clause
coefficient c0 is used to prove the canonical estimates; it is not an
additional coefficient of the new guard. There is no additional scalar
port multiplying q: its coefficient in W is the literal integer 1.

For arbitrary source coordinates put

    q = beta*J + 1,
    C = q - F - alpha,
    U = A*F,
    V = D*C,
    W = q - U - V,
    G = U*V-W^2.

Replace the two old rows

    F*alpha = Pos(FA1,FA2,FA3),
    F*C     = Pos(FC1,FC2,FC3)

by the single quadratic row

    G = Pos(t1,t2,t3),
    Pos(x,y,z) = 1+x^2+y^2+z*(z+1).

This deletes six private variables and inserts three, decreasing the
unrestricted quartic source from 41 to 38 variables and from 26 to 25
quadratic residuals. All other rows remain literally unchanged.

## 2. Soundness of the new guard, without native assumptions

The right-hand side Pos is always a strictly positive integer. Thus the
new row implies U*V>W^2>=0, so U and V are nonzero and have one common
sign. Also

    |W| < sqrt(U*V) <= (|U|+|V|)/2.

Because q=U+V+W, it follows that q has the same sign as U and V and

    |q| > (|U|+|V|)/2
        = (A*|F|+D*|C|)/2
        >= |F|+|C|,

where the last inequality uses A,D>=2. As A,D are positive, F and C
have the same sign as q. The strict inequality |q|>|F|+|C| then forces
alpha=q-F-C to have this same nonzero sign. Consequently F*alpha>0 and
F*C>0. This proof includes q<0 and does not use the source compiler.

Every positive integer admits a ternary Pos representation, by Legendre's
three-square theorem applied to 4n-3. Thus any zero of the new system can
be extended by the six old Pos variables to a zero of source 64's Q41.
All inherited soundness follows. No early positivity of q is assumed.

## 3. Canonical C blocks

The source-34 canonical accepting word has N occupied native cells and
q=B^N, with N>=1. Each cell is a chosen genuine tile, with all four
occupancy anchors set to 1. Its native digit C_j has its top nonzero digit
at exponent 3296, of value 1, and all remaining support lies at exponents
at most 2195. The lower dummy can have its permitted small value; this
does not affect the top-support argument. All radix-rho coefficients are
nonnegative and less than rho. Hence

    rho^3296 <= C_j < rho^3296 + rho^2196
                          <= (1+1/rho)*rho^3296.

This is a statement about the native canonical words, not a restriction
on every arbitrary integer solution of the final equation.

The facts are read directly from source 34's support E and from the
canonical construction. That construction places one occupied tile at
each cell of the padded accepting rectangle. The free lower dummy used
for rank tuning is at exponent 1063, well below 2195, and does not change
the anchor at 3296.

## 4. Canonical F blocks

At the rank-tuned canonical witness, the temporal shift is a whole number
of native cells, say w_c. Since q=B^N and the rank satisfies the documented
congruence R=d*w_c modulo dN, the transport multiplier w_source=2^R/q
has residue B^w_c modulo q-1. The native F word is therefore the least
nonnegative residue

    F = (D_C + B*D_R + B^w_c)*C mod(q-1).

Indices in the following formula are cyclic modulo N. Its native block j
is exactly

    F_j = D_C*C_j + D_R*C_(j-1) + C_(j-w_c).

Here D_R=rho. The largest exponent of D_C is 5495, with coefficient c0.
The largest exponent of C_j is 3296, with coefficient 1. Thus the unique
largest exponent of D_C*C_j is 8791, with coefficient c0. Every other
term has smaller exponent. The D_R and temporal contributions have
exponents at most 3297 and 3296, respectively.

There is also a direct coefficient bound that makes the carry step fully
explicit. The canonical C_j digits are 0 or 1 except that the lower dummy
at 1063 may use 0,1,2,3. Put S=sum_{e in E} c_e. The sum of all
coefficients of D_C is 4+2S. Every coefficient of D_C*C_j is therefore at
most 3*(4+2S), and each of the DR and temporal summands contributes at
most 3. Every F_j coefficient is at most 6S+18. This is less than
991*(2S+6)=M. Thus the source-34 finite estimate

    4*M+8 < rho,
    M = 991*(2*sum_{e in E} c_e + 6)

ensures that these native convolution coefficients are all below rho.
This agrees with the carry-free canonical reconstruction in its coefficient
proof. There is no carry into or past the leading digit.
Thus, allowing the much weaker generic bound rho-1 on each lower digit,

    c0*rho^8791 <= F_j < (c0+1)*rho^8791.

Since 8791<8801 and c0<rho, all F_j are below B-1. Thus their base-B word
is in (0,q-1), has the required residue, and is exactly the canonical F.
No ambiguity between residue 0 and q-1 occurs.

## 5. Uniform balancing inequalities

Put J_N=1+B+...+B^(N-1)=(q-1)/(B-1). The exact exponent identities

    121*8791+1113 = 1064921-97,
    121*3296+666104 = 1064921-1

show that summing the preceding block bounds and multiplying by the fixed
scales gives

    (c0/2^97)*B*J_N <= U < ((c0+1)/2^97)*B*J_N,
    (1/2)*B*J_N <= V < ((1+1/rho)/2)*B*J_N.

For N>=1 we have q<=B*J_N<q*B/(B-1). Also rho>=8 and B>=16, so
B/(B-1)<=16/15. Together with 2^96<=c0 and c0+1<=3*2^95 this gives

    q/2 <= U < (3/4)*(16/15)*q = 4*q/5,
    q/2 <= V < (1/2)*(9/8)*(16/15)*q = 3*q/5.

The same bounds hold after any permitted rank-tuning dummy changes and
for every size of a canonical accepting rectangle.

Set s=q/2. Write U=s+x, V=s+y, so 0<=x<3s/5 and 0<=y<s/5.
Since q=2s, W=-x-y. Direct expansion gives

    G = s^2+s*(x+y)-(x^2+y^2+x*y)
      > (1-9/25-1/25-3/25)*s^2
      = (12/25)*s^2 > 0.

Thus every canonical accepting witness satisfies the new strict determinant
inequality. The positive integer G admits a ternary Pos representation,
which supplies the three new variables. This proves completeness.

## 6. Scope and proof dependency boundary

This is an existence equivalence, not equality of source zero sets on the
old coordinates. The determinant guard need not contain arbitrary Q41 solutions.
Soundness maps a new zero to an old zero; completeness chooses canonical
native witnesses anew. This distinction is essential.

The new guard's algebra and canonical leading-block estimates are proved
above. The logical equivalence with finite ZFC refutations still imports
source 64's Q41 proof and its source-34 native-compiler/K215 calibration.
This note adds no end-to-end proof-assistant certificate.

The final sum of 25 squares remains degree exactly four: none of the
changed rows contains tau, so its tau^4 coefficient remains exactly 1.

## 7. Coefficient height and the total J^4 coefficient

Let A=2^1113 and D=2^666104 as above. Upon expanding C=beta*J+1-F-alpha,
the J^2 coefficient of the guard residual G-Pos is exactly

    -beta^2*(D-1)^2.

Its square therefore contributes

    beta^4*(D-1)^4

to the J^4 coefficient of Q38. This is a contribution, not the whole
coefficient. Inspection of the retained source64 Q41 rows shows that only
two other residuals contain a pure J^2 term: their coefficients are
`-beta^2` and `beta*(beta-MF)`. Consequently the exact total coefficient is

    [J^4] Q38 = beta^4*(D-1)^4 + beta^4 + beta^2*(beta-MF)^2.

All terms are nonnegative, and the first is positive. The shifted MF from
the complete source34 tuple is required here. The actual total coefficient
and the guard's squared contribution both have exactly 6,924,100 bits.
For an elementary exact bitlength proof, put d=1064921, e=666104 and
H=4(d+e)=6924100. Since d,e>=4, the contribution is at least
(15/16)^8*2^H>2^(H-1). Also (2^e-1)^4<=2^(4e)-2^(3e), so it is at most
2^H-2^(4d+3e). The source mask bounds give MF=beta+MF_native with
0<MF_native<beta; the other two terms therefore sum to less than
2^(4d+1). Since 3e>1, the total remains below 2^H.
This is a lower bound on Q38's maximum coefficient bitlength, not a claim
that this particular coefficient is the largest. Variable count, symbolic
description length, payload size and expanded coefficient height are
distinct measures of simplicity.

## Primary repository sources inspected

* Source 64 `integer41/PROOF41.md` and `PROOF44.md`, at the pin above.
* Source 64 `integer41/quartic41.json`, the literal 26-row packet.
* Source 34 `coefficients/COEFFICIENT_PROOF.md`, especially the complete
  support/constant recipe, uniform carry estimates, Boolean rank controller,
  and canonical parity section.
* Source 34 `coefficients/wang943_tiles.json`, including literal tile 0.

All paths are beneath
`Computability/DiophantineConsistency/con-zfc-diophantine-forms/`.
