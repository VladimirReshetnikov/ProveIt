# A product history scale gives a253-operation U9 polynomial

The [literal source](neary_woods_universal_product_scale253.py) saves one
multiplication from the [native-bound254 construction](neary_woods_universal_native_bound254.md).
The default is **253=132M+121A**, with **252 certificate operations**, one
comparison, **43 positive witnesses**, four fixed positive program parameters
and ordinary positive input. Its conservative total-degree bound is **1147**,
down from1203. The independent fifth duration-bound interface is retained.
The [receipt](neary_woods_universal_product_scale253.json) records complete
canonical schedules and both single-group and three-group checks.

This transfers the [group product-scale idea](group_projective_product_radix_scale.md)
to the actual fixed U9 compiler. The numerical U9 program recipes, input
loader, low recoder, exact physical counter and chronology are unchanged.
The theorem preserves the accepted-input relation on the same valid shifted
program slices. The prescribed joint native scale and index change, so its
private positive witnesses are rebuilt; no bijection between the supplied
joint-native zero tuples or arbitrary-point equality to254 is claimed.
The independent75/87 bounds remain unchanged.

## 1. Reuse the paid history-radix product

Use b for the history radix, P for its scale and J for its selector sum.
The current supplied history height is D>=1 and b=c_h D, where the actual
fixed compiler multiplier c_h is a power of two at least32. Put T=P^9.
The existing history source has three lower blocks H0,M0,Z and the ports

    H_old=H0+bT, M_old=M0+(b-1)T, Z_old=Z.

Its high native scale is P^11. Write q0 for the low **padded** recoder
scale16*B_rec*S_rec; its actual low ports a0,b0,z0 are strictly between0
and q0 before native typing. The complete joined ports are

    A=a0+q0 H, Bport=b0+q0 M, Zport=z0+q0 Z.

Use instead

    H=H0+2T, M=M0+T, Qhigh=bT, q=q0*bT.              (1)

Every coefficient and product in(1) is paid. Specifically:

* Keep the existing `hist__top_history__87=b*T`, now used as Qhigh.
* Change `hist__top_mask__92=(b-1)*T` to the charged product2*T.
* Feed2*T to H's existing addition, and feed the already paid T to M's.
* Feed b*T to the existing joined-scale multiplication by q0.
* Delete the now-private `hist__P11__99=T*P^2` multiplication.

A topological sort places these same rows before their new consumers.
Thus exactly one M disappears; no addition, comparison, fixed numeral
role, supplied coordinate or finalizer gate is added. The active fusion
interface names b*T as its high scale. Historical packet records remain
provenance and must not be evaluated as the current high-port recipe.

The guard reconstructs the complete supported254 caller, checks these
literal rows and private consumers, and rejects exports of the deleted
power or top products. Both merged and separate duration interfaces,
the eight inherited bases with a joint positive-scale coordinate, and
compatible factor partitions are supported. The emitted-source closure
is checked; all remaining gates reach the output.

## 2. Strict scalar fields before any binary semantics

At a positive zero, every ordinary comparison holds and each integer
factor in every group is a unit. This follows directly from an all-SOS
finalizer or from an integer anchor times one plus a sum of squares,
minus one. In particular, the unchanged computed history scale and signed
repunit give

    P=H_U+H_V+ZUhat0+ZVhat0+ZVhat1+beta>=6,
    P=(b-1)J+epsilon_G, epsilon_G in{-1,+1}.          (2)

The selector hats give J>=0. Equations(2) exclude J=0 and imply

    J>=1, b<=P+2, J<=P/6.

Each history and product hat is below P. The exact lower blocks are those
of [history_scale257, Section2](neary_woods_universal_history_scale257.md):

    C=S0+P*S1+P^2*S2+P^3*S3,
    C_m=J(1+P+P^2+P^3),
    H_b=H_U+P*H_V+P^2*H_V,
    Z_b=Z_U+P*Z_V0+P^2*Z_V1,
    M_b=(b-1)((S1+S2)+P*S0+P^2*S1),
    H_r=H_U+P*H_V, R=(D-1)J, M_r=R(P+1),

    H0=H_b+P^3*C+P^7*H_r,
    M0=M_b+P^3*C_m+P^7*M_r,
    Z =Z_b+P^3*C+P^7*H_r.                            (3)

Here S_i>=0 sum to J, and all three unhat Z-products are nonnegative.
The [initial-bound proof, Section2](neary_woods_universal_initial_bound254.md)
checks these estimates even at D=1: R>=0 and
c_h R<(b-1)J<=P+1 imply R<P. The mask coefficients may be P+1, so
no mask-lane split is assumed. Instead

    H_b,Z_b<P^3, C<P^4, M_b<2P^3,
    C_m+2<P^4, H_r,M_r<P^2

prove the complete block bounds

    0<=H0,M0,Z<T.                                    (4)

For example M_b+P^3*C_m<P^7 absorbs the possible carry, and its
sum with P^7*M_r is below P^9. These bounds use only(2), positivity
and the fixed multiplier, not the sign of epsilon_G or an AND relation.

The new top tags in(1) now give the particularly simple integer margins

    H-Z>=T+1, M-Z>=1,
    Qhigh-H-M+Z>=(b-5)T+2>=2,                        (5)

as H<=3T-1 and M<=2T-1. Also all H,M,Z lie below Qhigh because b>=32.
The signed mask unit and low-port proof from the inherited compiler are
unchanged: 0<a0,b0,z0<q0 even before its sign is fixed. Therefore the
implicit native fields

    F0=q-A-Bport+Zport-1,
    F1=A-Zport, F2=Bport-Zport, F3=Zport              (6)

are strictly positive. The weaker M-Z>=1 suffices: F2 is at least
q0+b0-z0>0. Their sum is identically q-1 and their residues modulo16
are respectively1,4,2,8. Hence each field is below q and the packed
native index r satisfies q^3+q^2+q+1<=r<q^4.

The unchanged paid factoring is the exact identity

    V=A+1+(q+1)(Bport+(q-1)Zport),
    r=(q-1)V, X=q(V+native_bound_beta).              (7)

Since V>0, equation(7) gives X-r=V+q*native_bound_beta>0 before typing.
Thus changing the native scale has not lost the strict native bound.

## 3. Native signs, dyadic factors and the history repunit

Use the local dependency order in
[history_units260, Sections2--3](neary_woods_universal_history_units260.md)
and native_bound254, Section2. The relevant hypotheses have now been
proved explicitly: positive fields/checksum and padding residues, q>=16,
r>=4369, X>r, the positive odd multiplier in Y, both positive ratios and
the complete ordinary or normalized strong equation. Every norm sign is
+1 by the same congruences; rank and strict duplication recover the linear
sign. These implications do not assume any outer unit sign or that q has
the parent's former P^11 factorization.

At the provisional joint index r'=r+epsilon_j-1, the scalar population
argument gives q=2^popcount(r'). Once q is dyadic, the positive checksum
fields imply popcount(r)>=log2(q). The unchanged residue r=1 modulo16
gives

    popcount(r-2)=popcount(r)+v2(r-1)-2
                 >=log2(q)+2.

Thus epsilon_j=-1 is impossible. The full prescribed joined AND is
restored. In particular q is dyadic. Its **new** literal factorization is

    q=16*B_rec*S_rec*b*P^9.                          (8)

All factors in(8) are positive integers, so both history quantities b,P
are dyadic directly. This is the purpose of paying b inside the scale.
No reserved-lane test or history repunit sign is needed for this inference.
The factors B_rec,S_rec likewise recover exactly the same low recoder
powers as before. The paid loader congruence excludes the negative geometry
index by its old dn-1 population argument, and the recoder Mersenne
congruence excludes the negative mask sign. Neither argument depends on
the history exponent11.

Write b=2^v, with v>=5. If epsilon_G=-1 in(2), dyadic P=2^u would satisfy
2^u=-1 modulo2^v-1. Reducing u modulo v leaves one of1,2,...,2^(v-1),
all strictly below2^v-2. This contradiction proves

    epsilon_G=1, P=(b-1)J+1.

The usual repunit divisibility now gives P=b^t for a positive integer t.
Since c_h is a fixed power of two and b=c_h D, D is dyadic too.
This sign proof is shorter than the former top b AND(b-1) argument,
but it is used only after the scalar native theorem types(8).

The low scale q0 is dyadic and all low ports are below it, so the joined
AND first splits into the unchanged recoder relation and H AND M=Z.
Now T=P^9 is dyadic and(4) yields

    (H0+2T) AND(M0+T)=(H0 AND M0)+T*(2 AND1)
                    =H0 AND M0.                    (9)

Thus all unchanged lower controller, selected-product and range lanes
hold exactly. Their masks have coefficients below P after epsilon_G=1,
so the original per-lane conclusions are legitimate. In particular there
is exactly one actual tile per chronological row and both history digits
are in[0,D-1]. The upper transport sign, language-derived initial bound,
terminal bound and forbidden-zero-run exclusion of the negative lower
transport sign now follow literally from initial_bound254, Sections2--3.
They use only these lower-lane facts and the unchanged loader/transport
rows. This restores the actual input sentinel and the original physical
counter. The new scale does not modify the ordinary-input word language.

## 4. Complete positive extension and precise equivalence

At any new positive zero, Section3 recovers the complete unchanged outer
history and recoder relations, with every individual factor+1. Restore
the parent's old top ports bT,(b-1)T and old high scale P^11. Their lower
blocks still satisfy(4), and dyadic b gives b AND(b-1)=0, so the genuine
old prescribed AND holds. The complete native extension theorem supplies
fresh positive joint-native coordinates at that scale, including fresh
normalized strong coordinates where selected. The parent's paid bound
coordinate in(7) is positive at its canonical extension: X=2^(2r+1),
q<r and V=r/(q-1)<r imply X/q>V. Its divisibility is part of the same
canonical extension. All outer and geometry coordinates can be retained.
Every parent group is consequently1 and every retained comparison holds,
giving a positive254 zero and the actual accepted-input conclusion.

Conversely, start with any positive parent zero on a valid program/input
slice. It supplies the dyadic history scales, exact lower-block AND and
all genuine outer factors. Replace its top ports and native scale by(1).
Equation(9) proves the new AND, and(4)--(7) give its required scalar
margins. The same complete native extension theorem supplies positive
new joint coordinates, with the same positive canonical bound argument.
All outer and geometry coordinates remain fixed. Hence every accepted
ordinary input has a positive new extension, with the same fixed program
parameters. No extra duration padding or new input loader is required.

This is equality of the existential projections after forgetting the
private joint-native coordinates. It is not equality of the positive
zero sets on identical supplied native tuples. The eight strong/scale
bases retain their own auxiliary meanings; no cross-base tuple bijection
is asserted.

## 5. Exact arbitrary-point replay, counts and degree

The original254 and new253 polynomials generally differ off zero. For
an exact signed algebra audit, execute the old source with only these
four scalar-definition overrides:

    top_mask=2P^9,
    joined_H=H0+2P^9,
    joined_M=M0+P^9,
    native_q=q0*b*P^9.                              (10)

All unaffected inputs in(10) are computed from the old outer cone.
Every retained new register, comparison, factor, group and complete output
then agrees with that overridden old schedule. The checker also evaluates
the complete anchor/SOS formula independently from its residuals and group
products. Equation(10) is a changed-port replay identity, not equality to
the original polynomial or a free rescaling of its native witnesses.

The default certificate is252=132M+120A, and its one final subtraction
gives253=132M+121A. Both domain lists and all comparisons are unchanged.
The new q has propagated degree15 rather than16. The changed joint factor
bounds are168,404,93,220,76,76 instead of177,426,98,232,80,80. All other
factor bounds remain unchanged, so the total decreases by56 to1147.
Only the inherited guarded main-norm polynomial cancellation is used;
no on-zero equation lowers a degree. This is a conservative bound on the
emitted polynomial, not its exact degree or a circuit lower bound.

Run `python3 neary_woods_universal_product_scale253.py`; `--write` regenerates
the receipt. It covers the eight supported bases, both duration interfaces
and single-group plus anchored/SOS three-group schedules. This is a mapped
family with representative grouped schedules, not an exhaustive partition
optimization. Parent sources, proofs and receipts remain unchanged.

Author receipt generation and a separate fresh replay pass48 literal ledgers
and384 complete changed-port/register/factor/output identities,192 signed.
The receipt stores all16 canonical complete sources. Pretyping checks cover
1536 scalar contexts, including384 at height1,768 negative repunit signs
and1392 nondyadic cases. Another432 dyadic top-block identities compare the
old and new ports, and2496 modular cases exclude the negative repunit.
Forty-eight genuine affine histories with168 chronological rows are joined
to48 genuine low recoder outputs and checked against the new AND. Six
malformed or unsupported callers are rejected. These are algebra and outer
component checks, not materialized complete fixed-program U9 or Pell zeros.
Independent full proof/source/dependency review and two fresh replays pass
without findings. A separate executor checks384 complete changed-port register,
group and finalizer identities,192 signed, across all eight bases, both
interfaces and canonical or independent four-group schedules. Another1536
independent scalar block/field checks include768 negative-repunit and384
height-one cases;480 old/new top-bit identities and48 literal source closure,
domain and opcode checks also pass. The review checks local native sign
recovery before using the new dyadic scale factors.
