# A standalone Pell ordinate supplies the entire growth scale

## Status and exact semantic change

This is an independent ordinary mathematical audit of the proposed new direct-quartic source. It verifies the unbounded semantic change; it does not authenticate an emitted coefficient file or assert a newly compiled Lean/Rocq theorem. All variables mentioned as witnesses below range over the integers.

Retain the old cofinal even horizon

    t = 16 + 4 z^2,

and put d = 2^19. Delete the main shared-Pell request that formerly authenticated F=t^(2^20*t), together with its private growth-index pair, modulus and quotient when they have no other use. In their place introduce precisely three independent coordinates X,Z,u and retain F as the existing front coordinate. Impose

    Z = t F,
    X^2 - 16 Z^2 - 8 Z F = 1,
    F = d*t*(2u+1).                                    (G)

Every row has total degree at most two. The second row becomes

    X^2 - ((4t+1)^2-1) F^2 = 1.

No exponentiation occurs in these literal equations. Initially F is signed. Its positivity is recovered only after the remaining shared-Pell certificates are oriented and certain front powers are interpreted.

The new radix definition is

    D = 2(C+F+1),    q = D^x,                             (R)

where C is the existing actual CRT row-index representative, explicitly even, and the displayed power is enforced by the retained polynomial certificate. The old divisibility row is retained:

    B eta = C+F+1.                                       (I)

The previous H=2+4(sum of actual representatives) definition is deleted. All remaining main-Pell pairs, the C anchor, the full orientation row, beta endpoints, range-binomial predicates, and every needed frame atom must remain correctly bound in the emitted source. In particular the existing request with exponent F+t must remain.

## 1. Elementary Pell facts used

For integer a>=2 define X_n(a),Y_n(a) by

    X_0=1, Y_0=0,
    X_(n+1)=a X_n+(a^2-1)Y_n,
    Y_(n+1)=X_n+aY_n.

The positive generator of the integer Pell group for discriminant a^2-1 is a+sqrt(a^2-1): an integral positive ordinate is at least one and the pair (a,1) exists. Consequently every integer solution of X^2-(a^2-1)Y^2=1 with Y nonzero has

    |X|=X_n(a), |Y|=Y_n(a)

for a unique positive n. This is the standard unbounded Pell classification, also an inherited theorem of the source project. The new uses below are elementary consequences of the displayed recurrence.

At a=1 the polynomial recurrence gives X_n(1)=1 and Y_n(1)=n. Therefore

    Y_n(a) = n modulo a-1.                               (1)

If a is odd, every X_n(a) is odd, and Y_n(a) is odd exactly when n is odd. The duplication identity

    Y_(2m)(a)=2 X_m(a)Y_m(a)

then proves

    v_2(Y_n(a))=v_2(n),    n>=1, a odd.                   (2)

Indeed write n=2^r s with s odd: Y_s is odd, and each doubling adds exactly one factor of two because each X_(2^j s) is odd.

The sequence Y_n is strictly increasing for a>=2. Its second-order recurrence yields

    Y_(n+1)=2aY_n-Y_(n-1) >= (2a-1)Y_n,

and hence

    Y_n(a) >= (2a-1)^(n-1),    n>=1.                      (3)

## 2. A sharper constructor majorant and sign-free growth

The square-shell syntax constructors are

    I(a,b)=2((a+b)^2+a),  M(a,b)=I(a,b)+1,
    A(a,b)=2((a+b)^2+3a+4b+3), E(a,b)=A(a,b)+1.

For integer arguments 0<=u,v<=M0, all four constructor outputs are at most E(M0,M0), and

    E(M0,M0)+1 = 8M0^2+14M0+8 <= 8(M0+1)^2.              (4)

Each local parameter is strictly below t. Constants zero and one are also below t. Consequently the value of every depth-zero leaf plus one is at most t. Define

    H_0=t, H_(r+1)=8H_r^2.

Induction using (4) shows that every constructor tree of depth r has value plus one at most

    H_r = 8^(2^r-1) t^(2^r).

The independently authenticated source has maximum constructor depth 19. Therefore every local label is strictly below

    L = 8^(d-1) t^d,    d=2^19.                           (5)

This replaces the old coarser exponent-2^20 majorant. It uses the same actual syntax trees and does not change the underlying calculus.

In (G), t>=16 is positive and even. The last row makes F nonzero. Pell classification at a=4t+1 (an odd integer) gives a positive n with

    |F|=Y_n(4t+1).

Because d is divisible by four, 4t divides F. Equation (1) gives 4t|n. Equation (2) and the odd multiplier in (G) give

    v_2(n)=v_2(F)=19+v_2(t).

Thus n/(4t) is a positive integer of exact 2-adic valuation 17, and

    n >= d*t.                                           (6)

By (3),

    |F| >= (8t+1)^(n-1)
         >= (8t)^(d*t-1)
         >= L^t.                                        (7)

For the last inequality, substitute (5): the ratio of (8t)^(d*t-1) to L^t is exactly 8^(t-1)/t, which is at least one for every positive integer t. In particular L>=t, so |F|>=t^t>t, and F is even, before any semantic sign recovery. Once F is shown positive, (7) supplies the sharp product-separation hypothesis F>=L^t with the new majorant (5).

## 3. The main shared Pell certificates remain noncircular

The C-anchor proof does not assume any sign of F or of the other front atoms. Its square frame includes the actual signed bases, exponents and proposed outputs of all retained requests, including F+t. Removing the old growth-index pair only decreases the number of pairs in the cap and orientation sum.

The independent standalone Pell variables X,Z,u are not requested main-frame atoms and need not be bounded by that frame. The existing F atom remains included wherever the unchanged frame interface requires it. The C-anchor classification, cap, and orientation arguments therefore recover every retained principal pair at its canonical signed nominal index before applying any front arithmetic. No use of (7) is needed for this index recovery except its separately proved elementary sign-free conclusions when interpreting the new front.

## 4. Signed front bootstrap with the collapsed radix

All equalities involving powers in this section mean the outputs of the unchanged signed exact-power certificates. For a base with absolute value at least two, those certificates exclude a negative requested exponent and return the genuine integer power. The canonical-index theorem is already available from Section 3.

Retain the beta equations

    y = F(2v+1),
    x = F+1+(y+1)r_0,
    x = 1+[1+(t+1)y]r_t.                                 (8)

Initially |y|>=|F|>t. Since both C and F are even, C+F+1 is odd and nonzero. Thus D=2(C+F+1) is even and |D|>=2. The request q=D^x forces x>=0.

If x=0, the last equation of (8) says that 1+(t+1)y divides -1. This is impossible because |y|>=|F| and

    |1+(t+1)y| >= (t+1)|y|-1 > 1.

Hence x>=1 and |q|>=2. The retained request with base q and exponent y+1 gives y+1>=0. A negative y would satisfy y<=-|F|<-1, so it is impossible. Therefore

    y >= |F| > 0.                                       (7)

If x=1, the first endpoint in (8) gives

    -F = (y+1)r_0.

But 0<|F|<=y<y+1, so a nonzero F cannot be divisible by y+1. Consequently x>=2. The last endpoint now has a positive multiplier 1+(t+1)y and left side x-1>0, so r_t>=1 and

    x >= 2+(t+1)y.                                      (9)

In particular |q|>=2^x>=4 and |q+1|>=3. Every retained base-(q+1) request is now interpretable. These include all independent CRT representatives, C itself, and the exponent F+t. They force those actual indices to be nonnegative, including

    F+t >= 0.

Together with |F|>t, this excludes the negative sign of F. Thus F>0, y>=F and the full growth inequality (7) holds for F itself. The C-anchor has already excluded C=0, so the new nonnegativity of C gives C>0.

The first endpoint now has its usual positive interpretation. If r_0<=-1 then x<=F-y<=0, contrary to x>=2. Hence r_0>=0 and x>=F+1. The complete established order is:

    |F| large and even;
    D nonzero and even;
    x>=1;
    y>=|F|;
    x>=2 and x>=2+(t+1)y;
    all q+1 indices nonnegative;
    F>0 and C>0;
    D>0 and q>0.

No postponed sign is used as a premise for itself.

## 5. One uniform coefficient bound validates the smaller radix

Once every retained principal pair is canonical, the C cap makes every other classified index strictly smaller than C. All relevant indices are now nonnegative. Thus the first binomial upper argument F+t is below C, each ordinary range-binomial upper representative is at most C, and C itself is the only anchored boundary value. The lower indices used by the range predicates are among t, y+1 and x; (9) puts all of them at most x.

From (R) and F>0,

    D=2(C+F+1)>2C>0,
    q=D^x>(2C)^x.

For every binomial coefficient needed by any digit extraction, including the initial coefficient B, write its upper argument as A0 with 0<=A0<=C, and its degree as 0<=j<=k<=x. Then

    0 <= binom(A0,j) <= max(1,A0)^k <= C^x < q/2^x.        (10)

Here C>t>=16, so C>=1 and the j=0 case is included. The common normalized remainder bound still supplies |r|<=L0/2 for each relevant denominator L0=q^k. By the elementary geometric-series estimate, the genuine low tail has magnitude less than

    (C^x/(q-1))*q^k < q^k/32,

since x>=F+1 is much larger than six and q/(q-1)<2. Thus a candidate and its canonical low tail that are congruent modulo q^k have difference of magnitude below q^k and must be equal. The unchanged digit equations then authenticate every range binomial.

For the first digit, the candidate B is also bounded before it is interpreted. From (I), eta is a nonzero integer, so

    |B| <= C+F+1 = D/2 < q/2.

The true binomial coefficient is positive and less than q/32 by (10). Their congruence modulo q therefore implies exact equality

    B=binom(F+t,t)>0.

Finally B|D follows directly from (I), giving N=B^x | q=D^x after the retained request N=B^x is interpreted. The original role of H is completely replaced by the actual C cap and this divisibility. The new radix has the same parity class D=2 modulo 4 because C+F+1 is odd.

## 6. A normalized Pell permutation modulo every power of two

This elementary lemma supplies the missing cofinal completeness condition.

**Lemma.** If a is an integer with a=1 modulo 4, then for every r>=1 the function s -> Y_s(a), restricted to nonnegative indices, induces a permutation of the residue classes modulo 2^r. In particular every odd residue is attained by an odd index, and that index may be chosen arbitrarily large in a fixed residue class.

**Proof.** All X_s(a) are odd and X_s(a)=1 modulo 4. Modulo two, Y_s(a)=s. For h=2^r, (2) gives v_2(Y_h)=r. The norm identity and a^2-1 divisible by eight give

    v_2(X_h^2-1)>=2r+3.

Since X_h=1 modulo 4, X_h+1 has exact valuation one. Therefore

    X_h=1 modulo 2^(2r+2).

The addition formula yields, for every nonnegative s,

    Y_(s+h)-Y_s = (X_h-1)Y_s + X_sY_h
                = 2^r modulo 2^(r+1).                  (11)

The first term vanishes modulo 2^(r+1), and the second has exact valuation r. Thus the two lifts s and s+2^r of an index class modulo 2^r produce the two distinct output lifts modulo 2^(r+1). Induction from modulo two proves bijectivity. The same congruence shows periodicity modulo 2^r. Adding positive multiples of 2^r supplies cofinal positive indices in any selected class. QED.

The lemma uses only the recurrence, Pell norm and elementary 2-adic valuations. No analytic 2-adic inverse theorem is assumed.

## 7. Choosing F so the binomial selector is odd

For completeness, start with a finite refutation. The horizon must exceed its finite length and local schema parameters. It suffices to choose the original horizon parameter z to be divisible by 2^12. These horizons remain cofinal, and satisfy

    t=16+4z^2 = 16 modulo 2^26.

Therefore v_2(t)=4 and the binary digit of t at position 23 is zero.

Set

    n_0=d*t,
    y_0=Y_(n_0)(4t+1),
    a_0=X_(n_0)(4t+1).

By (1), t|y_0; by (2), v_2(y_0)=23. Consequently

    b_0 = y_0/(d*t)

is an odd integer. Also a_0=1 modulo 4. This follows, for example, because n_0 is even and X_(2m)=2X_m^2-1 with X_m odd.

Choose any integer L with L>26 and 2^L>t. Put R=L-23. Since t/16 and b_0 are odd, they are invertible modulo 2^R. The lemma gives a positive odd index s satisfying

    (t/16)*b_0*Y_s(a_0) = 1 modulo 2^R.                 (12)

The same s can be chosen arbitrarily large by adding multiples of 2^R. Define

    n=n_0*s,
    F=Y_n(4t+1)=y_0 Y_s(a_0),
    X=X_n(4t+1), Z=tF,
    u=(F/(d*t)-1)/2.

Composition gives the displayed F identity, and (12) ensures

    F = 2^23 modulo 2^L.                                (13)

The quotient F/(d*t)=b_0Y_s(a_0) is odd, so u is an integer. Every row of (G) is satisfied. These choices give arbitrarily large positive F at each allowed horizon; no circular dependence on later beta or CRT parameters has been introduced.

Because t<2^L and its bit 23 is zero, (13) says that the binary supports of F and t are disjoint. Their addition has no binary carries. The elementary parity criterion for binomial coefficients therefore gives

    binom(F+t,t) is odd.                                (14)

For completeness, the criterion follows from v_2(m!)=m-s_2(m):

    v_2 binom(F+t,t)=s_2(F)+s_2(t)-s_2(F+t).

Disjoint binary supports make the right side zero. Hence B and N=B^x are odd, which is exactly the parity needed by the subsequent CRT representative and even-anchor construction.

## 8. Beta spacing does not require the full factorial divisibility

The new F has a fixed 2-adic valuation in the completeness construction, so it is essential not to retain an unjustified assertion that t! divides F times an odd number for arbitrary t. That stronger divisibility is unnecessary.

Choose an arbitrarily large positive odd multiplier w divisible by every odd prime at most t, and put y=Fw. Then every prime at most t divides y, because F is even. For 1<=i<j<=t+1, any common prime divisor p of

    1+i y,  1+j y

is coprime to y and divides (j-i)y, hence divides j-i. Thus p<=t, but every such prime divides y, a contradiction. The beta moduli are pairwise coprime. Choosing w sufficiently large also makes y exceed F and every finitely many pending-multiset state value. It has the required form y=F(2v+1).

Finite CRT now supplies an arbitrarily large positive beta code x with the correct endpoints and local states. The quotient ranges remain strict by the unchanged positive-denominator argument.

After x is fixed, set B=binom(F+t,t) and N=B^x. The generalized factorial-free binomial-CRT theorem applies because (7) implies F>=t^t>=lcm(1,...,t)^2. It assigns all independent representatives at precision N^2. Since N is odd, choose the eight other representatives positive first, then choose C even, positive, in its prescribed residue class modulo N^2, and larger than every other actual exponent and representative. The retained selector congruence gives B|C+F+1. Set D=2(C+F+1) and q=D^x only after this choice. Then B|D, N|q, D>2C, and D=2 modulo 4. All digit estimates in Section 5 hold for these actual values.

Construct the main frame and positive canonical principal pairs last. The C anchor, its cap slack, orientation quotient and odd auxiliary witnesses are completed exactly by the inherited cofinal-anchor construction, with one fewer principal pair. All remaining normalized remainders meet the old common bound. This supplies every new or retained witness from a finite refutation.

## 9. Conclusion and proof boundary

Soundness recovers positive F with the sharper label-separation budget (5)--(7), the exact binomial selector and all range digits, coherent positive beta states, and a finite C222 refutation. Completeness constructs a zero from every finite C222 refutation using Sections 6--8. Composing with the identified inherited C222/ZF/ZFC calibration proves in ordinary mathematics formalizable in ZFC that the new literal system has an integer solution exactly when a finite ZFC refutation exists. Negation gives the requested consistency equivalence.

The new proof does not assume either consistency or inconsistency. It proves neither. The new unbounded arguments are the standalone growth certificate, the delayed sign bootstrap, normalized Pell residue surjectivity, and the squarefree beta-spacing construction. The main shared-Pell canonical-index theorem, generalized binomial CRT theorem, local finite-calculus encoding and logical calibration remain explicitly inherited. Exact source deletion, frame/cap/orientation edits, integer projection identities, and coefficient counts still require the independent emitted-artifact check.
