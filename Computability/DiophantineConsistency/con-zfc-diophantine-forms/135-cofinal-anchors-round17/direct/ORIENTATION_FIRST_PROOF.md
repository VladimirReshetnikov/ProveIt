# Recovering nonnegative arithmetic from signed Pell orientation

This proof extends `PROOF_315.md`, whose signed-center frame, squared semantic anchor, odd auxiliary construction, literal compiler and inherited calibration boundary are retained. The changed sign proof below replaces its front-sign schedule. It is not a claim that the old shifted representative coordinates become nonnegative. The proof applies to `orientation_first`, `orientation_separate` and `orientation_groups5`; their centered endpoints are `integer285`, `integer286` and `integer290`.

The exact centered metrics are respectively (variables, rows, monomials, height) = (285,194,6594,128446), (286,195,5770,128446), and (290,199,4949,128446). Each polynomial is a fully materialized degree-four sum of squares over unrestricted integer variables. These are finite achieved constructions, not minimality claims.

## The hypotheses available before any semantic arithmetic

Retain only the factorial remainder and slack scalar graphs r>=0,s>=0, and the exact-binomial output slack scalar graph o>=0. The cofinal horizon remains t=16+h0^2. The literal rows give B=r+s+1>=1 and q=B+o+1>=2. Neither x, the nine shifted representatives, the frame center A, nor any proposed power output is assumed nonnegative.

Let a_i be the actual nine representatives, each equal to its stored coordinate plus one. They are unrestricted at this stage. Let h be the literal derived-label expression, also unrestricted. The square frame still contains every base, exponent and output atom; in particular |h|<W and every requested |k_i|<W. It gives W>=258 and, from the odd frame norm, a=|A|>W^W and |A-1|>4W^3. These statements use squares of signed atoms, not the postponed signs.

## A signed nominal index in the squared anchor

The exact anchor equations and odd auxiliary multiplier are those in `PROOF_315.md`, but do not presume h>0. The squared cap gives |C|>|h| and C!=0. Classification and squared divisibility give positive indices i,l with |C|=Y_i(a), |J|=Y_l(a), i<=l and |C| dividing l. The two comparison residues imply i=+/-h modulo 2|C|.

If h=0, this is impossible for 1<=i<=|C|. If h!=0, |h|<|C| implies i=|h|. Thus h!=0 and

    |C|=Y_|h|(a).

For every other principal pair the cap gives |y_i|<|C|, hence j_i<|h|<W; the anchor has j=|h|<W. This is the complete, noncircular bound on all classified indices. It does not use any monotonicity property of the signed derived-label expression. In fact |h|=1 is also excluded by |C|>|h|, but that extra fact is not needed until h is oriented.

## Both coordinate signs from bounded errors

Replace ordinate-only pooling by

    sum_i [(x_i-1)^2+(y_i-k_i)^2]=(A-1)Q,                  (1)

including the anchor pair. Q is an unrestricted integer. The separate-pool endpoint instead has one row for all abscissa errors and one for all ordinate errors. The grouped endpoint partitions the fifteen pairs into blocks of five, and uses one abscissa and one ordinate row for each block. The proof below applies to each such row separately.

At A>0, a classified pair x_i=sigma_i X_j(a), y_i=epsilon_i Y_j(a) reduces modulo A-1 to (sigma_i,epsilon_i*j). At A<0, a=-A is congruent to -1 modulo A-1, so it reduces to (sigma_i*(-1)^j,epsilon_i*(-1)^(j-1)*j). The ordinate residue is zero at j=0. Call these small residues s_i and r_i.

Each row therefore makes A-1 divide a nonnegative sum of its errors (s_i-1)^2 and/or (r_i-k_i)^2. Here |s_i-1|<=2, |r_i-k_i|<2W, and the total number of pairs is m=15. The full sum satisfies

    0<=E<4mW^2+4m<4W^3<|A-1|,

where W>=258. Hence every error vanishes. For either sign of A this says exactly

    x_i=X_(k_i)(A),       y_i=Y_(k_i)(A),

with X_(-k)=X_k and Y_(-k)=-Y_k. In particular negative A does not imply that x_i is positive: it is the correct Pell polynomial at the original signed center.

## Negative requested exponents are impossible at a positive base

Let a genuine power request have 2<=n<W, signed requested index |k|<W and signed output |m|<W. Its polynomial modulus is T=2An-n^2-1. Since |A|>W^W,

    |T|>W^W+W.

The canonical signed Pell polynomials satisfy the usual power congruence. If k>=0, it gives m=n^k modulo T. Both quantities have absolute difference below |T|, so m=n^k, including k=0 and m=1.

If k=-j<0, the recurrence at -j is the inverse unit. Multiplication by the positive-index congruence gives

    m*n^j=1 modulo T.

Equivalently gcd(n,T)=1 because T=-1 modulo n, so this inverse is legitimate. Since |m*n^j-1|<W^W+1<|T|, equality m*n^j=1 would follow. This is impossible over the integers for n>=2,j>=1. Consequently every such power request itself forces k>=0 and supplies its exact nonnegative power output. No sign of m or of k was used as a premise.

For n=1 and a known nonnegative k, the same canonical congruence directly gives m=1. This handles the possible initial F=0 case without a wrong-abscissa exception, because both coordinates are already oriented by (1).

## The complete acyclic recovery schedule

1. The initial q>=2 and t>=16 interpret q^t. The common t pair is already canonical. Apply its other request with base F^2+1>=1 to obtain V0=(F^2+1)^t>=1.

2. The raw ceiling identity is F*B=V0+s, with B>=1 and s>=0. Hence F>=1. Also F*B>=V0>=F^2+1, so B>F and B>=2. Therefore q>=3. The cofinal beta value y=V0(V0-1) satisfies y>F+2; this follows immediately for F=1 from t>=16, and for F>=2 from V0=(F^2+1)^t.

3. The request with base q and exponent x+1 now forces x+1>=0, so x>=-1. The first endpoint row is

       x=F+1+(y+1)u0.

   If u0<=-1 then x<=F-y<-2, a contradiction. Thus u0>=0 and x>=F+1>=2. The last endpoint row is

       x=1+[1+(t+1)y]ut.

   Its positive coefficient and x>=2 force ut>=1, giving x>=2+(t+1)y. These conclusions precede the factorial interpretation.

4. Every actual independent representative a_i is the exponent of a request at base q+1>=4. Each is therefore nonnegative, and each numerator request is exact, even if a_i=0. The same argument gives h>=0 for the anchor request. Since the anchor already excluded h=0, it is positive. The ordinary monotone syntax interpretation of h is now available.

5. K=2(2+t+x+y+F)>0. The requests at B and B*H0, where H0=1+sum a_i>=1, give N=B^K and q=(B*H0)^K. Every remaining request is exact by the same canonical power lemma; all eighteen requested powers have been recovered. The derived t+1 pair is still the unchanged one-step Pell addition from the canonical t pair.

6. Each of the eleven delayed remainder pairs satisfies r_i+s_i=L_i-1>=0, because its denominator L_i is now a positive exact q-power. Its retained product graph r_i*s_i>=0 implies both signs. The corresponding quotient signs follow from their bounded remainders and positive divisors. The output slack o was already retained. These deductions do not justify an earlier power step; they are explicitly later.

7. The ceiling gives V0<=B*F<B^2. Since K>=2 and H0>=1, q>=B^2>V0. Thus the unchanged factorial digit is exact: B=binom(F^2+t,t). The inherited square-output fixed-point proof for t>=16 now yields F=t! and identifies B as the product of the pairwise coprime d_i=1+F^2/i.

This order uses no sign graph or arithmetic meaning that it is attempting to establish.

## Zero representatives and the precise semantic boundary

The shifted stored coordinate a_i-1 can now equal -1. Therefore it would be false to claim that an arbitrary zero restores every variable of the old natural source pointwise. Instead we have recovered the actual semantic CRT representatives a_i>=0. These are the upper arguments in the range-binomial conditions and the inputs to the arithmetic source. Nonnegative, not strictly positive, upper arguments are sufficient for the inherited range-decoding proof.

For n=0 and k>=1, binom(0,k)=0. The positive-degree coefficients vanish, while the constant coefficient is one. All congruence and prime-power loss arguments remain valid: no step divides by n or assumes n>=k. The range condition still recovers local parameters in the required nonnegative interval. Their constructor and Horn polynomials are then evaluated on nonnegative local values exactly as before. The precision and unit-weight flow argument are unchanged, so a finite refutation is recovered even if some global representative is zero.

The radix bounds need one explicit repair. Let C0 be the encoded index representative, distinct from the private cap ordinate C. After the factorial interpretation, the retained congruence is

    B divides C0+F^2+1.

Because t>=16, the product B=(F^2+1) product_(i=2)^t(1+F^2/i) is strictly greater than F^2+1. Thus C0=0 is impossible and C0>=1. Consequently H0=1+sum a_i>=2.

For every ordinary upper representative a>=0 and every coefficient needed through a positive lower index k, use

    binom(a,j)<=max(1,a)^k<=H0^k<q,

rather than the invalid bound a^k at a=j=0. For the derived label let n=max(a,b,c,d), and n*=max(1,n). The inherited positive-input degree ledger gives h<=(n*+1)^ell, with ell=4194304. Because C0>=1 is a separate representative, H0>=n+2 and hence n*+1<=H0. Thus h<=H0^ell. The existing t!, K and ell inequalities still give all required derived-label coefficients below H0^K<=q. No extra sign or nonzero premise is hidden in this repair.

The local source is interpreted on the decoded nonnegative values, not on the old shifted global coordinates. The ordinary C222/refutation calibration therefore applies. This establishes the soundness direction without a claim of pointwise restoration to the old natural private or shifted representation.

## Completeness and exact audit

Completeness is unchanged from `PROOF_315.md`: start with a finite refutation, choose all actual CRT representatives positive, choose the dominant a representative with parity opposite b, obtain an even semantic anchor h, and construct the positive canonical frame and all private witnesses. Every abscissa error X_k(A)-1 and ordinate error Y_k(A)-k is divisible by A-1. Thus (1), its separated version, or every grouped row has an integer quotient. Removing ten sign graphs only removes constraints that these canonical witnesses already satisfied. The squared-cap and odd-auxiliary completeness arguments remain fully constructive.

The independent literal checker reconstructs the precise pool partitions, source deletion boundaries, every remaining sign graph, all power atoms, complete factorization, integral monic projection, translations and collected quartic coefficients. It is run normally and under -O. The independent mathematical review separately checks the unbounded signed-anchor and orientation-first arguments. These finite checks do not prove consistency or replace the inherited logical calibration. Together with that calibration, the two directions establish in ZFC that no integer zero exists exactly when Con(ZFC).
