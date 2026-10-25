# Reusing a semantic Pell anchor over unrestricted integers

## Result and scope

The selected exact equation is the sum of the squares of the 204 quadratic residuals in `integer315/equation.json`. Its 315 variables range over all integers. Its separately materialized collected polynomial has degree four, 5709 nonzero monomials and coefficient height 128446. The conservative comparison `integer321` has 321 variables, 206 rows, 5785 monomials and the same height. These are literal finite counts, not global minimality claims.

The input is precisely the round16 direct portable source. The two input files are bound by SHA256 in the independent checker. All eighteen power requests, the square-output factorial fixed point, the cofinal horizon, the self-sized radix, the range tests and the finite Horn-refutation calibration are unchanged. The inherited semantic boundary is the ordinary interpretation associated with `KEndpoint.c222_iff_zf_refutation` and `ConstructibleChoice.zf_refutation_iff_zfc_refutation`. We do not claim a new end-to-end proof-assistant certificate or a proof of consistency. The result is an ordinary mathematical proof, formalizable in ZFC, that integer solvability is equivalent to the existence of a finite ZFC refutation.

The round16 `direct/PROOF.md` supplies the complete arithmetic-front argument. This note gives the replacement private Pell certificate, its full sign schedule, and the changed completeness choice. In particular it does not silently treat a signed private coordinate as a natural one.

## Shared notation and unchanged front

Write X_j(a), Y_j(a) for the Pell polynomials defined by X_0=1, Y_0=0 and

    X_(j+1)=a X_j+(a^2-1)Y_j,
    Y_(j+1)=X_j+aY_j.

For j>0 extend to negative indices by X_(-j)=X_j and Y_(-j)=-Y_j. For negative centers,

    X_j(-a)=(-1)^j X_j(a),
    Y_j(-a)=(-1)^(j-1)Y_j(a)  (j>0).

The unchanged square frame W=2+sum(atom^2) includes every actual affine base, exponent and output atom of all eighteen requests. Thus W>=258, |atom|<W, atom^2<W, and every requested absolute index is less than W. The fifteen principal pairs include the already needed derived-label pair. Its requested index is denoted h; literally h=1+add.380. It is a monotone syntax-constructor expression in the four positive CRT representatives, so h>=2 before interpreting any power.

The unchanged odd frame is

    A^2-W^3(W+2)(2z+1)^2=1.

No sign graph is retained on A. Put a=|A|. Classification at center W+1, with ordinate |W(2z+1)|, gives a=X_l(W+1), with positive l divisible by W. Hence

    a>=X_W(W+1)>W^W,       |A-1|>4W^3.

This argument uses neither a power output's sign nor a binomial interpretation.

## The reused signed anchor

Reuse the derived-label seed pair (U,C), including its original norm and A*C multiplication gate. No fresh duplicate anchor norm is created. Retain one auxiliary pair (H,J), one comparison pair (S,R), and a comparison center D, with

    U^2-(A^2-1)C^2=1,
    H^2-(A^2-1)J^2=1,
    S^2-(D^2-1)R^2=1,
    J=C^2(2e+1),
    D=1+4J(2d+1),
    D=A+Hf,       S=U+Hg,       R=h+4Cq.

Every displayed coordinate is an unrestricted integer. The squared cap is

    C^2=h^2+1+sum_(i not anchor) y_i^2+u^2+v^2+w(w+1).       (1)

The ternary form is always nonnegative. Therefore |C|>h, so C is nonzero. The odd auxiliary factor gives J nonzero and C^2 divides J. Consequently |H|>=a and |D|>=3. D is congruent to 1 modulo 4C even when C, J or D is negative.

Classify the anchor and auxiliary pairs at a:

    |U|=X_i(a), |C|=Y_i(a), |H|=X_l(a), |J|=Y_l(a).

Here i,l>0. The inherited squared-divisibility Pell lemma gives i<=l and |C| divides l. Polynomial transfer through D=A modulo H and S=U modulo H gives comparison index j=+/-i modulo 2l. For A<0, the additional factor (-1)^j in X_j(A) is absorbed by the independent abscissa sign. At D=1 modulo 4C, the ordinate recurrence gives j=+/-h modulo 4|C|. Hence i=+/-h modulo 2|C|. Since 1<=i<=|C| and 0<h<|C|, only i=h is possible. Thus

    |C|=Y_h(a).

The proof uses the absolute values of the signed anchor and auxiliary ordinates. In particular neither C>0 nor J>0 is an implicit assumption.

## Pooled signed-index recovery including the anchor

For every other principal pair, (1) gives |y_i|<|C|, hence its classified index satisfies j_i<h<W. For the anchor itself j=h<W. Retain all fifteen terms in the single pooled row, including the anchor term:

    sum_i (y_i-k_i)^2=(A-1)q0.                              (2)

The free quotient q0 has no sign graph. If A>0, reducing the recurrence modulo A-1 yields y_i=epsilon_i j_i. If A<0, a=-A is congruent to -1 modulo A-1 and yields y_i=epsilon_i(-1)^(j_i-1)j_i; at j_i=0 the residue is zero. Thus (A-1) divides the nonnegative integer

    E=sum_i (r_i-k_i)^2,

where r_i is the indicated signed integer index. Since all j_i<W, |k_i|<W and the fifteen pairs are fewer than W,

    0<=E<4*15*W^2<4W^3<|A-1|.

Therefore E=0 and y_i=Y_(k_i)(A) for every pair. Keeping the anchor's pooled term is essential: for an even h and a negative A its correct ordinate is negative. A positive linear cap combined with anchor reuse would not justify this signed-center variant.

## Powers and the acyclic front-sign schedule

For any positive requested index k<W, base 2<=n<W, and signed candidate output |m|<W, put T=2An-n^2-1. Its magnitude exceeds W^W+W. Once y=Y_k(A), the two possible norm abscissas are +/-X_k(A). The correct choice gives m=n^k modulo T. The wrong choice gives m*n^k=-1 modulo T, by multiplying the two conjugate recurrence expressions; this identity holds for either sign of A. Since |m*n^k+1|<W^W+1<|T|, the wrong case would imply the impossible equality m*n^k=-1. The correct congruence similarly gives m=n^k. For base one, the already oriented t pair gives the result directly.

The retained front signs are exactly those of round16 except for A. Initially x>=0, all nine encoded representatives minus one are nonnegative, the factorial remainder and slack are nonnegative, and the exact-binomial output slack is nonnegative. Therefore B=r+s+1>=1, q=B+o+1>=2 and t=16+h0^2>=16. First apply the signed-center power argument to q^t. This orients the t abscissa to X_t(A), not necessarily to a positive number. The same pair gives V0=(F^2+1)^t. The raw ceiling identity FB=V0+s>0 gives F>=1, and then B>=2, q>=3 and y=V0(V0-1)>=F+1. Thus K=2(2+t+x+y+F)>0. All representative indices are positive, and so is the derived-label index. The B^K request gives N, its shared pair gives q=(B H0)^K, and all remaining q or q+1 requests follow. This is the same acyclic order as round16.

Only after the power interpretations are established do the eleven product guards r_i*s_i>=0 combine with the positive denominator equations r_i+s_i=L_i-1>=0 to give both signs. The factorial fixed point, all range tests and Horn decoding then proceed exactly as in round16. Signed A changes no semantic front value. Private Pell quotient signs need not become natural: if comparison with the older all-natural private representation is wanted, reconstruct its witnesses afresh at a positive center.

## Cofinal semantic-anchor completeness

Begin with a finite refutation and perform the round16 cofinal horizon and beta-CRT construction. It fixes t,F,V0,y,x,B,K,N before the independent representatives. Since t>=16 and F=t!, each d_i=1+F^2/i is odd, so N and N^2 are odd. The representative moduli multiply to N^2.

Choose the ordinary positive representatives in their required residue classes with 0<a_i<=2N^2, prescribing parity by adding N^2 when needed. For the dominant a representative, start with its least nonnegative residue a0 in [0,N^2), and choose a=a0+2N^2 or a0+3N^2 to have parity opposite to b. Then 2N^2<=a<4N^2. The literal monotone derived-label constructor gives h>=2a^2, and its parity is h=1+a+b modulo 2. Thus h is even and exceeds every other requested index, indeed it can be chosen to exceed twice their maximum. The inherited fixed-front bounds are far below N^2. The self-sized radix H0=1+sum representatives is chosen only afterward, so q=(B H0)^K still dominates all required binomial coefficients; no new circular modulus choice is introduced. The factor-of-four increase in the representatives is harmless because the radix uses their actual values rather than an old aggregate ceiling.

Form the actual square frame, choose A=X_W(W+1)>0 and the ordinary odd frame witness, and use canonical principal pairs. Set U=X_h(A), C=Y_h(A). If M=max_(i not anchor) k_i<h, then Y_M(A)<=Y_(h-1)(A). Recurrence gives C>(2A-1)Y_(h-1)(A). As A>W^W, h<W and the number of other pairs is 14,

    C^2-sum_(i not anchor)Y_(k_i)(A)^2
      >[(2A-1)^2-14]Y_(h-1)(A)^2>h^2+1.

Thus the slack in (1) is nonnegative and has a ternary representation. Every term in (2) is divisible by A-1, so its free quotient exists.

To construct the odd auxiliary quotient explicitly, use h even. Then C=Y_h(A) is even and U=X_h(A) is odd. Choose the common index l=hC, and let H=X_l(A), J=Y_l(A). Composition gives J=C*Y_C(U). The binomial Pell-polynomial expansion gives

    Y_C(U)=C U^(C-1) modulo C^2,

because U^2-1=(A^2-1)C^2. Thus J/C^2 is an integer congruent to U^(C-1) modulo C, so it is odd. Set e=(J/C^2-1)/2. Also H is odd and the Pell norm gives gcd(H,J)=1, hence gcd(H,8J)=1. CRT chooses D>=2 with D=A modulo H and D=1+4J modulo 8J. Set d=(D-1-4J)/(8J), S=X_h(D), R=Y_h(D), and fill the three congruence quotients. This supplies every anchor witness without an e sign graph.

The elementary universal representation n=u^2+v^2+w(w+1) for every n>=0 fills all retained guards. The old arithmetic front and every genuine power request are unchanged. Hence each finite refutation extends to a zero of the exact new system.

## Literal compilation and audit boundary

The emitted source records reused anchor coordinates and index, the signed-center flag, squared-anchor flag, odd auxiliary coefficient, every source edit, all frame atoms, every guard and all original power requests. The independent checker does not import the producing compiler. It reconstructs the complete source, checks the exact guard identities and their noncircular sign dependencies, replays Horn factorization and every integral monic restoration, composes integral translations, and independently collects every quartic coefficient. It runs both normally and under Python -O. Deliberate malformed source, frame, guard, factorization, restoration, translation and polynomial controls are rejected.

These finite checks certify the actual finite polynomial and its exact algebraic transformations. They do not replace the unbounded Pell, CRT, factorial, Horn-flow and logical-calibration arguments. Those arguments establish both directions without an assumption of consistency. Negating the solvability statement proves, in ZFC, that this polynomial has no integer zero if and only if Con(ZFC).
