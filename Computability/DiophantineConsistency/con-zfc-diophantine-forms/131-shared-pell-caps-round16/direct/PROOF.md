# Signed pooled Pell bounds and cofinal direct certificates

## Fixed equation and dependencies

The endpoint in `integer324/equation.json` is an ordinary sum of squares of 208 explicitly listed quadratic integer residuals in 324 unrestricted integer unknowns. The companion `integer338/equation.json` replaces one pooled congruence by fifteen individual congruences. Its 338 unknowns and 222 quadratic residuals trade variables for a smaller collected polynomial. The 324-variable polynomial has 5,808 collected monomials; the 338-variable polynomial has 4,493. Both have exact degree four and coefficient height 128,446. The exact collected coefficients are in each endpoint's `expanded_polynomial.json`. No variable exponent is an operation of either polynomial.

The source is the pinned round15 direct square-shell, derived-label, unified-factorial/product construction. Its 18 power requests have 15 independent indices and one derived index. The natural arithmetic and numerical C222 calibration remain the dependencies described in round15 `architecture/UNIFIED_PRODUCT_PROOF.md` and `direct/PROOF.md`. In particular the named logical interfaces remain `KEndpoint.c222_iff_zf_refutation` and `ConstructibleChoice.zf_refutation_iff_zfc_refutation`.

This note proves a different signed representation of the complete arithmetic interface, plus an existence-preserving cofinal restriction and a self-sized radix. It proves, in ordinary mathematics formalizable in ZFC, that an integer zero exists exactly when a finite ZFC refutation exists. Negation gives the ZFC-provable equivalence of unsolvability with Con(ZFC). It neither proves consistency nor supplies a new end-to-end proof-assistant derivation. No global minimality or literature-wide novelty is claimed.

The shared-cap idea is inherited from the incoming Shared Pell Bound 261 package. The signed sum-of-squares cap, signed-index recovery, delayed front signs, odd private parameters, and exact composition here are the new signed extension. The cofinal horizon and consecutive-product beta modulus are inherited from the incoming Cofinal Witnesses package, transferred here to the already existing square-output factorial numerator. The self-sized radix is also developed in this round's natural-number construction; the literal signed source here uses q=(BH)^K, not that construction's q=(NH)^K. Both variants have the necessary bounds.

## The literal semantic changes

All notation in this section names intended values or retained coordinates. Powers are interpreted only in the order proved below.

The retained front has

    t = 16+t0,       rho=F^2,       V0=(rho+1)^t,
    B=binom(rho+t,t),       R0=2+t+x+y+F,       K=2R0,
    N=B^K.

The cofinal source adds t0=h0^2 and y=V0(V0-1). Let a_1,...,a_9 denote the independent positive CRT representatives, including the encoded index, and set

    H0=1+sum_i a_i,       q=(B H0)^K.

The aggregate constraint sum_i a_i+slack=9N^2 is removed. Its only purpose was the old radix bound. The semantic base of the third power request is replaced by B H0. The explicit transformation lists the three changed private power-base rows and the new quadratic product gate.

The old per-index comparison norms, comparison congruences, private ordinate inequalities, and common product over all principal ordinates are removed. Each original principal norm is retained, at its original undoubled requested index k_i. All original power congruences and front remainders are retained without squaring outputs or residue-one restrictions.

The private square frame is

    W=2+sum(a^2 : a is a distinct actual base, exponent, or output atom).

All atoms include their complete affine restorations. Consequently |a|<W, a^2<W and W>=258 because t>=16. For each original requested index, W>=2|k_i|+1. There are m=15 principal pairs, so m<W. No positivity of an unvalidated output or of K is used in these facts.

The old frame norm is retained, with its ordinate parameter replaced by an odd integer:

    A^2-W^3(W+2)(2z+1)^2=1,       A>=0.

There is no sign guard on z. The source still has an ordinary quadratic multiplication circuit for this displayed higher-degree identity.

## Frame and Pell facts

For integer a>=2 let X_j(a),Y_j(a) be the Pell sequences with X_0=1,Y_0=0 and

    X_(j+1)=a X_j+(a^2-1)Y_j,    Y_(j+1)=X_j+a Y_j.

Every integral norm-one solution at discriminant a^2-1 has independent signs on X_j(a),Y_j(a), for a unique j>=0. This follows by elementary descent by the smallest positive unit a+sqrt(a^2-1). In particular Y_j>=j, and the positive ordinate sequence is strictly increasing.

The frame norm and 2z+1 nonzero give A>=2. Apply classification at center W+1 to (A,|W(2z+1)|). Since Y_j(W+1)=j modulo W, the positive frame index is divisible by W and is at least W. Hence

    A>=X_W(W+1)>W^W,       A-1>4W^3.

The last inequality holds for W>=258. All following applications use A positive.

We use two elementary inherited index facts. If Y_i(A)^2 divides Y_l(A), with i,l>=1, then i divides l and Y_i(A) divides l. To see this, divide l by i, use the addition law modulo Y_i to force zero remainder, and expand modulo Y_i^2. Also, for 1<=i<=l, the congruence X_j(A)=+/-X_i(A) modulo X_l(A) forces j=+/-i modulo 2l. Reduce the Pell unit exponent modulo 2l, use its value -1 at exponent 2l modulo X_l, and reflect about l; strict growth and 2X_(l-1)<X_l distinguish all remaining absolute residues.

These are unbounded arithmetic arguments, not consequences of finite samples.

## One fully certified anchor

Introduce the single anchor (U,C), its common pair (H,J), comparison pair (S,Q), and comparison center D. The literal quadratic circuit represents

    U^2-(A^2-1)C^2=1,
    H^2-(A^2-1)J^2=1,
    S^2-(D^2-1)Q^2=1,
    J=C^2(e+1),           e>=0,
    D=1+4J(2d+1),
    D=A+Hf,              S=U+Hg,              Q=W+4Ch.

All letters other than the stated e are unrestricted integers. The cap row is

    C=W+1+sum_i y_i^2+u^2+v^2+w(w+1).                 (1)

Thus C>W>=258. The product gives J>0; hence |H|>=A and |D|>=3. D is odd and D=1 modulo 4C. No sign of D or d is assumed.

Write |U|=X_i(A), C=Y_i(A), |H|=X_l(A), J=Y_l(A), with positive i,l. Squared divisibility gives i<=l and C divides l. Classify the comparison norm at |D|. Polynomial base transfer D=A modulo H and S=U modulo H give comparison index j=+/-i modulo 2l; signs due to a negative D are absorbed by the independent coordinate signs. Since D=1 modulo 4C, the ordinate polynomial gives j=+/-W modulo 4C. It follows that i=+/-W modulo 2C. But 1<=i<=C and W<C, so only i=W is possible. Therefore

    C=Y_W(A).

The argument does not need a sign guard on U,H,S or Q. Unlike the old individual certificate, this complete index verification is performed only once.

## Bounded signed principal indices

Each retained norm gives

    x_i=sigma_i X_(j_i)(A),       y_i=epsilon_i Y_(j_i)(A),

where j_i>=0 and sigma_i,epsilon_i belong to {+1,-1}. Equation (1) implies |y_i|<C, hence j_i<W. Reduce the Pell recurrence modulo A-1 to obtain X_j=1 and Y_j=j modulo A-1.

The primary source imposes the single quadratic row

    sum_i (y_i-k_i)^2=(A-1)q0.                       (2)

The quotient q0 is unrestricted. Consequently A-1 divides

    E=sum_i (epsilon_i j_i-k_i)^2.

Because j_i<W, |k_i|<W and m<W, one has 0<=E<4mW^2<4W^3<A-1. Thus E=0, and epsilon_i j_i=k_i for each i. This statement allows zero or negative proposed k_i: the conclusion is y_i=Y_(k_i)(A) in the signed-index convention Y_(-k)=-Y_k. No premature positivity of F, K or y is required.

The sparse source instead imposes fifteen rows

    y_i-k_i=(A-1)q_i.

The signed error epsilon_i j_i-k_i has absolute value below 2W<A-1, so it vanishes directly. The same ordinate conclusion follows. The primary and sparse sources therefore have identical semantic interfaces.

The conservative `cap_both` checkpoint additionally pools (x_i-1)^2; its residual small error includes (sigma_i-1)^2 and forces sigma_i=+1 immediately. The smaller-support released variants omit those terms and orient abscissas by their genuine power requests below.

## Acyclic power and sign recovery

The only front sign premises needed at the start are x>=0, the nine encoded representatives minus one >=0, factorial remainder r>=0, factorial slack s>=0, and the exact-binomial output slack o>=0. The literal raw rows give

    B=r+s+1>=1,          q=B+o+1>=2.

The cofinal horizon gives t>=16. Thus the pooled conclusion already gives the t ordinate Y_t(A)>0, although its abscissa might still have either sign.

For any positive base 2<=n<W, exponent 1<=k<W and candidate output |m|<W, put T=2An-n^2-1. Then T>W^W+W. If the abscissa is positive, the power congruence gives m=n^k modulo T and the size bounds give equality. If it is negative while the ordinate is positive, the Pell norm instead gives m*n^k=-1 modulo T. The absolute value of m*n^k+1 is below T, so equality m*n^k=-1 would follow, impossible for n>=2. This ordinary signed-output lemma uses no sign of m.

Apply it first to the genuine request q^t. It orients the t abscissa positively. The same positive pair now certifies V0=(F^2+1)^t, including the possible base one, by direct small-residue uniqueness. The ceiling identity is FB=V0+s>0. Since B>0, F>=1. Also V0>=F^2+1 and FB>=V0, so B>F>=1, B>=2 and q>=3. None of these conclusions uses a binomial interpretation.

Now y=V0(V0-1)>=F+1: already V0>=F^2+1, and if F=1, t>=16 gives V0=2^t>=3; if F>=2, V0>=F+2. Hence the deleted endpoint slack r0=y-F-1 is nonnegative. R0=2+t+x+y+F and K=2R0 are positive. Every representative exponent is positive from its guarded +1 constructor, and the derived label exponent is positive by the inherited monotone constructor circuit. Thus every requested index is now positive.

The B^K request has base B>=2 and orients the K pair, giving N=B^K. Its other request has base B H0>=2 and gives q=(B H0)^K. Every remaining principal pair supports a request at base q or q+1, so the same lemma orients it and certifies its power. The unchanged one-step Pell addition from the oriented t pair certifies the derived t+1 request. All eighteen powers have now been recovered.

For every exact or range digit, replace its two old remainder-sign guards by the one guard r_i*s_i>=0. Its unchanged bound row is L_i=r_i+s_i+1, where L_i is now a positive power of q. Thus r_i+s_i=L_i-1>=0 and r_i*s_i>=0 imply both are nonnegative: one negative would force the other nonpositive and make the sum negative. This recovery occurs after power semantics and cannot be used to justify the initial t orientation. Our initial t orientation did not use any remainder bound.

The usual bounded remainder equations then restore all quotient signs: a positive numerator, 0<=r<L, and positive divisors exclude a negative high or range quotient. The endpoint quotients are nonnegative because x>=0, y>F, and the two endpoint rows. The front is therefore genuinely natural wherever its inherited arithmetic proof requires it.

## Self-sized radix and the unchanged factorial fixed point

From the preceding raw ceiling bootstrap, V0<=BF<B^2. Since K>=2 and H0>=1,

    q=(B H0)^K>=B^K>=B^2>V0.

For positive rho and t, every binomial coefficient binom(rho+t,j) with 0<=j<=t is at most (rho+1)^t; this is the inherited Pascal/product bound, which does not require rho>=t. Therefore the single digit is exact and B=binom(F^2+t,t). The round15 square-output fixed-point proof, valid for t>=16, then gives F=t!. This proof uses F>t^2, obtained from 2^t/(t+1)>t^2, to exclude any small additional fixed point.

The same B is the product of the pairwise coprime d_i=1+F^2/i, 1<=i<=t. Thus N=B^K is still the amplified CRT modulus. The new q is N*H0^K, so N divides q.

Every independent representative a_i is strictly below H0. For an ordinary lower range index 1<=k<R0 and j<=k,

    binom(a_i,j)<=a_i^k<H0^K<=q,

with the coefficient zero if j>a_i. No aggregate representative bound is needed. For the derived label Jlabel the inherited ledger gives Jlabel<=(n+1)^ell, where n is the largest of its four syntax parameters and ell=4194304. Since H0 exceeds every positive independent representative, n+1<=H0 and Jlabel<=H0^ell. The retained padding t>=16 and F=t! give ell(t+1)<2F<K, hence every needed derived-label coefficient is below H0^K<=q. The earlier stronger coefficient estimate using 3ell also suffices.

The local Horn majorant still gives L<R0^8388608<2^R0<2^K. All prime-power range-decoding and multiplicity arguments therefore apply exactly as in the inherited proof. In particular they do not assume that a supplied rule multiset is acyclic, and the truth label still has unit weight.

## Cofinal completeness at the new beta modulus

Start with a finite C222 refutation, not with an assumed solution or consistency assumption. Expand its DAG into a finite tree. Choose h0 large enough that t=16+h0^2 dominates its step count, every local parameter and every full constructor label sum, including the fixed truth-padding tuple. Insert truth steps to reach exactly t rows. This restriction is complete because every sufficiently large horizon is permitted, not merely because an unspecified admissible set is unbounded.

Set F=t!, b=F^2+1 and V0=b^t. Each pending multiset has at most t+1 members, including multiplicities, and every weight is at most 1+tF<=F^2+1=b because F>=t. Hence each accumulator is at most b^(t+1). Since t>=16 and b>=2,

    y=V0(V0-1)=b^t(b^t-1)>b^(t+1).

Moreover V0=1 modulo F, so F divides y, and y>=F+1. These are precisely the inherited first beta-CRT requirements. The moduli 1+(i+1)y, 0<=i<=t, are pairwise coprime: a common prime divides i-j, hence is at most t and divides F and y, contradicting its divisibility of either modulus. Choose the CRT code x and its nonnegative endpoint quotients.

Then fix R0,K,B,N and choose the nine independent positive representatives by the original CRT at precision d_i^(2K). No aggregate cap is imposed on them. Only afterwards compute H0 and q=(B H0)^K. The bounds above validate all required digits uniformly in these chosen representatives. This dependence order has no fixed-point or future-modulus circularity.

## Complete private Pell witnesses

For these genuine front values form the exact square frame W. Set A=X_W(W+1). The recurrence Y_(n+2)=2(W+1)Y_(n+1)-Y_n gives Y_n(W+1)=n modulo 2W, so Y_W(W+1)/W is a positive odd integer. Set z=(Y_W(W+1)/W-1)/2. This supplies the odd frame exactly.

Choose each main pair canonically at k_i, and choose the anchor U=X_W(A), C=Y_W(A). Let h=max_i k_i. The square frame gives W>=2h+1. Pell doubling and growth imply

    Y_(2h)=2X_hY_h>2Y_h^2,
    Y_(2h+1)>(2A-1)Y_(2h)>2(2A-1)Y_h^2.

Thus C-sum_i Y_(k_i)^2>(4A-2-m)Y_h^2>W. Consequently the slack in (1) is nonnegative. Its ternary witnesses exist by the standard representation n=u^2+v^2+w(w+1) of every nonnegative integer.

Choose a positive Pell unit power at A that is one modulo 8C^2. Its coordinates give H odd, J>0 divisible by C^2 and gcd(H,8J)=1. Set e=J/C^2-1>=0. CRT now chooses a sufficiently large positive D with

    D=A modulo H,       D=1+4J modulo 8J.

Hence D=1+4J(2d+1) for an integer d. Choose the comparison pair at index W; polynomial base transfer gives its two required congruences. Fill the three signed quotient witnesses. This constructs the full single anchor, including the strengthened odd multiplier condition.

For the pooled row, each Y_(k_i)-k_i is divisible by A-1, so its sum of squares is divisible by A-1. The sparse quotients exist individually. Fill every genuine power congruence by the ordinary recurrence identity and every retained sign guard by the ternary representation. This gives a complete zero of the new source. Conversely, the prior soundness argument gives a genuine front refutation; one may reconstruct old natural Pell witnesses afresh. No claim identifies the old and new private witnesses pointwise.

## Exact compilation and verification boundary

`build_cap.py` records the full square-frame atom list, removed private constraints, complete new anchor, pooled or individual residues, actual sign guards, front changes, and source hashes. Every guard G>=0 is the quadratic row G=a^2+b^2+c(c+1). Products of interval coordinates and the linear-in-anchor sum of squares are themselves quadratic.

The inherited exact Horn factoring does not alter its external interface. Monic integral projection then removes only equations z-Q=0 with integral quadratic Q and substitutions that leave every residual quadratic. Its certificate restores every deleted variable; unconstrained variables may be restored as zero. Integral translations are bijections old=new+shift. The separately stored collected polynomial is the exact sum of squares, not a numerical sample or a symbolic exponent shorthand.

For reproduction from the workspace root:

    python diophantine_zfc_round16/direct/build_cap.py diophantine_zfc_round16/direct/portable_input diophantine_zfc_round16/direct/rebuilt --strong-cap --odd-frame --odd-comparison --ys-only --cofinal --self-radix
    python diophantine_zfc_round16/direct/center_integer.py diophantine_zfc_round16/direct/rebuilt diophantine_zfc_round16/direct/rebuilt_integer324

Add --sparse for the 338-variable companion. The separate conservative checkpoints retain stronger sign conditions or omit cofinal restrictions. Their counts must not be confused with the released two endpoints. Literal checks certify syntax, complete expansion and exact algebraic maps. The unbounded Pell, factorial, CRT, Horn-flow and calibration arguments above and in the identified dependencies supply the semantic theorem.
