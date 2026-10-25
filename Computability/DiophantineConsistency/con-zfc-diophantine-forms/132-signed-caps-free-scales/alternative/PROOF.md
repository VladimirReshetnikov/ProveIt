# A signed squared cap replaces sixteen indexed-Pell certificates

## Result and logical boundary

The supplied polynomial is the sum of the squares of the 220 explicit quadratic residuals in `signed_cap/equation.json`, in 355 unrestricted integer variables. Its complete expanded coefficient list is `signed_cap/expanded_polynomial.json`: exact degree 4, 9,370 nonzero monomials, coefficient height 15,020,718. These are actual finite coefficient lists, not gate estimates or expressions containing variable powers.

The new theorem is a signed, squared-aggregate version of the incoming natural-number pooled Pell cap. It recovers the signs and indices of all sixteen principal ordinates from one bounded sum of squares. The construction replaces the separate index certificates of the previously completed 489-integer direct equation. It improves the variable count also relative to the new 442-integer direct equation, but not its coefficient height or support. No global optimality or historical-priority claim is made.

Composition with the frozen parent's ordinary C222/refutation and ZFC calibration gives, in ZFC, that existence of an integer zero is equivalent to existence of a finite ZFC refutation. The no-zero sentence is consequently equivalent in ZFC to Con(ZFC). This uses exactly the parent's ordinary arithmetic and logical calibration; it is not a new Lean/Rocq proof term or literal object-language ZFC derivation. Neither consistency nor inconsistency is assumed. No K215 execution or Jones universal equation is encoded here.

## 1. The signed squared-cap theorem

For A>=2 define the Pell sequences X_j(A),Y_j(A) by

    X_0=1, Y_0=0,
    X_(j+1)=A X_j+(A^2-1)Y_j,
    Y_(j+1)=X_j+A Y_j.

Suppose W>=4, A-1>9W^3, 1<=k_i<W (1<=i<=m), and m<=W. Let x_i,y_i be unrestricted integers satisfying

    x_i^2-(A^2-1)y_i^2=1.

Certify once that V=Y_(2W)(A), and impose, for s>=0 and Q an unrestricted integer,

    V=2W+1+s+sum_i y_i^2,                         (1)
    sum_i (y_i-k_i)^2=(A-1)Q.                    (2)

Then necessarily

    y_i=Y_(k_i)(A)>0,   |x_i|=X_(k_i)(A).

Conversely all these canonical positive ordinates and either sign of their abscissae satisfy (1)-(2) with some s>=0 and integer Q.

### Soundness, including signs and endpoints

Integer Pell classification gives |x_i|=X_(j_i)(A) and y_i=epsilon_i Y_(j_i)(A), with j_i>=0 and epsilon_i in {1,-1}; either sign is permissible when j_i=0. From (1), y_i^2<V. Since V>1 this implies |y_i|<V. Strict monotonicity gives j_i<2W, excluding the endpoint j_i=2W.

Modulo A-1, the recurrence gives Y_j(A)=j. Thus (2) implies that A-1 divides the nonnegative integer

    E=sum_i (epsilon_i*j_i-k_i)^2.

Each absolute difference is less than 3W. Consequently 0<=E<9mW^2<=9W^3<A-1. Hence E=0. Every signed index epsilon_i*j_i equals the positive k_i, so epsilon_i=1 and j_i=k_i. In particular neither a negative ordinate nor the zero-index solution survives. The abscissa sign is intentionally not asserted here; Section 5 recovers it from the existing power congruences.

### Constructive completeness

Set y_i=Y_(k_i)(A). Each y_i-k_i is divisible by A-1, so Q in (2) is an integer (indeed nonnegative). Put S=Y_W(A), which is at least 1. The norm and positivity give X_W(A)>(A-1)S. The double-index identity gives

    V=2X_W(A)S>2(A-1)S^2.

Each k_i<W implies y_i<S, and thus sum_i y_i^2<=m S^2. Since A-1>9W^3 and m<=W,

    V-sum_i y_i^2 > (2A-2-m)S^2 > 2W+1.

Therefore s=V-2W-1-sum_i y_i^2 is a nonnegative integer. This is an explicit restoration, not an assertion based on finite examples.

## 2. One ordinary polynomial certificate for the cap

Every new letter below is an unrestricted integer unless a sign is explicitly encoded. Use auxiliary H,J,B,S,R,d,e,f,g,h, together with U,V, and impose

    U^2-(A^2-1)V^2=1,
    H^2-(A^2-1)J^2=1,
    S^2-(B^2-1)R^2=1,
    B=1+4Vd,
    J=V^2(e+1),      e>=0,
    B=A+Hf,
    S=U+Hg,
    R=2W+4Vh.                                         (3)

Equation (1) supplies V>=2W+1>0. Thus J>=V^2>1. Pell classification of the auxiliary norm gives |H|>=A>=2 (in fact |H|>=2A^2-1). The comparison base need not be positive: if d=0 then B=1 and H divides A-1, impossible since |H|>=A. If d!=0, B=1+4Vd gives |B|>=4V-1>=3. Consequently |B|>=2 without any sign guard on d, B, f, S, R, g, h, H, or U.

The inherited signed indexed-Pell criterion applies with index 2W, principal ordinate V, auxiliary ordinate J, and moduli |H| and 4V. It gives |U|=X_(2W)(A) and V=Y_(2W)(A). Its premises 1<=2W<=V, V^2|J, the three norms, and all four congruences are exactly (1) and (3).

For clarity, two harmless signed extensions of that criterion are justified here. For negative B, define X_j(B),Y_j(B) by the same polynomial recurrence. They equal (-1)^j X_j(|B|), (-1)^(j-1)Y_j(|B|) for j>0; at j=0 the values are 1,0. Hence every signed solution at |B| also has independently signed X_j(B),Y_j(B). Polynomial base-congruence transfer and Y_j(B)=j modulo B-1 remain valid. The standard residue-class proof therefore works for |B|>=2. Also principal U may be replaced by |U| while multiplying S by the same sign; its norm and S=U modulo H are preserved. Signed H changes no divisibility modulus.

In more detail, classification gives cap index i>0, auxiliary index n>0 and comparison index r>=0. Squared divisibility V^2|J gives V|n, and also i<=n. The abscissa congruence gives r=+i or -i modulo 2n, allowing the independent sign of S and using the half-period sign-change identity. The ordinate congruence gives r=+2W or -2W modulo 4V. Therefore i=+2W or -2W modulo 2V. Since 1<=i<=V and 1<=2W<=V, the short interval implies i=2W, including its endpoint. This is precisely the inherited proof, not a new unproved classification assumption.

For completeness choose U,V as the canonical pair at 2W. The existing indexed-Pell completeness theorem supplies H,J,B,S,R and progression witnesses with B positive and e>=0. These witnesses also satisfy the weaker unrestricted domains used here. This is a single ordinary certificate at one index; no simultaneity at a new or stronger domain is required.

## 3. All size and positivity premises precede power interpretation

The retained parent frame is

    W=2+sum_(a in actual power atoms) a^2.

The atoms are the distinct bases, exponents, and outputs of all nineteen existing power requests. The literal expanded identity and request list are independently checked in `check_signed_cap.py`. Thus every such atom has absolute value less than W. Since t=t0+16 with t0>=0 and t is an atom, W>=258, and the sixteen seeds satisfy m=16<=W.

The retained guarded scale certificate is

    A^2-((W+1)^2-1)(W(z+1))^2=1,       A,z>=0.

Its ordinate is positive. Pell classification at base W+1 and the congruence Y_l(W+1)=l modulo W imply a positive l divisible by W. Hence A>=X_W(W+1)>=(W+1)^W. For W>=4, (W+1)^W-1>9W^3: it holds at W=4, and the ratio of consecutive left exponential bounds exceeds W+2, while the cubic ratio is at most (5/4)^3. Consequently A-1>9W^3, without interpreting any requested power.

All sixteen seed exponents are positive from retained semantic signs and raw polynomial rows: t, K=2R, rho+t, F^2+t, the nine positive representatives, y+1, x+1, and the positive derived-label expression. Here rho=F^2*t^2, y=F^2+r0+1, R=2+t+x+y+F^2, x,r0,t0>=0. Positivity of F itself is not yet assumed. The derived label expression has a positive constant and nonnegative constructor inputs. The supplied fresh lower-bound check establishes every seed from the retained guards and the actual source rows. It does not use an omitted seed-gap sign or any cap conclusion.

Thus the cap theorem applies before any binomial, factorial, CRT range, or requested output is interpreted.

## 4. Precisely what was deleted and added

The source is the frozen square-anchored 489-integer construction, before its monic projection. For each of its sixteen independent seed pairs, retain the principal norm and every ordinary power-congruence row. Delete only its index-at-most-Y row, comparison norm, S congruence and R congruence. Delete the old shared auxiliary norm, shared comparison-base congruence and positive-product equation. Remove the sixteen scalar sign guards on Y-k, and the two old shared auxiliary scalar guards. The exact original row numbers and literals are recorded in `cap_certificate.json`.

Unused arithmetic gates of the old certificates remain temporarily as harmless polynomial definitions and are eliminated with the same checked integral monic projection as the parent. They do not supply a premise to the new proof. No semantic sign, digit-pair guard, factorial ceiling, range row, or Horn source row is deleted.

Add (1)-(3) and (2), with e>=0 and s>=0 each represented by three unrestricted integers using

    n=a^2+b^2+c(c+1).

This represents exactly the nonnegative integers by Legendre's three-square theorem applied to 4n+1. All equations are made quadratic with the explicit wires AV, AJ, BR, VV=V^2. In particular J=VV(e+1) is quadratic. Every k_i is already affine in retained source wires, so the entire pooled sum (2) is quadratic with no additional summand wires. The exact cap coordinates and guard witnesses are supplied in the certificate.

## 5. Recovering all nineteen powers, including abscissa signs

After the signed cap theorem, each seed has Y=Y_k(A)>0 and X=+X_k(A) or -X_k(A). For a retained request at positive base n and exponent k, the unchanged row is

    X+(n-A)Y=m+T_n u,       T_n=2An-n^2-1.

The frame gives 1<=n,k<W and |m|<W. Its scale makes T_n>W^W+W. If X is positive, the usual Pell substitution gives m=n^k modulo T_n and the strict bound gives equality. If X is negative, multiplying the two conjugate expressions and using the norm gives

    m*n^k = -1 modulo T_n.

Since |m*n^k+1|<T_n, this gives m*n^k=-1 as an integer identity. Thus negative X is impossible when n>=2, and at n=1 the sole exception is m=-1. No nonnegative quotient or output hypothesis is needed; all quotients remain unrestricted.

Here is the complete noncircular orientation order, unchanged from the parent:

1. The retained factorial remainder/slack give D>=1. The retained exact-binomial output slack gives q=D+o+1>=2. The request q^t orients the t pair. The request (rho+1)^t sharing it therefore yields the actual V0>=1, even if rho+1 was initially 1. The ceiling identity DF=V0+factorial_slack now gives F>=1, hence V0>=2.
2. The retained B>=0 guard and C+F^2+1=B*i_q, C>=1, give B>0. At index K, B^K gives either N=B^K>0 or the sole inverse branch B=1,N=-1. In either case the second K base N+V0+1 is at least 2, so that request orients the K pair and excludes the inverse branch. It also recovers q=N(N+V0+1)^K.
3. Every other independent seed has a request at base q or q+1, both at least 2. This orients all remaining pairs. The t+1 pair is the inherited exact Pell addition from the already oriented t pair, not an extra unchecked seed.

Explicit request coverage, using the original output labels, is:

- pow0: (rho+1)^t; pow4: q^t.
- pow1: B^K; pow2: (N+V0+1)^K.
- pow3: (q+1)^(rho+t); pow5: (q+1)^(F^2+t).
- pow6,8,9,10,11,13,14,16,17: (q+1) raised to the nine shifted encoded representatives.
- pow12: q^(y+1); pow15: q^(x+1).
- pow18: (q+1) raised to the positive derived-label expression.
- pow7: q^(t+1), using the derived addition pair.

These are nineteen requests at sixteen independent indices and one derived index. The supplied literal audit verifies that their rows are retained and cover every independent seed.

## 6. The unchanged direct arithmetic and both directions

Having recovered every power, the twelve parent paired guards restore all digit remainder/slack signs from their nonnegative sums q^k-1. The ordered factorial argument yields F=t!, then identifies the reciprocal binomial product, then validates all CRT range digits. The amplified reciprocal CRT argument recovers every bounded local C222/Horn-flow row and the derived label bound. The parent multiplicity-flow proof extracts a finite refutation, and its ordinary C222/ZFC calibration applies unchanged. The retained parent proof and dependencies state these arguments in full; no part is inferred from finite tests.

Conversely start with a finite refutation and choose all semantic data exactly as in the parent's constructive completeness: horizon, factorial, Horn accumulators, beta CRT data, reciprocal product, powers, representatives and digit witnesses. This fixes W. The retained large-scale Pell construction gives A. Choose all seed pairs canonically at this A and the t+1 pair by addition; the old positive-power completeness supplies every retained power quotient. Section 1 supplies the aggregate slack and pooled quotient. Section 2 supplies the sole cap-index certificate at 2W. Add the two nonnegative guard representations, retain all semantic guards, and assign all now-unused old witness coordinates arbitrarily with their remaining gate definitions computed. Every new raw residual vanishes.

This reconstruction may replace private old Pell witnesses; it does not assert same-tuple equivalence for discarded coordinates. Existence is preserved in both directions. The final Horn factorization is the parent's exact identity, and every subsequent projection step has an explicitly verified integral monic restoration, so the finite 355-variable equation has exactly this existence status.

## 7. Reproduction, tests and source credits

Run `python build_signed_cap.py NEW_DIRECTORY` and `python check_signed_cap.py`; optimized Python is also supported. The builder executes only the local standard-library code and reviewed finite-polynomial utilities. The independent checker verifies literal coefficient expansion, the parent-row deletion boundary, cap formulas and guards, all power requests, frame atom identity, seed positivity, and projection certificates. Finite small-Pell tests and negative controls supplement, but do not replace, the universal proofs above.

Credit: the natural pooled-cap principle is in incoming `ConZFC_Shared_Pell_Bound_261_2026-10-24`, `portable/CAP_THEOREM.md`. This packet's new step is the squared aggregate with cap index 2W, which recovers signed ordinates through the pooled residue and removes all individual principal-ordinate signs and index tests. The unrestricted comparison-base extension is already proved in the inherited `research/comparison-base-sign/README.md`; it is reused here with explicit hypotheses. The parent 489 construction, factorial/CRT arithmetic, signed-power argument, Horn factorization, numerical calculus and ZFC calibration remain credited to their pinned sources. The complete source hashes are recorded separately.

## 8. The 352-integer odd-quotient sibling

The preferred sibling replaces just one auxiliary relation in (3):

    J=V^2(2e+1),       e unrestricted.

It removes e's single nonnegative predicate and its three witnesses. Everything else remains unchanged. Its equation in `odd_cap/equation.json` has 352 unrestricted integers and 219 quadratic residuals. The complete expanded quartic has 9,355 nonzero monomials and coefficient height 15,020,718. The preceding 355 construction remains supplied as a simpler independent sibling; neither count is inferred from the local saving alone.

### Soundness

For integer e, 2e+1 is nonzero and has absolute value at least 1. Hence |J|>=V^2>1. The auxiliary norm supplies |H|>=A just as before. Every use of J in the signed indexed-Pell proof concerns its absolute-value classification or the divisibility V^2|J; no sign of J is required. Therefore Section 2 remains valid, with |J| replacing J in its lower bound. No hypothesis elsewhere changes.

### Constructive odd quotient

Let r=2W and choose the canonical cap pair U=X_r(A), V=Y_r(A). The doubling identities give V even and U odd. Choose

    H=X_(rV)(A),   J=Y_(rV)(A)=V Y_V(U).

The Pell composition identity justifies the last equality. Expand the polynomial defining Y_V(U):

    Y_V(U)=V U^(V-1)+(U^2-1)T

for an integer T. Since U^2-1=(A^2-1)V^2, division by V gives

    J/V^2=Y_V(U)/V=U^(V-1)+(A^2-1)V T.

This is a positive odd integer: U is odd and V is even. Therefore e=(J/V^2-1)/2 is an integer, supplying the new auxiliary row.

Also H=X_V(U) is odd, since U is odd and U^2-1 is even. The norm implies gcd(H,J)=1, and V divides J, so gcd(H,4V)=1. Choose a sufficiently large positive B simultaneously satisfying B=A modulo H and B=1 modulo 4V by the ordinary Chinese remainder theorem. Set S=X_r(B), R=Y_r(B). Polynomial base transfer gives S=U modulo H, and base-one reduction gives R=r modulo 4V. The corresponding integers d,f,g,h satisfy all remaining rows of (3). This constructs the entire cap certificate explicitly; it does not assume an unproved odd-quotient strengthening of the inherited completeness theorem.

The resulting savings are exactly three coordinates and one quadratic residual. Only the aggregate slack still needs a three-witness nonnegative predicate. Build this endpoint with `python build_signed_cap.py NEW_DIRECTORY --odd-auxiliary`; check it by passing its directory to `check_signed_cap.py`.
