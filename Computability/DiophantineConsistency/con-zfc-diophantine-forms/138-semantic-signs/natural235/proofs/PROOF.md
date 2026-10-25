# Direct quartics with 235 and 236 nonnegative variables

## Statement, scope, and fixed source

The two literal polynomials in `equations/` are the sums of squares of all their supplied quadratic residuals. Their coefficients are fixed ordinary integers. The principal equation has 235 nonnegative integer unknowns, 184 residuals, degree four, 22,185 collected monomials, and coefficient height 90,911,633. The sparse companion has 236 unknowns, 185 residuals, degree four, 15,645 collected monomials, and height 88,233,865.

The ordinary arguments below, composed with the explicitly inherited direct C222/ZF/ZFC refutation calibration, prove in ZFC that each equation has a nonnegative integer zero if and only if ZFC has a finite syntactic refutation. Negation gives the requested equivalence with Con(ZFC). This does not prove either consistency or unsolvability. It is not a new end-to-end Lean/Rocq or encoded object-ZFC proof object.

The source is package 133's literal 343-variable raw arithmetic graph, pinned at repository commit `1c5367452a0bd4dd7e9e4bceb1508b62dbd2ff61`. Its full bytes are retained as `inherited/source_equation.json`; all imported file hashes and paths are in `SOURCE_LEDGER.json`. The raw graph is the common source of package 133's four natural endpoints. The source's unbounded proof is retained as `inherited/STAGED_SOURCE_PROOF.md`; the modular factorial, CRT, source-calculus and majorant arguments are retained alongside it. We change only the common Pell frame/cap, one cofinal beta-modulus choice, and explicit integral coordinate shifts. Every other raw row is checked literally.

The cap theorem is credited to package 128. Its combination with package 133's dominant common denominator and the new linear beta modulus is the contribution here. The cofinal principle and the earlier nonlinear choice y=V(V-1) occur in package 131. We claim the concrete composition and measured improvement, not historical priority for Pell equations, cofinal restrictions, or sum-of-squares compilation.

## 1. Semantic arithmetic of the source

Initially all raw coordinates are nonnegative. Write

    t=t0+16,  F=fact0.output,  b=reciprocal.Bminus2+2,
    R=2+t+x+y+F,  K=2R,
    V=(F^2+1)^t,  N=b^K,  q=N^K,
    Dt=q^t,  Dy=q^(y+1),  Dx=q^(x+1).

The six displayed powers are conclusions of the literal power certificates. They are not assumed to interpret those certificates. The source also requests one exact binomial

    b=binom(F^2+t,t)

and ten modular range binomials. Their upper indices are nine positive CRT representatives a_1,...,a_9 and a positive constructor-label polynomial J. Its lower indices are t, t+1, y+1, or x+1. A shared algebraic root is used modulo M=N*Dx.

The unchanged factorial ceiling rows imply

    V+s=bF,  b=r+s+1,  r,s>=0,

and hence F=ceil(V/b) once V and b have their intended values. The source's squared-radius fixed-point theorem, valid at t>=16, gives F=t!.

The principal cap pairs are at fifteen requested indices:

    t, K, y+1, x+1, F^2+t, a_1,...,a_9, J.

The frame's original twelve actual atoms are the distinct bases, exponents and outputs of the six exact powers. Their identities, including affine restorations, are checked from the fixed source. In particular it contains F^2+1 and t, so F^2+t is less than two plus their sum.

The independent CRT representatives satisfy the unchanged raw aggregate bound

    a_1+...+a_9 <= 9N^2.

This is not an assumed range interpretation. It is a literal nonnegative-slack equation.

## 2. A linear cofinal beta modulus

The source allowed y freely, with an endpoint row

    y=F+1+r0,  r0>=0.

Replace it by

    y=V-1.                                                   (1)

Delete r0, and use the coordinate v=V-1>=0 instead of V. Thus the emitted row is the linear equality y=v; the power output is v+1. This changes no unknown count merely by renaming: the deleted r0 is explicitly counted, and the final monic projection can identify y and v.

### Soundness

Once the power V=(F^2+1)^t has been recovered, the unchanged ceiling identity V+s=bF and b>=2 force F>=1. If F>=2, then V-1>=F^2>=F+1. If F=1, then t>=16 gives V-1=2^t-1>=F+1. Consequently the deleted source witness can be restored as

    r0=y-F-1>=0.

All old endpoint requirements therefore hold. This restoration uses neither the factorial interpretation nor any range-digit semantics. There is no circular sign bootstrap.

### Completeness

Start with a finite C222 refutation. Expand it into a finite proof tree, then pad with the inherited fixed truth step to any sufficiently large horizon t. Choose t>=16 larger than the actual local syntax data and all full constructor labels, including the padding labels. Every pending multiset contains at most t+1 entries, each of weight at most 1+tF, where F=t!.

For t>=16 one has F>(t+1)^2. This follows from 16!>17^2 and induction: (t+1)^3>(t+2)^2 preserves the inequality. Hence

    (1+tF)^(t+1) <= ((t+1)F)^(t+1) < F^(2t) <= (F^2+1)^t-1.

The strict middle inequality is F^(t-1)>(t+1)^(t+1), which follows from F>(t+1)^2 and 2(t-1)>t+1. Thus y=V-1 exceeds every pending-multiset accumulator, including multiplicities. Furthermore V=1 modulo F, so F divides y, and y>=F+1.

These are exactly the beta-CRT completeness conditions. For indices 0<=i<=t, the moduli 1+(i+1)y are pairwise coprime: any common prime would divide a nonzero difference of indices, and hence be at most t; it would then divide F and y, contradicting its divisibility of 1+(i+1)y. The inherited CRT construction produces x and the endpoint quotients with the required residues. In particular the last endpoint has zero pending accumulator and the initial endpoint has the standard value F+1. The remaining positive representatives are chosen by the unchanged amplified CRT construction.

This is an explicit witness order: t,F,V,y precede x and the later CRT representatives. It does not postulate a fixed point involving y or a future radix. The new linear choice is smaller than package 131's V(V-1) but is still large enough because the actual weight estimate is used.

## 3. The full even frame for the principal equation

Let S be the source's twelve distinct power atoms, and put

    Bframe = 2 + sum(S) + a_1+...+a_9+J,
    W = 2 Bframe.                                            (2)

Every requested index e is positive and satisfies e<Bframe directly from the raw natural definitions. The four ordinary power indices are in S. The binomial index F^2+t is bounded by the two atoms F^2+1 and t. The last ten are explicit summands. No factorial or binomial interpretation is used for these bounds.

The source lower-frame equation is retained:

    L^2 - ((W+1)^2-1)(W Z)^2 = 1,  Z=z0+1.

Use the harmless cofinal shift

    A=L+sigma+1,  sigma>=0,                                  (3)

rather than A=L+sigma. All occurrences, including affine expansions in every raw row, are translated together. Soundness has a stronger lower bound; completeness is preserved because the later common-root congruence admits cofinally many A. The generator does not replace one occurrence while leaving the other occurrences on the old base.

Classifying the natural lower-frame pair gives L=X_h(W+1) and WZ=Y_h(W+1) for h>=1. The Pell recurrence gives Y_h(W+1)=h modulo W. Thus W divides h and h>=W, whence

    L>=X_W(W+1)>=(W+1)^W,
    A-1>=L>W^3.                                             (4)

All these facts hold before interpreting any of the six powers.

## 4. One quadratic row identifies all fifteen Pell pairs

For A>=2 define

    X_0=1, Y_0=0,
    X_(j+1)=A X_j+(A^2-1)Y_j,
    Y_(j+1)=X_j+A Y_j.

Every natural solution of X^2-(A^2-1)Y^2=1 is the canonical pair (X_j,Y_j) for a unique j>=0. Also X_j=1 and Y_j=j modulo A-1, Y_j>=j, and the ordinates increase strictly.

Retain the source's complete indexed anchor at W, with principal ordinate C. Its private natural equations and witnesses are unchanged. Its exact contract is: under C>=W>=1 the certificate gives C=Y_W(A); conversely this pair admits the complete private witnesses. This is the same contract used in packages 128 and 133.

For each requested index e_i retain its principal norm. Replace the old separate aggregate bound and both staged error congruences by the single row

    C = W + sum_i (Y_i-e_i)^2 + (A-1) Q,  Q>=0.              (5)

Every expression in this row is quadratic in the literal graph coordinates and their affine restorations. The equation is not using a variable-length sum: i runs over exactly fifteen supplied pairs. Since A>=2, row (5) first proves C>=W. Hence the anchor theorem can be applied before any cap argument.

### A square excludes the next index

Let W=2Bframe and 1<=e<Bframe. Put z=Y_Bframe(A), x=X_Bframe(A). The norm implies x<=Az and x>(A-1)z, while z>=Bframe. Hence

    Y_(Bframe+1)(A)-e > (2A-2)z+1.

The doubling identity gives Y_(2Bframe)=2xz<=2Az^2. Since (2A-2)^2>=2A for A>=2, it follows that

    (Y_(Bframe+1)(A)-e)^2 > Y_W(A).                         (6)

At a solution of (5), each squared error is at most C-W<C=Y_W(A). If the actual seed index j_i were at least Bframe+1, monotonicity and (6) would contradict that inequality. Thus 0<=j_i<=Bframe.

Now reduce (5) modulo A-1. The anchor gives C=W modulo A-1, and the seed congruences give

    A-1 divides E,  E=sum_i (j_i-e_i)^2.

The frame is much larger than fifteen, so m=15<=W-2. Since 0<=j_i<=Bframe and 1<=e_i<Bframe,

    0<=E<=m(Bframe-1)^2<W^3<A-1.

Therefore E=0, and each j_i=e_i. This proves all fifteen intended Pell indices simultaneously without staged semantic assumptions.

### Constructive converse

Choose all principal pairs canonically, and set C=Y_W(A). Write z=Y_(Bframe-1)(A)>=1. Then

    sum_i (Y_(e_i)-e_i)^2 <= m z^2,
    C=2X_Bframe Y_Bframe > 2(A-1)A^2 z^2.

Because A>W+1 and m<=W-2, their difference exceeds W. Moreover C-W and every Y_(e_i)-e_i are divisible by A-1. Thus

    Q = [C-W-sum_i (Y_(e_i)-e_i)^2]/(A-1)

is a positive integer. Fresh private anchor witnesses exist by the retained indexed-Pell completeness theorem. This proves both directions of the new cap interface, with no sampling argument.

## 5. Exact powers and all later arithmetic

Each power's base, exponent and candidate output is an actual frame atom and is below W. Its retained modulus is T_n=2An-n^2-1. Natural T_n rules out n=0. The bound (4) implies that both the intended n^e and the candidate output are strictly less than T_n. The canonical Pell congruence

    X_e(A)+(n-A)Y_e(A) = n^e modulo T_n

therefore makes the unchanged power row force equality, not only congruence. All six powers are recovered. In particular V=(F^2+1)^t, N=b^K, q=N^K, and the denominator outputs have their intended meanings. Section 2 restores the deleted endpoint slack.

The unchanged ceiling rows now imply F>=1. The endpoint rows imply x>t+1 and x>y+1 before interpreting b as a binomial. Hence M=N*Dx=N*q^(x+1) is divisible by all needed digit moduli. The common-root congruence

    2A(q+1)=(q+1)^2+1+M h0

therefore produces the correct modular numerators. It is simultaneously soluble for cofinally many positive A: gcd(q+1,M)=1, so the linear congruence has gcd 1 or 2, and its right side has the needed parity in the second case. Select A>=L+1 sufficiently large and put sigma=A-L-1>=0. This also makes its ordinary quotient nonnegative.

The independent bound q>=2^(4R^2) dominates all coefficients binom(F^2+t,j), 0<=j<=t, before using the factorial value. Consequently the exact digit is b=binom(F^2+t,t). The inherited squared-radius fixed-point argument yields F=t!.

For the range digits, the raw aggregate representative bound gives a_i<=9N^2. The retained constructor-label ledger gives J<=(9N^2+1)^ell<=N^(3ell), ell=2^22. The factorial budget 3ell(t+1)<=2F<K then makes every required low binomial coefficient strictly smaller than q. The unchanged modular range extraction and amplified prime-power CRT argument recover the bounded source rows. Finally the pending-product Horn proof and the named logical interfaces `KEndpoint.c222_iff_zf_refutation` and `ConstructibleChoice.zf_refutation_iff_zfc_refutation` give a finite ZFC refutation.

For completeness, begin with the padded finite C222 proof and construct the semantic data in Section 2. Choose the nine CRT representatives in their inherited bounds, then compute all genuine powers, exact binomial values and range digits. Compute the enlarged W only after all these values are fixed. Choose the lower Pell pair and then a compatible A as above. Fill the canonical fifteen pairs, the complete anchor and Q by Section 4. The unchanged Euclidean-remainder and power-congruence constructions fill the remaining natural witnesses. The new equation thus has a zero for every finite refutation.

## 6. The 236-variable sparse companion

The sparse companion uses W=2(2+sum(S)), excluding the late ten indices from the frame. It retains two cap rows,

    C=W+sum_(i in I0)(Y_i-e_i)^2+(A-1)Q0,
    C=W+sum_(i in I1)(Y_i-e_i)^2+(A-1)Q1,

where I0 contains t,K,y+1,x+1,F^2+t and I1 contains the other ten indices. The first row supplies C>=W, the anchor and the square bound for its own early indices. Their raw frame bounds allow the same small-error argument, recovering the six powers and the factorial binomial. The preceding aggregate and label estimates then put every late index below q<W/2. Apply the second row to identify those indices. Each row has a positive quotient witness by the same converse estimate. Thus the two-row version is sound without assuming late bounds too early. Its linear cofinal modulus is the same as in Section 2.

## 7. Literal projection, audit, and comparison

The supplied raw transforms delete only the five unused old bound coordinates, their five rows, the late quotient and row in the one-row version, and r0 in both versions. The quotient signs in the new cap are positive; allowing a signed quotient would destroy its bound. The two simultaneous integral shifts are A_slack_old=A_slack_new+1 and V_old=v_new+1. The complete full-frame enlargement is literal, not a size heuristic.

All later projections are monic integral substitutions. Every deleted natural coordinate is restored by an integer polynomial whose nonnegativity has an exact rational sum-of-squares plus nonnegative-monomial certificate. Each substitution leaves every residual quadratic. The independent checker expands these identities, replays every transformed row, and independently collects every coefficient of the final quartic. These finite checks do not establish the unbounded Pell, factorial, CRT or proof-calculus theorems; those are the ordinary arguments stated above and in the retained source proofs.

Against package 133's matched dense minimum, the principal comparison is

    variables: 237 -> 235,
    residuals: 185 -> 184,
    collected monomials: 69,710 -> 22,185,
    coefficient height: 133,499,131 -> 90,911,633,
    degree: 4 -> 4.

The sparse companion has one more unknown but fewer terms and smaller coefficients. These statements compare concrete finite equations in the same nonnegative domain and direct C222 architecture. They do not assert a global simplicity minimum or dominate high-degree few-variable constructions. No K215 simulation or Jones universal coefficient tuple is used in this branch.
