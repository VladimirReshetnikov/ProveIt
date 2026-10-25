# Independent audit of the signed pooled Pell cap

## Verdict and scope

The signed pooled cap in `../root_math/SIGNED_POOLED_CAP.md` is valid for integer parameters. Its sign and zero-index branches are not assumptions: the bounded error argument eliminates them. The stronger linear-cap version below is also valid, and permits signed requested indices before their eventual positivity is established. This is an ordinary unbounded mathematical audit, not a theorem-prover derivation or a claim about the consistency of ZFC. The final compiled-source and completeness checks are reported separately in FINAL_AUDIT.md and FINAL_ENDPOINT_CHECK.json.

The existing unsigned idea belongs to the incoming Shared Pell Bound 261 package. The new result under audit is simultaneous orientation of both Pell coordinates with one bounded congruence, and the strengthened aggregate that also supplies the anchor's lower bound.

## Pell classification without a sign assumption

For integers A>=2, put D=A²-1 and define X_0=1, Y_0=0, X_(j+1)=AX_j+DY_j and Y_(j+1)=X_j+AY_j. D is positive and nonsquare because (A-1)²<D<A².

Suppose x²-Dy²=1. If y=0, x=±1. Otherwise replace x,y by their absolute values, so y>=1 and x>0. Then

- x<=Ay, with equality only at y=1, since A²y²-x²=y²-1;
- x>(A-1)y, since x²-(A-1)²y²=2(A-1)y²+1>0;
- x'=Ax-Dy>0, since A²x²-D²y²=A²+Dy²>0;
- y'=Ay-x satisfies 0<=y'<y.

The inverse Pell transformation (x,y) -> (x',y') preserves the norm. Repeated descent reaches (1,0), and reversing the recurrence gives exactly (X_j,Y_j) for one j>=0. The recurrence makes Y_j strictly increasing, so j is unique. Thus every original signed solution is (σX_j,εY_j), with σ,ε in {±1}; ε is immaterial if j=0. This also shows X_j>Y_j for j>=1, because X_j²-Y_j²=(A²-2)Y_j²+1>0.

Modulo A-1, the recurrence gives X_j≡1 and Y_j≡j for all j>=0.

## Original squared-cap statement

Assume W>=4, 1<=m<=W, A-1>4W³ and 1<=k_i<W. Let V=Y_W(A). Suppose

x_i²-Dy_i²=1,
V²-1-Σy_i²=u²+v²+w(w+1),
Σ[(y_i-k_i)²+(x_i-1)²]=(A-1)Q.

All unknowns on these rows range over the integers. The ternary expression is nonnegative because w(w+1)>=0 for every integer w. Hence |y_i|<V, and classification gives 0<=j_i<W. Reducing the last row modulo A-1 yields divisibility of the nonnegative integer

E=Σ[(ε_i j_i-k_i)²+(σ_i-1)²].

Its bound is 0<=E<=4m((W-1)²+1)<=4W((W-1)²+1)<4W³<A-1. Therefore E=0. Consequently σ_i=1 and ε_i j_i=k_i>0; all coordinates are the requested canonical positive pair. No sign of Q is needed.

Conversely choose the canonical pairs. Each difference y_i-k_i and x_i-1 is divisible by A-1, so the pooled quotient is integral. For j>=1, X_j>(A-1)Y_j gives Y_(j+1)>(2A-1)Y_j. Since all k_i<=W-1, A-1>4W³ and m<=W imply V²-1-Σy_i²>=0. The ternary representation below fills the slack. Thus the original statement is bidirectional.

## Stronger linear-cap statement with signed requested indices

Assume integer W>=4, 1<=m<=W, A-1>4W³, |k_i|<W and W>=2 max_i|k_i|+1. Requested k_i may be negative or zero. Set V=Y_W(A), and replace the squared-cap row by

V=W+1+Σy_i²+u²+v²+w(w+1).

Keep the individual norms and the same pooled residue row. Then the system is equivalent to

x_i=X_|k_i|(A),
y_i=sgn(k_i)Y_|k_i|(A),

where the last expression is zero at k_i=0. In particular, when a later part of the source proves k_i>0, its pair is positive and has exactly index k_i.

Soundness: the aggregate gives V>=W+1 and y_i²<=V-W-1<V², hence 0<=j_i<W. The same bound on E holds because both signed quantities ε_i j_i and k_i lie in [-(W-1),W-1]. E=0 gives σ_i=1 and ε_i j_i=k_i, including k_i=0. This proof does not require k_i>0 before the factorial bootstrap.

Completeness: let h=max_i|k_i|. If h>=1, the doubling law gives Y_(2h)=2X_hY_h>2Y_h². Therefore

V>=Y_(2h+1)>(2A-1)Y_(2h)>2(2A-1)Y_h².

Since Σy_i²<=mY_h² and A>W,

V-Σy_i²>(4A-2-m)Y_h²>W.

This integer is at least W+1, so the needed slack V-W-1-Σy_i² is nonnegative. If h=0 then every y_i=0; Y_2=2A>W and W>=4 give V>W directly. The pooled quotient is again integral because Y_|k_i| with its sign has residue k_i. Thus all signed and zero requested-index cases extend.

## Ternary slack surjectivity

For every G>=0, the integer 4G+1 is not of the excluded Legendre form 4^a(8b+7): it is odd and is 1 or 5 modulo 8. Hence it is a sum of three squares. Its residue 1 modulo 4 forces exactly one of those squares to be odd. Write the even squares as (2u)²,(2v)² and the odd square as (2w+1)². Subtract one and divide by four to obtain G=u²+v²+w(w+1). This proof includes G=0.

## Frame bounds and remaining compiler obligations

For the literal square frame W=2(2+Σa²) over integer semantic atoms, W>=4 and W>4|a| for every atom a: 4+2a²-4|a|=2((|a|-1)²+1)>0. Thus both an original requested index k and its doubled version 2k satisfy W>=2|e|+1. Also m<=W follows when the m distinct requested indices correspond to distinct integer atoms each with |k|>=1, or from a separate explicit lower bound on W. If some requested atoms could be zero before bootstrap, mere distinctness of atom identifiers does not itself give m<=W; the actual ledger must supply this bound.

The retained scale norm A²-W³(W+2)Z²=1 with A>=0 and Z>=1 identifies (A,WZ) as a nontrivial Pell pair at center W+1. Modulo W its index is divisible by W, so A>=X_W(W+1)>=(W+1)^W. For W>=4 this yields A-1>4W³. This is independent of every intended power value.

The compiler must still certify V=Y_W(A) without circularly invoking the new principal-pair result; retain a complete indexed-Pell anchor and establish its needed sign/lower-bound premises from retained guards and the linear aggregate. Verify each literal principal norm, residue summand, the actual index (including doubled indices), atom frame, and the number m of seed pairs. Quartic degree requires every retained residual to be quadratic after the needed product registers; semantic polynomial formulas alone do not establish that.

Because the signed cap already fixes both Pell-coordinate signs, undoubled power rows can in principle recover an unrestricted output directly by their strict residue bounds. Doubling and residue-one output restrictions are no longer logically necessary, although retaining sound existing ones is permissible.

## Logical calibration boundary

The cap is only an arithmetic replacement. The exact zero-existence iff syntactic ZFC-refutation claim still depends on the inherited direct C222-calculus calibration and its C222-to-ZF and ZF-to-ZFC interfaces. Neither finite tests nor the cap lemma proves these dependencies, consistency, or global minimality. A release must keep the inherited calibration explicit and distinguish ordinary proofs from newly checked formal proof objects.
