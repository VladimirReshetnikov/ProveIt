# Independent audit: signed shared-scale positive-power graph

## Verdict and scope

**PASS for the standalone positive-power lemma.** For every fixed integer r >= 1, the polynomial displayed in `alternative/PROOF.md`, Section 1, represents the simultaneous relations m_i = n_i^k_i on the explicitly restricted input domain n_i >= 1, k_i >= 1, m_i >= 0, using exactly 4r+5 auxiliary natural variables and having exact total degree 12r+8 in independent input and auxiliary ports. In particular, the one-request graph has nine auxiliaries and degree 20, and the two-request graph has thirteen auxiliaries and degree 32.

The retained-A two-request variant has fourteen auxiliary natural variables and exact degree 24. This verdict includes a mathematical audit of arbitrary natural witnesses and an independent check of the three emitted generic polynomial DAGs. It is not a new Lean verification, a formal internal ZFC proof object, a minimality result, or a calibrated 21-variable equation for Con(ZFC).

The raw 943-tile source and the new generic strict-boundary compiler are not treated as interchangeable. A raw tile list containing an all-zero tile admits the trivial strict-boundary one-cell rectangle. Supplying and verifying the appropriate proof-checker-to-boundary translation remains a separate obligation. This audit does not certify the entire inherited tiling compiler.

## 1. Polynomial and domain accounting

The quantified coordinates are exactly

- five common coordinates z, U, v, q, b;
- four coordinates y_i, h_i, s_i, t_i for each request.

The input coordinates n_i, k_i, m_i are ports, not auxiliaries. All other displayed symbols W, Y_i, D, V, B, A, T_i, X_i, S_i, R_i are explicit ordinary integer-polynomial expressions. Integer subtraction has its ordinary meaning; no natural truncated subtraction is being used in the polynomial. The sum of squares contains two common residuals and two residuals per request.

Every operation in the audited emitted DAGs is an integer constant, a variable, addition, multiplication, or a fixed nonnegative integer power. No variable exponent, hidden graph predicate, divisibility test, or quantified range occurs in the emitted polynomial. Natural numbers include zero, but the stated input restrictions exclude n_i=0 and k_i=0. The theorem is not asserted for those inputs.

## 2. Zero and sign branches

The frame equation is

A^2 = 1 + W^3(W+2)(z+1)^2,

where W=2+sum_i(n_i+k_i+m_i). Consequently |A|>W^2, and A=0, A=1, A=-1 are impossible. Also Y_i=k_i+y_i>=1, so D>=1 and V=D^2(v+1)>0. Thus neither the main Pell Y-coordinate nor the auxiliary V-coordinate can take its zero-index exceptional value. The auxiliary norm rules out U=0. No positivity of the eliminated A or X_i was assumed before this case split.

### Negative A

Write A=-alpha, alpha>W^2, and tau_i=2alpha n_i+n_i^2+1. Then tau_i>m_i and

X_i=-(alpha+n_i)Y_i+m_i-tau_i h_i<0.

Set x_i=-X_i>0. The norm gives x_i<=alpha Y_i, while the defining identity gives

n_i Y_i+tau_i h_i<=m_i.

Hence Y_i<=m_i<=W<alpha. If Y_i>1, the norm implies x_i<alpha Y_i, and

(alpha Y_i-x_i)(alpha Y_i+x_i)=Y_i^2-1.

Its first factor is a positive integer and its second is greater than alpha Y_i. Thus Y_i^2-1>alpha Y_i, contradicting Y_i<alpha. Therefore Y_i=1 and k_i=1. The norm then gives x_i=alpha, and the defining identity reduces to m_i=n_i+tau_i h_i. Since tau_i>m_i, h_i=0 and m_i=n_i.

This is an unbounded argument covering every negative-A witness. It does not invoke an unsigned index criterion at a negative base. It proves that the entire negative branch is semantically harmless, not merely that chosen positive witnesses exist.

In fact, the negative branch has witnesses for every genuine simultaneous k_i=1 input. Choose alpha from the positive frame, set Y_i=1, h_i=t_i=0, U=2alpha^2-1, V=2alpha, v=V-1, and select b>=1 so that B=-alpha+Ub>=5 and B=1 modulo 4. This is possible because U is odd. Put q=(B-1)/4-1 and s_i=b. Then X_i=-alpha, S_i=B, R_i=1, and all four types of residual vanish.

### Positive A

For A>0, the frame gives A>W^2 and 1<=n_i<A. Therefore T_i=2An_i-n_i^2-1>=2A-2>W>=m_i. The definitions imply X_i>0, S_i>0, R_i>=k_i>=1, and B>=5. Thus every coordinate used as a natural coordinate in the imported Pell-index criterion is actually nonnegative; no sign-restoration gap remains.

Zero values of the auxiliary quotient variables y_i,h_i,s_i,t_i,z,v,q,b are allowed wherever the equations permit them. They do not create an omitted case: the positive shifts in Y_i, z+1, v+1, and q+1 establish precisely the nonzero conditions that the proof needs.

## 3. Exact imported index theorem and its signed-index alternative

The inspected pinned theorem is `Pell.matiyasevic` in the Mathlib source at commit 4dc43842a11f257ffba2a611c943a133a65cb4b2; its ordinary-integer-norm wrapper is `PellRepresentation.criterion_iff_pell` in the packet. The local file is independently checked against its pinned SHA-256 in the receipt.

For a>1 and k<=y, the nontrivial branch requires natural x,y,u,v,s,t,b with

- the three norm equations at (a,x,y), (a,u,v), and (b,s,t);
- b>1, b=1 modulo 4y, and b=a modulo u;
- v>0 and y^2 dividing v;
- s=x modulo u and t=k modulo 4y.

It concludes x=chi_a(k), y=psi_a(k). The audited definitions establish all these hypotheses exactly: each Y_i^2 divides D^2 and hence V, B-1 is a multiple of 4D and hence 4Y_i, B-A=Ub, S_i-X_i=Us_i, and R_i-k_i=4Y_i t_i. Using a stronger common divisibility condition does not invalidate the theorem.

The imported proof includes the negative index-residue alternative, rather than assuming it away. After classifying the three Pell pairs by indices i,l,j, the congruence of first coordinates implies j=i or j=-i modulo 4l. The condition y_i^2 dividing V transfers the modulus to 4Y_i, while 0<i<=Y_i and k_i<=Y_i give 0<k_i+i<4Y_i. Hence the negative alternative is impossible. The surviving positive congruence identifies i=k_i. The certificate used here has exactly the hypotheses needed for that step.

Source link: https://github.com/leanprover-community/mathlib4/blob/4dc43842a11f257ffba2a611c943a133a65cb4b2/Mathlib/NumberTheory/PellMatiyasevic.lean

## 4. Unbounded Pell classification and exponential frame bound

The standard Pell classification used for the frame has no missing bound or fundamental-unit hypothesis for this special discriminant. Here is a direct descent proof. For an integer a>=2 and a natural solution x^2-(a^2-1)y^2=1, y=0 gives (x,y)=(1,0). For y>=1,

(a-1)y < x <= ay.

Multiplication by a-sqrt(a^2-1) produces

x'=ax-(a^2-1)y > 0,  y'=ay-x >= 0.

Moreover y'<y, and x'^2-(a^2-1)y'^2=1. Induction on y therefore expresses every nonnegative solution uniquely as the jth power of a+sqrt(a^2-1). This establishes the unbounded classification used in the argument.

Apply it with a=W+1 and y=W(z+1)>0. In the quadratic-ring recurrence modulo W, the coefficient a is 1 and a^2-1 is 0, so chi_a(j)=1 and psi_a(j)=j modulo W. Thus W divides j and j>=W. The nonnegative recurrence gives

A=chi_(W+1)(j)>=(W+1)^j>W^W>=n_i^k_i.

Since T_i>=2A-2 and A>=2, both the true power and the proposed m_i lie in [0,T_i). The exact recurrence for H_j=chi_A(j)-(A-n_i)psi_A(j) is

H_0=1,  H_(j+1)=n_i H_j+T_i psi_A(j).

Consequently H_(k_i)=n_i^k_i modulo T_i, while the definition of X_i makes it m_i modulo T_i. The strict common bound then forces equality. This establishes soundness for all natural witnesses, not only boundedly tested instances.

## 5. Simultaneous completeness and dependency order

The witness order is noncircular:

1. Start from fixed genuine powers m_i=n_i^k_i and compute W.
2. Choose A=chi_(W+1)(W), z=psi_(W+1)(W)/W-1. The quotient is a positive integer by the recurrence modulo W.
3. Set X_i=chi_A(k_i), Y_i=psi_A(k_i), y_i=Y_i-k_i, and D=product_i Y_i. The inequality Y_i>=k_i follows inductively from psi_A(j+1)=chi_A(j)+A psi_A(j).
4. Set h_i to the nonnegative convolution sum in the proof. The recurrence for H proves the oriented power equation exactly, not just modulo T_i.
5. In the finite ring (Z/(4D^2)Z)[s]/(s^2-(A^2-1)), the element A+s is a unit with inverse A-s. A positive power is the identity. Choose that positive index l and set U=chi_A(l), V=psi_A(l). Then U=1 modulo 4D^2, V=0 modulo 4D^2, V>0, and v=V/D^2-1>=0.
6. In particular gcd(U,4D)=1. CRT provides B=A modulo U and B=1 modulo 4D; enlarge it by a common modulus to ensure B>A and B>1. Define b=(B-A)/U and q=(B-1)/(4D)-1, both natural.
7. Set S_i=chi_B(k_i), R_i=psi_B(k_i). Polynomial dependence on the base supplies the two required congruences. Monotonicity in the base gives S_i>=X_i, while psi_B(k_i)>=k_i. Therefore the oriented quotients s_i,t_i are natural.

All requests share the same U,V,B without assuming their Y_i are pairwise coprime. D^2 is a common multiple of every Y_i^2, and the only CRT coprimality needed is gcd(U,4D)=1, which was explicitly established. There is no unjustified attempt to combine separate local CRT solutions.

## 6. Exact degree and literal artifact checks

With all input and auxiliary ports independent, the degree bounds are

deg(Y_i)=1, deg(D)=r, deg(V)=2r+1, deg(A),deg(B)<=r+1,
deg(T_i)<=r+2, deg(X_i),deg(S_i)<=r+3, deg(R_i)<=2.

The auxiliary norm has degree 6r+4, each local norm at most 2r+6, and the frame at most max(2r+2,6). Hence the SOS degree is at most 12r+8. It is exactly that degree: the auxiliary norm contains the monomial

-16 q^2 v^2 product_i(y_i^6),

and the full polynomial contains 256 q^4 v^4 product_i(y_i^12). The other residuals do not contain v. Thus its nonzero coefficient cannot cancel. This also avoids relying only on syntactic degree upper bounds.

The independent script `audit_power_graph.py` does not import the producer's code. It:

- validates ordinary-operation topology and the precise variable/auxiliary sets;
- reconstructs all generic formulas separately and proves equality of every emitted residual and defined port by symbolic expansion;
- checks the output is exactly the sum of all residual squares;
- computes exact residual degrees with independent symbolic polynomial expansion;
- compares 150 random modular evaluations per artifact with a direct formula evaluator;
- constructs complete positive- and negative-frame k=1 witnesses, including two simultaneous requests with different bases;
- constructs shared finite-ring/CRT certificates for different local indices, including k=2 and k=3;
- tests the negative-branch local obstruction over a finite diagnostic grid;
- rejects deliberate auxiliary-count, degree, dropped-residual, and modulus-coefficient corruptions.

The tests are regression evidence and do not themselves prove the unbounded theorem. The preceding mathematical argument supplies that theorem, conditional only on the inspected standard Pell-index theorem, whose exact applicability was checked above.

## 7. Composition boundary

The 13-auxiliary graph can be substituted into two already-defined positive power requests without adding input ports as new variables. However, its degree 32 is an independent-port degree, not a degree bound after high-degree source substitutions. The producer correctly states a separate bound 1728k+8 for its signed-frame k-tile composition and 1152k+8 for the retained-A variant. Those upper bounds agree with substitution-degree propagation through the displayed circuit, in particular deg(D)<=144k, yielding auxiliary-norm degree <=864k+4 in the signed variant.

This is an accounting check of the displayed composition, not a proof that a particular fixed tile set is calibrated to a ZFC proof checker. The standalone nine-auxiliary exponentiation lemma remains a valid reusable result independently of that open source-calibration obligation.
