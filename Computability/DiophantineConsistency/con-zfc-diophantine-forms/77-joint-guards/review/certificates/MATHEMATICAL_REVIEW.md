# Independent review: local checker graphs and index-free CRT closure

## Verdict and boundary

The local graph formulas are mathematically sound and complete for their stated
natural domains. Their literal expression trees, exact sparse coefficient
expansions, degree, variable counts, and operation counts pass an independently
written checker, both normally and under Python -O. The index-free CRT
transformation and shared product bound are valid as ordinary mathematical
compiler lemmas. Their conditional graph-slot ledger is correct.

These are **local graph and certificate-interface improvements**, not a newly
compiled whole-checker polynomial, not a numerical global variable count, and
not a new kernel-checked or internally encoded ZFC consistency biconditional.
No multiplication of local savings by the checker's PR-node count is justified
without a compositional shared-register/iteration compiler and its size proof.

The independently read baseline documents are QUADRATIC_REGISTER_SYSTEM.md,
QUADRATIC_TREE_CODE_GRAPHS.md, and QUADRATIC_GUARDED_GRAPHS.md at the supplied
repository pin2605669a532342f153b13eb6b4a0af4b54f5fa37. They establish the exact
max-square pairing convention, nil/tree/list semantics, and cited previous
local witness/count values. The authored LOCAL_GADGET_PROOFS.md matches those
semantics; it is not substituting an incompatible Cantor encoding.

## 1. Pairing quartic: branch orientation, not an approximation

Let B=t(t-1), L=a-b-s+t(2s+1), and
E=4(z-a-b)-(a+b+s)^2+t. All inputs and witnesses are natural, and every
subtraction is formal integer-polynomial subtraction. Since t(t-1)>=0 for
all integers t, B+L^2+E^2=0 forces t=0 or1 and L=E=0.

If t=0, L=0 says a=b+s, so the shell gives z=a^2+a+b, exactly the b<=a
branch of Nat.pair. If t=1, L=0 says b=a+s+1 and a+b+s=2b-1. The shell
then gives z=b^2+a, exactly the a<b branch. The witnesses s=a-b or b-a-1
are natural in the respective branches, proving completeness for every pair,
including equal components and zero. Hiding the other component gives each
unpair projection using the actual bijection, not an unverified inverse rule.

The 39-operation expression is not literally a sum of squared residuals: its
first term is B, which is nonnegative for discrete integer inputs. This is
legitimate ordinary polynomial arithmetic, but a squared-row-only compiler
needs either that nonnegative-term extension or the provided B^2+L^2+E^2
alternative. The latter has two witnesses, exact degree4 and42 tree operations.
The independent checker confirms both forms and does not conflate them.

## 2. Selector elimination is integral and sound

The shell equation is monic in t. Substituting
T=(a+b+s)^2-4(z-a-b) makes it identically zero and leaves
T(T-1)+(a-b-s+T(2s+1))^2. T is an integer polynomial and can be negative
at arbitrary inputs, but T(T-1) remains nonnegative for every integer T.
A zero therefore forces T=0 or1, so the missing natural selector is restored
without a separate naturalness guard. Conversely the preceding canonical
witnesses give T=t. This is a genuine one-natural-witness degree6 graph,
not a quartic claim. Its exact tree/DAG counts are53/18.

## 3. Predecessor, tree readers, and nil

The predecessor polynomial (n-p-1)^2(n^2+p^2) vanishes precisely when
n=p+1 or n=p=0. Over naturals these are exactly p=pred(n). It is the exact
factorization of the baseline two residual squares, not a weakened condition.
Combining it with the pair polynomial at z=p therefore implements both tree
projections. At n=0, p=0 forces a=b=0, so the right projection is also the
actual guarded listTail. Both readers use four auxiliaries rather than five.

For list head, the combined predecessor term is
(n-p-1)^2(n^2+p^2+c^2), and the remaining output term is [n(c-a-1)]^2.
At n=0 the middle factor cannot vanish through n-p-1, so p=c=0; pairing
then forces a=b=0. At n>0, the middle term forces p=n-1 and the last term
forces c=a+1. These are exactly the source's nil/found-head semantics,
including output1 for a found head equal to0. Completeness is immediate from
unpairing n-1 and its pairing witnesses. No separate output-bound slack is
needed. The five-auxiliary/59-tree-operation claim is correct.

The c^2 term is essential: deleting it permits n=p=a=b=t=s=0,c=7. Our
negative control checks this explicit false nil head. Thus this is not a
silent deletion of the baseline nil guard.

## 4. Conditional slack and reuse

For [n(c-b)]^2+[(c-a)(n-s-1)]^2, if n=0 then -s-1 is nonzero because
s is natural, so c=a. If n>0, the first term forces c=b. Choose s=0 in
the zero branch and s=n-1 otherwise. This proves both directions with
one witness, including a=b. Setting a=1,b=0 gives the zero test without
an independent Boolean guard. A pre-existing correct predecessor p may be
substituted for s in both branches, saving the new slack slot; an arbitrary
stored register cannot be reused without its exact predecessor relation.

The natural domain is substantive: if s=-1 were allowed at n=0 then both
terms vanish for arbitrary c. Our checker records this as a negative control.
No unrestricted-integer version or free domain conversion is claimed.

## 5. Exact local accounting

The independent AST walker counts every binary +,-,* occurrence, including
scalar products, both copies in a square, and the recipe's final addition
of zero. It separately hash-conses repeated subtrees for DAG counts. A custom
sparse integer polynomial ring reconstructs every published expanded term;
it does not import the author's builder or its SymPy expressions.

The exact natural auxiliary / tree-operation / degree values are:

- Pair:2/39/4; strict SOS pair:2/42/4.
- Either unpair projection:3/39/4.
- Predecessor:0/10/4.
- Tree left or right, and actual list tail:4/49/4.
- Conditional:1/16/4; zero test:1/14/4.
- Actual list head:5/59/4.
- Selector-eliminated pair:1/53/6.

All displayed variables actually occur. These counts compare the stated
literal expression-tree convention with the baseline convention, not
minimal arithmetic circuits. Factored expressions and nonsquared B should
not be advertised as already supported by an unchanged squared-row compiler.

## 6. Index-free inert-prime closure

For n>=1,m>=1 and a fixed integer-coefficient local polynomial P=e-f, where
e,f have nonnegative coefficients, choose a bound U and set

    H=e(n,U,...,U;x)+f(n,U,...,U;x)+n+U+1,
    D=4H!, S=D^n n!, Q=S, M=DQ+1.

The certificate's least remainder
B=(S binom(Q+n,n)) mod M equals the positive product
prod_{j=1}^n(Dj-1). Indeed S binom(Q+n,n)=prod D(Q+j), each factor is
Dj-1 modulo M, and the product lies strictly between0 and S<M. Thus the
old separate variable-base power used only for a product upper bound is
unnecessary. Q=S suffices; even S+1 is not required.

The moduli m_i=D(i+1)-1 are pairwise coprime. Any common prime divisor
would divide a nonzero index difference of magnitude<n<=H, hence H!,
contradicting coprimality with D. Every prime divisor of any m_i exceeds H,
and m_i=3 modulo4 has some prime divisor p_i=3 modulo4. This is the
standard sign-of-prime-factorization argument, not a primality claim for m_i.

Choose a fixed nonnegative bound d on the index degree, including P=0 by
choosing d=0 if appropriate. For P(i,w;x)=sum_{k=0}^d P_k(w;x)i^k,
replace the separate index coordinate by the ordinary integer polynomial

    R(D,A;x)=sum_{k=0}^d P_k(A;x)D^(d-k)(1-D)^k.

The identity underlying its soundness is

    R(D,A;x)-D^d P(i,A;x) is divisible by D(i+1)-1.

For each monomial this follows from the difference-of-powers factorization
of (1-D)^k-(Di)^k, whose linear factor is -(D(i+1)-1).
Thus the phrase D^d P(D^(-1)-1,A;x) is only shorthand: the delivered R is
an integer polynomial, with no division in its actual construction.

## 7. Soundness and completeness of the new certificate

Take the nested binary anisotropic norm of m+1 leaves:

    binom(A_1,U+1),...,binom(A_m,U+1),R(D,A;x).

Require B to divide that norm. At each selected p_i=3 modulo4, induction
on the binary norm tree forces every leaf to vanish. This uses anisotropy
of two squares over F_p. A flat sum of three or more squares would not be
an acceptable replacement.

Because p_i>H>=U+1, the factorial (U+1)! is invertible modulo p_i.
The falling-factorial identity for the total natural binomial then gives
A_j=w_j modulo p_i for some w_j in[0,U], using the same p_i for all j.
Since D is invertible and D(i+1)=1 modulo p_i, the cleared local residual
gives D^d P(i,w;x)=0 modulo p_i; cancel the unit D^d. Only after this
cancellation apply |P(i,w;x)|<=e(n,U;x)+f(n,U;x)<H<p_i to conclude
P(i,w;x)=0 as an integer. There is no unjustified bound on the much larger
cleared residual R.

Conversely select bounded witnesses for all i and use CRT only for A_j,
not an index coordinate. Both the range-binomial leaves and R vanish modulo
each full modulus m_i, since the relevant factorial and D are units there.
Pairwise coprimality yields divisibility by B. The norm is nonnegative for
m>=1, so its final quotient can be natural. The empty index bound n=0 is
handled separately: S=1,B=1, making the certificate vacuous as required.
No interpretation through standard-model soundness or consistency assumption
is involved.

## 8. Conditional graph ledger, not a final equation size

Assume total natural factorial, power, and binomial graphs use respectively
f,p,b internal witnesses beyond their visible inputs and output. The shared
certificate uses two factorial calls, one variable-power call, and m+1
binomial calls. The visible additional slots are:

- U and the m CRT coordinates: m+1.
- The two factorial outputs and one power output:3.
- The m+1 binomial outputs:m+1.
- The remainder B, its quotient, and its strict-bound slack:3.
- The final norm-divisibility quotient:1.

Thus the conditional total is 2m+9+2f+p+(m+1)b. This ledger does not
expand or fix the graph constructors, include an unprovided complete
checker-instance count, or establish a global degree bound. The fixed-degree
clearing polynomial uses ordinary powers, not another variable-power graph.
Natural total binomial semantics must include binom(A,k)=0 for A<k.

The index coordinate and its norm leaf are genuinely removed; the bound
norm's leaves decrease from m+2 to m+1. This can reduce the maximal norm
depth at thresholds, but no universal degree improvement after full graph
compilation is claimed.

## 9. Test coverage and recommendations

The two independent scripts run unchanged normally and with -O. Their
acceptance conditions use explicit exceptions, not removable assertions.
Exact local coefficient records and AST counts are checked, with diagnostic
small inputs and explicit counterexamples to invalid weakenings. The CRT
checker separately verifies monomial clearing identities, product/remainder
identities, field-range behavior and the conditional slot arithmetic.
These finite tests support the literal deliverables; the universal proofs
above, not a finite sample, establish unbounded correctness.

The author initially used assertions in its local generator; it replaced all
of them with explicit checks before final optimized validation. No outstanding
mathematical defect was found in the reviewed formulations. The remaining
work is formal transport, actual graph expansion with sharing, and a complete
closed-polynomial coefficient/size certificate.
