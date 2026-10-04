# Exact strict kernels of rational planar maps

4 October 2026. Conventional mathematical proof; no proof-assistant certificate is claimed. This note is independent of the existing five-signal rotation construction and changes none of its files. The theorem concerns exact guard kernels, not a physical realization of arbitrary matrices.

## 1. Statement and conventions

Let A be a rational 2-by-2 matrix, and let

    P = {x in R² : h_i x < b_i, 1 <= i <= m}

be a bounded open convex rational polygon containing 0. Here h_i are rational row vectors and b_i are rational. Every b_i is positive, because 0 satisfies every supplied guard strictly. Constant rows can be discarded. Redundant rows are allowed. Define

    K(A,P) = {x : A^n x is in P for every integer n >= 0}.

The notation A^(-n)P, when used for this set, means a preimage; A need not be invertible. Convexity is part of the hypothesis. An arbitrary nonconvex polygon is not silently included.

Define the bounded-orbit subspace

    B(A) = {x : sup_n ||A^n x|| < infinity}.

Call A *infinite-order elliptic* if it has nonreal eigenvalues of modulus one and has infinite order. For rational planar A this is exactly

    det(A)=1,  -2<tr(A)<2,  tr(A) not in {-1,0,1}.

### Theorem A: exact geometric dichotomy

1. If A is not infinite-order elliptic, one can effectively construct finitely many strict or weak rational affine inequalities whose intersection, restricted to B(A), is exactly K(A,P). The subspace B(A) has an effectively computable real-algebraic basis. Thus K(A,P) has a finite conjunction of real-algebraic linear equalities and strict/weak inequalities.

2. If A is infinite-order elliptic, one can effectively compute a rational positive definite symmetric matrix Q, a positive rational number r², and a nonempty finite set E of nonzero rational points on x^T Qx=r² such that

    K(A,P) = {x : x^T Qx < r²}
             union ({x : x^T Qx = r²} minus union_{p in E,n>=0}{A^(-n)p}).

   The matrix Q satisfies A^T Q A=Q. Each point orbit on a nonzero Q-ellipse is dense.

3. Consequently K(A,P) is semialgebraic if and only if A is not infinite-order elliptic. In the exceptional case no finite polynomial-sign formula, even with arbitrary real coefficients, agrees with membership in K(A,P) on all rational points.

4. In every nonexceptional case membership restricted to Q² does admit a finite rational linear-sign formula. This does not mean that the exact real set is always rational-polyhedral: an irrational B(A) is a genuine obstruction.

### Theorem B: effectiveness and complexity

For every fixed rational A, membership x in K(A,P), with rational x and a rational polygon P as input, is decidable in deterministic polynomial time in the total bit length of x and the inequality description of P. In particular this holds for every fixed pair (A,P). The construction is effective also when A is input, but no uniform polynomial-size explicit polyhedral output is possible: the stable family in Section 8 has exponentially many necessary facet lines as a function of the input bit length.

The elliptic decision branch is uniformly polynomial time in A,P,x by the elementary denominator argument in Section 7.2. A uniform polynomial-time decision bound for all stable A is not inferred from finite determination or from the fixed-A bound here.

These results specialize established invariant-set and orbit methods. Their presentation as one exact strict-guard classification, and their application to a particular signal-machine compiler, should not be called novel without a further literature comparison. See PRIOR_WORK.md.

## 2. Bounded orbits, closure, and all spectral cases

Because P is bounded, K(A,P) is a subset of B(A). In real Jordan coordinates, B(A) is the direct sum of all generalized eigenspaces of eigenvalues of modulus less than one and the ordinary eigenspaces of eigenvalues of modulus one. Generalized vectors above a nontrivial unit-modulus Jordan block are excluded. Components belonging to eigenvalues of modulus greater than one are excluded.

Indeed, a stable Jordan block has powers bounded by a polynomial in n times a geometrically decaying term. A nontrivial Jordan block at +1 or -1 has a linearly growing component unless the generalized coordinate vanishes. An expanding Jordan block makes each nonzero component unbounded. A conjugate nonreal pair has common modulus sqrt(det(A)); it either contracts, expands, or is an elliptic block. Distinct spectral components cannot cancel their unbounded behavior in an invertible eigenbasis. These observations also give an effective construction, using only roots of a quadratic and linear equations.

For clarity, repeated eigenvalues of a rational 2-by-2 matrix are rational. Thus a repeated eigenvalue gives these possibilities:

- Absolute value less than one: B(A)=R², including nontrivial Jordan blocks and the nilpotent case A²=0
- Eigenvalue +1 or -1: B(A)=R² if A is scalar, and otherwise B(A)=ker(A-lambda I)
- Absolute value greater than one: B(A)={0}

Distinct real eigenvalues give the direct sum of the stable and unit eigenspaces. Distinct nonreal eigenvalues give B(A)=R² for modulus at most one and B(A)={0} for modulus greater than one. This covers negative, zero, mixed stable/expanding, and mixed stable/unit cases.

There is also a useful distinction between strict and closed kernels. Write

    C = intersection_{n>=0} {x : h_i A^n x <= b_i for every i}.

Then closure(K)=C. The inclusion closure(K) subset C is immediate. Conversely, if x is in C and 0<=s<1, then

    h_i A^n(sx) <= s b_i < b_i,

so sx is in K and sx tends to x as s increases to one. This lemma does not say that every boundary point of C belongs to K.

## 3. Zero- and one-dimensional bounded-orbit subspaces

If B(A)={0}, then K={0}, because 0 is in P.

If B(A) is a line, A acts on it by a real scalar mu with |mu|<=1. Then

    K = B(A) intersect P,                       if 0<=mu<=1;
    K = B(A) intersect P intersect A^(-1)P,     if -1<=mu<0.

For nonnegative mu, every future point lies on the segment from 0 to x, which is contained in P whenever x is in P. For negative mu, the even subsequence lies on the segment from 0 to x and the odd subsequence on the segment from 0 to Ax. This proves both necessity and sufficiency, including mu=0,+1,-1. All the displayed guard rows remain rational in the original ambient coordinates.

The line itself need not be rational. For example, take

    A = [[0,1],[-1,3]],       P=(-1,1)²,
    mu=(3-sqrt(5))/2.

Then B(A) is the line y=mu x and K is its nontrivial open segment inside P. It has no description by a finite Boolean combination of rational affine linear signs. To prove this, suppose such a formula existed. At every point of the segment, at least one nonconstant atomic affine form must vanish; otherwise all signs would be locally constant in an ambient neighborhood, forcing the defined set to contain an open disk. A finite union of rational affine lines cannot cover a nontrivial segment of an irrational-slope line, because each distinct line meets it in at most one point.

On the other hand, an irrational line through 0 contains no nonzero rational point. Hence K intersect Q²={0} in this case. If B(A) is rational, its equation and the displayed guard inequalities are rational. This proves the rational-input linear-sign claim in the one-dimensional case.

## 4. Two-dimensional stable dynamics

Suppose every eigenvalue has modulus less than one. Then A^n tends to zero. We give an exact finite-horizon construction that does not assume diagonalizability, positivity of eigenvalues, invertibility, or a rational eigenbasis.

Use the induced infinity norm. Find an integer k>=1 such that

    ||A^k||_infinity <= 1/2.

Enumerating powers and comparing rational numbers terminates. Set

    C_A = max_{0<=j<k} ||A^j||_infinity.

Compute rational R>0 and epsilon>0 with

    P subset [-R,R]²,      [-epsilon,epsilon]² subset P.

The first follows by enumerating the vertices of the closed rational polygon. For the second one may take

    epsilon = min_i b_i / (2 ||h_i||_1)

over nonzero rows. Find an integer q>=0 with

    2^(-q) C_A R < epsilon,

and put N=qk. For n>=N write n=lk+j, with l>=q and 0<=j<k. Then, for every x in P,

    ||A^n x||_infinity <= 2^(-l) C_A R < epsilon.

Consequently all guards are automatically strict at every n>=N. Therefore

    K = intersection_{0<=n<=N} A^(-n)P.

Keeping the redundant time N avoids an empty intersection when N=0. This is a finite open rational polygon. It may have many facets, as Section 8 demonstrates.

## 5. Two-dimensional real unit and mixed spectra

If both eigenvalues have modulus one and B(A)=R², the real case is semisimple with eigenvalues in {+1,-1}. Thus A²=I, and

    K = P intersect A^(-1)P.

It remains to consider eigenvalues epsilon in {+1,-1} and mu with |mu|<1. They are distinct. Since tr(A) is rational, mu is rational. The spectral projector

    E=(A-mu I)/(epsilon-mu),       F=I-E

has rational entries, and A=epsilon E+mu F.

### 5.1 Nonzero stable eigenvalue

Assume 0<|mu|<1. Put r=mu², so 0<r<1. For j=0,1 and k>=0,

    A^(2k+j)x = epsilon^j Ex + r^k mu^j Fx.

For any row h_i this scalar guard is a convex interpolation between its value at A^j x and its limiting value at epsilon^j Ex. Hence it is strictly below b_i for every finite k if and only if

    h_i A^j x < b_i,       h_i epsilon^j E x <= b_i.

Necessity uses k=0 and the limit. Sufficiency follows since r^k>0, the first endpoint is strict, and the second endpoint is weak. Therefore

    K = P intersect A^(-1)P
        intersect {x : Ex in closure(P), epsilon Ex in closure(P)}.

This finite conjunction has rational coefficients and correctly handles either sign of each eigenvalue. A weak limiting inequality must not be changed into a strict one.

### 5.2 Zero stable eigenvalue

If mu=0, then Ax=epsilon Ex and A²x=Ex; thereafter the orbit is periodic with period dividing two. Therefore

    K = P intersect A^(-1)P intersect A^(-2)P.

All these guards are strict. The weak-limit argument of Section 5.1 cannot be used with r=0, since the limit is reached at a finite time. When epsilon=+1 the third factor is redundant.

### 5.3 Exact half-open counterexample

Take

    A=diag(1,1/2),
    P={ (x,y) : -1<x<2, -1<y<1, x+y<1 }.

All rectangle guards are preserved. The remaining guards are x+2^(-n)y<1 for all n. They are equivalent to x+y<1 and x<=1. Thus

    K=P intersect {x<=1}.

In particular (1,-1/2) belongs to K, although its limiting point (1,0) is outside P. No finite prefix of strict pulled-back guards describes K, since every such finite intersection is open in R², whereas K is not. The precise distinction is finite linear description versus finite determination by strict time-prefix constraints.

## 6. Unit-modulus nonreal spectra

Here det(A)=1 and -2<t=tr(A)<2. Fix a nonzero rational vector v. The two columns v,Av are independent because A has no real eigenvector. With

    S=[v Av],
    C=[[0,-1],[1,t]],
    H=[[1,t/2],[t/2,1]],

the Cayley-Hamilton identity gives AS=SC. Direct multiplication gives C^T H C=H, and H is positive definite since 1-t²/4>0. Consequently

    Q=S^(-T) H S^(-1)

is rational positive definite and A^T Q A=Q. A real change of coordinates turns this into a Euclidean rotation. The conjugating change need not be rational.

If a complex eigenvalue is a root of unity, its sum with its inverse is the rational algebraic integer t; hence t is an integer. The only possible integers are -1,0,1. Conversely these give orders 3,4,6. Thus the finite-order cases have

    K=intersection_{0<=n<order(A)} A^(-n)P,

a finite open rational polygon.

For every other rational t in (-2,2), the rotation angle is an irrational multiple of 2pi, and every nonzero orbit is dense on its Q-ellipse.

For each nonzero supplied row define

    d_i = h_i Q^(-1) h_i^T >0,
    r_i² = b_i²/d_i,
    p_i = (b_i/d_i) Q^(-1)h_i^T.

All these quantities are rational, and p_i^T Qp_i=r_i². Let r²=min_i r_i², and let E be the deduplicated list of p_i for minimizing rows. The list is nonempty since P is bounded.

The Q-inner-product Cauchy-Schwarz inequality gives

    h_i x <= sqrt(d_i) sqrt(x^T Qx).

Thus every point with x^T Qx<r² is in P. On the critical ellipse x^T Qx=r², a guard can fail only by equality, and equality occurs exactly at one of the minimizing contacts p_i. Every point on a larger Q-ellipse has a dense orbit that eventually reaches a nonempty open arc where a minimizing guard is violated strictly. These observations prove the exact formula in Theorem A.

### 6.1 Rational Euclidean conjugacy is not automatic

For example,

    A=[[0,-1],[1,1/2]]

preserves Q=[[1,1/4],[1/4,1]]. Its Euclidean rotation angle has cosine 1/4 and sine sqrt(15)/4. No rational change of basis conjugates it to a Euclidean rotation matrix, because conjugating a rational matrix by a rational matrix gives rational entries, while the sine is irrational. The correct uniform claim is preservation of a rational ellipse metric and real conjugacy to a rotation.

### 6.2 Semialgebraic and rational-sign obstruction

Fix p in E and consider O={A^k p:k in Z}. This is a rational orbit with no repeated points. Let

    I={k in Z : A^k p is in E},       k_* = max I.

The set I is finite and nonempty. Restricted to O, the forbidden union of backward contact orbits consists exactly of the indices k<=k_*. The indices k>k_* are all accepted. Both tails are dense on the critical ellipse and consist of rational points.

A semialgebraic subset of an ellipse is a finite union of points and arcs. Equivalently, the signs of finitely many polynomials are constant on each member of a finite decomposition into open arcs, apart from polynomials vanishing identically on the ellipse. Such a formula cannot accept one dense rational tail and reject another. This proves both nonsemialgebraicity of K and failure of every polynomial-sign formula to agree with K on all rational inputs. Combined with the previous sections, it proves the if-and-only-if statements of Theorem A.

## 7. Effective rational membership and exact bit-complexity scope

All spectral tests use rational arithmetic and roots of a quadratic. The following are separate claims.

### 7.1 Nonelliptic branches

If B={0}, test x=0. If B is an irrational line, rational membership again reduces to x=0. A rational nonzero vector on an invariant line would make its eigenvalue rational: select a nonzero coordinate and divide the corresponding coordinate of Ax by that of x. Therefore this branch can also be recognized effectively from the quadratic spectrum.

If B is rational, test its rational linear equations and the finitely many appropriate strict/weak guards. The real unit, one-dimensional, and mixed branches have only a constant multiple of m constraints, with coefficients obtained by rational matrix arithmetic. These branches are polynomial-time even when A is input.

In the stable branch, fix A. The k and C_A of Section 4 are constants. In dimension two, one can enumerate all pairwise intersections of supplied guard lines, retain the feasible vertices of closure(P), and compute an outer R in polynomial time. Cramer's rule shows that their coordinate bit lengths are polynomial in the input bit length L. The same holds for epsilon and for R/epsilon. Hence log_2(R/epsilon)=O(L), with a constant depending only on the fixed dimension and encoding convention. The chosen q and N are O_A(L). All powers through A^N and all pulled-back rows have polynomial bit length, and direct exact testing is polynomial-time. This handles Jordan blocks and complex stable eigenvalues without numerical approximation.

### 7.2 Elliptic branch

Construct Q,r²,E by Section 6 and compare x^T Qx with r² exactly. Accept below, reject above. On equality, reject precisely if

    A^n x=p

for some p in E and some integer n>=0. Although the Kannan-Lipton rational Orbit Problem algorithm already suffices, this particular elliptic case has a simpler exact denominator test.

Write tr(A)=a/q in lowest terms, with q>0. Infinite order implies q>=2: a rational integer trace in (-2,2) is one of the three finite-order traces. For a fixed contact p, set

    S=[p A^(-1)p],       C=[[0,-1],[1,a/q]].

The columns are independent, and A^(-1)S=SC by Cayley-Hamilton. Put y=S^(-1)x. The forbidden condition is precisely y=C^n e_1 for some n>=0.

Define integers V_0=1, V_1=a and V_k=a V_(k-1)-q² V_(k-2) for k>=2. Then

    C e_1=e_2,
    C^n e_1=(-V_(n-2)/q^(n-2), V_(n-1)/q^(n-1))  for n>=2.

For every prime dividing q, V_k is congruent to a^k modulo that prime; since gcd(a,q)=1, gcd(V_k,q)=1. Therefore the least common positive denominator of the coordinates of C^n e_1 is exactly q^(n-1) for every n>=1. This includes composite q and negative a.

First test y=e_1, which is the exceptional exponent n=0. Otherwise compute the least common positive denominator D of y's reduced coordinates. If D is not a pure power q^m, there is no hit. If D=q^m, the only possible exponent is n=m+1; compute C^n e_1 exactly and compare it with y. In particular D=1 forces the n=1 candidate e_2, after the separate e_1 test. Factoring q is unnecessary: repeated exact division by q tests pure powers.

All transformations have polynomial rational bit length. Since q>=2, m<=log_2 D, and D has polynomially many input bits after the rational basis change. Thus the candidate n is polynomially bounded in input bit length, and exact powering has polynomial bit cost. Run the test once per contact; their number is at most the number of supplied guards. This proves the uniform polynomial-time elliptic branch by elementary arithmetic.

The finite-order cases need at most six time checks. The rational contacts are important: no reduction to an algebraic-target variant of the Orbit Problem is needed.

### 7.3 What is not claimed

- No uniform polynomial bound on the finite stable cutoff or on the size of an explicit polyhedral kernel is claimed
- No unbounded orbit search is used in the infinite-order elliptic branch; the denominator forces at most one positive candidate exponent
- No conclusion about small Diophantine witnesses, unique witnesses, or finite-fold representations follows from polynomial-time membership
- No realization by a fixed number of signals follows from this abstract theorem alone; it can be composed with an independently verified physical compiler whose exact one-step chamber has the stated hypotheses
- The strict and closed kernels are not interchangeable, even though the latter is the closure of the former

## 8. Exponential explicit-polyhedral output already in a stable Jordan family

Let M>=4 be an integer, set lambda=1-1/M, and take

    A_M=[[lambda,1],[0,lambda]],       P=(-1,1)².

The input uses O(log M) bits. Both eigenvalues equal lambda<1, so Section 4 gives a finite open rational polygon K. For n>=1,

    A_M^n(x,y)=(lambda^n x+n lambda^(n-1)y, lambda^n y).

In the positive quadrant, the first-coordinate upper guard at time n is

    y < f_n(x),       f_n(x)=lambda^(1-n)/n - lambda x/n.

Adjacent lines f_n and f_(n+1) meet at

    x_n=lambda^(-n)(1-n(1-lambda)/lambda),
    y_n=(1-lambda)lambda^(-n).

Put x_0=1. Direct subtraction gives

    x_n-x_(n-1) = -n(1-lambda)² lambda^(-n-1) <0.

For every n>=1 and every x with x_n<x<x_(n-1), f_n(x) is strictly below every f_j(x) with j>=1, j not equal to n. To see this, compare each adjacent pair: f_(j+1)-f_j has positive slope and vanishes at x_j. The strict monotonicity of the x_j orders all comparisons; telescope them toward n.

Let N=floor((M-1)/2). For 1<=n<=N, both ends of the displayed x-interval lie in [0,1], and its interior lies in (0,1). Its corresponding y values are positive and less than one: Bernoulli's inequality gives

    lambda^n >= 1-n/M >= 1/2,

so y_n<=2/M<=1/2, and the endpoint at x_0 has f_1(1)=1/M. Thus the open segment

    {(x,f_n(x)) : x_n<x<x_(n-1)}

lies on the boundary of closure(K), satisfies all guards at all other times strictly, and activates exactly the first-coordinate upper guard at time n. The lower coordinate guards are automatic there because both coordinates of every iterate are nonnegative; the second coordinate is always less than one.

Therefore closure(K), and hence the boundary of K, has at least N distinct facet lines. Any exact finite Boolean formula using affine linear signs must include each such line among the zero sets of its atoms: otherwise at a generic point of that boundary segment all atomic signs would be locally constant, contradicting the boundary. Consequently explicit finite linear-sign descriptions can require Omega(M) atoms. Taking M=2^L proves an exponential lower bound in input length for such output representations.

This is an output-size obstruction, not a lower bound against a succinct decision algorithm or a formula language allowing nonlinear atoms or quantified auxiliary variables. The argument is elementary and is not asserted to be a new lower bound in the invariant-set literature.

## 9. Concrete next question

The next geometric test is a pair of independent rational planar rotations: take a rational 4-by-4 matrix A=diag(R_1,R_2), where each R_j has infinite order and their complex multipliers have no nontrivial multiplicative relation, and let P be a bounded open convex rational polytope containing0. Obtain an exact strict-kernel formula on the invariant two-tori, including lower-dimensional zero-radius strata, every active guard contact, and rational-input membership complexity.

The closed constraints on a torus involve the sum of the two blockwise support amplitudes. Strict validity must additionally remove the appropriate simultaneous backward contact orbits. A useful result would specify those contact sets and their arithmetic exactly, rather than replace the kernel by its semialgebraic closure. This is a concrete extension target, not a claim that the general torus/orbit machinery is new or that the answer is unknown in the literature.

Separately, the denominator lemma in Section 7.2 makes an explicit positive-integer certificate for general rational elliptic matrices plausible; that arithmetic ledger is being developed independently and is not claimed in this note. The sharp uniform bit complexity when stable A is part of the input should first be compared against low-order linear-recurrence positivity results. The exponential facet family alone does not answer it.

## 10. Verification boundary

The proof above is conventional and uses elementary standard facts about semialgebraic subsets of a circle, irrational rotations, and rational arithmetic. The polynomial-time Orbit Problem algorithm is a prior alternative, not a required black box for the stated planar decision bound. The newly authored verification script checks rational identities and finite instances only; it does not establish the universal statements or run a signal trajectory. No author/upstream program, saved collision schedule, numerical simulator, or existing compiler was executed in producing this note.
