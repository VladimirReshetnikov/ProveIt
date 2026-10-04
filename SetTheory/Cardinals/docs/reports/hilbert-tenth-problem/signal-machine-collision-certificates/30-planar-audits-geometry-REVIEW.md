# Independent audit of the planar strict kernel classification

Audit date: 4 October 2026 UTC

## Verdict

**PASS for the mathematical statements actually made.** No mathematical correction is required to Theorems A and B, the spectral/Jordan case analysis, the exact elliptic boundary formula, the rational-input obstruction, the elementary denominator algorithm, or the explicit-facet lower bound. The literature positioning is substantively supported and deliberately makes no novelty claim. Two optional precision refinements appear below.

This is a conventional mathematical review supplemented by newly written finite exact-arithmetic checks. It is not a proof-assistant certificate and does not certify a physical signal implementation.

## Exact source and preservation boundary

Reviewed directory: `/workspace/shared/planar-strict-kernel-classification-20261004`

The requested source pin agrees exactly:

- `PROOF.md`: `70eb8f8398d474c3343493fc88c006ce91951a2eb747c9b4133c5c481b666231`
- `SHA256SUMS`: `9dfaa3de34908d812ab29dff712d0f02c02aa1c69da1ac02ee11ef068d8abedc`
- `PRIOR_WORK.md`: `c32e05a6f60baa8d87f00cccb9cd87675875b34d9ac7f65400ea8e8a689276e9`
- `verify_exact.py`: `e2c456055b1f63dfe22b0c3bba9938ace3573cb335afd53a48b64c48e7689423`
- `verification.json`: `0e3c19a0159865647aed4a5dc0f9603c063251eb5f54037035ac460d1c0e5b3c`
- `README.md`: `b0238a72245b02a60483bf4de45343619d90f3c8fa02c2425280d6c23c59f685`

All source files, including the author script, were treated as inert text/data. Neither that script nor any upstream program or collision schedule was executed. The audit uses a separate directory. `source_before.json`, `source_after.json`, and `preservation.json` record the original inventory, SHA-256 values, modes, sizes, and nanosecond mtimes. Access times are outside the requested preservation scope.

Line references below are to the pinned `PROOF.md`; they are stable because the source was not edited.

## 1 Assumptions and completeness of the case split

Lines 7–24 correctly require a rational 2-by-2 matrix and a bounded open convex polygon containing the origin. Each supplied affine bound has positive right-hand side, even if redundant; zero rows can be discarded. The convention for A^(-n)P is a preimage and does not require invertibility.

The bounded-orbit description in lines 48–60 is correct and exhaustive. In real Jordan coordinates, a stable block contributes its entire generalized eigenspace; an expanding block contributes only zero; a unit-modulus nontrivial Jordan block contributes only its ordinary eigenspace. Norm equivalence under a fixed invertible change of basis prevents cancellation between distinct coordinates from hiding an unbounded component.

In dimension two the complete partition is:

1. B={0}: every nonzero component expands, so K={0}
2. dim B=1: a single real eigenline, including unit Jordan blocks and mixed expanding/bounded spectra
3. B=R² and both eigenvalues strictly inside the unit disk: the stable case, including singular, negative, nonreal, repeated, and nondiagonalizable matrices
4. B=R² with distinct real unit/stable eigenvalues: the mixed case
5. B=R² with real unit eigenvalues and semisimple dynamics: A²=I
6. B=R² with nonreal unit eigenvalues: finite-order or infinite-order elliptic

Repeated eigenvalues are rational because each is tr(A)/2. If a real unit eigenvalue is present, the other eigenvalue is rational. If a nontrivial Jordan block has eigenvalue +1 or −1, its generalized coordinate grows linearly in norm and is correctly excluded from B.

The closure lemma in lines 62–70 is valid: for any weakly admissible x and 0≤s<1, positivity of every b_i gives h_i A^n(sx)≤s b_i<b_i. Hence closure(K) is exactly the closed kernel C. This argument is important: replacing K by C itself would be incorrect.

## 2 One-dimensional kernels and coefficient fields

Lines 72–90 are correct. On B a scalar μ satisfies |μ|≤1. If μ≥0, all iterates lie on the segment [0,x]; if μ<0, the even and odd subsequences lie on [0,x] and [0,Ax]. Convexity and the inclusion 0∈P give exactly the one-time or two-time formula claimed, including μ=0 and μ=±1.

The example A=[[0,1],[-1,3]] has eigenvalues (3±√5)/2. Its bounded-orbit subspace is the irrational stable line y=((3−√5)/2)x. Its nontrivial segment in P cannot be defined by finitely many rational affine signs: at each point some nonconstant atom must vanish, while finitely many distinct rational affine lines meet this irrational line in only finitely many points. Otherwise all signs would persist in an ambient disk.

The rational-input conclusion is nonetheless valid. An irrational line through the origin contains no nonzero rational point. Conversely, a nonzero rational eigenvector of a rational matrix gives a rational eigenvalue by taking one nonzero coordinate ratio. Rational eigenvalues have rational eigenspaces. Thus the real coefficient-field obstruction is genuinely separated from rational-input membership.

## 3 Stable finite determination and fixed-matrix complexity

Lines 92–124 give a valid effective finite horizon. Once ||A^k||∞≤1/2 and C_A=max_{j<k}||A^j||∞, submultiplicativity gives

    ||A^(lk+j)x||∞ ≤ 2^(−l) C_A R.

The outer bound R can be obtained from the vertices of the closed polygon. The proposed ε=min_i b_i/(2||h_i||₁) places the closed ε-square strictly inside P. If 2^(−q)C_A R<ε, every x∈P satisfies every guard strictly from N=qk onward. Including time N in the finite intersection is harmless and handles the stated empty-prefix convention.

For fixed A, k and C_A are constants. In fixed dimension two, all candidate vertices come from pairs of guard lines; feasibility testing and Cramer's rule preserve polynomial bit length. Both R and ε have polynomially bounded encoding, so q and N are O_A(L). Rational powers and pulled-back rows through N have polynomial bit length. This proves the stated fixed-A polynomial decision bound without diagonalizing A or assuming a rational eigenbasis.

When A is an input, enumerating k is only an effective procedure; the proof correctly does not call this a uniform polynomial-time algorithm. The finite output construction and succinct membership complexity are kept separate.

## 4 Strict and weak guards for unit/stable dynamics

Lines 126–174 are correct.

For distinct eigenvalues ε∈{−1,+1} and 0<|μ|<1, the rational spectral projectors satisfy A=εE+μF and EF=0. Along each parity,

    h_i A^(2k+j)x = h_i ε^j Ex + (μ²)^k h_i μ^j Fx.

This equals (1−r^k)L+r^k U with 0<r^k≤1, U=h_i A^j x, and L=h_i ε^j Ex. All finite values are strictly below b_i exactly when U<b_i and L≤b_i. An equality at the unattained limit is allowed. This proves the finite rational strict/weak conjunction.

When μ=0, the limit is attained: times 1 and 2 reach εEx and Ex. All three displayed time guards must be strict. With ε=−1, time 2 can be indispensable; the packet's asymmetric example demonstrates this correctly.

The half-open example A=diag(1,1/2), P={−1<x<2, −1<y<1, x+y<1} yields K=P∩{x≤1}. In particular (1,−1/2) survives while its limit does not lie in P. Thus finite linear description does not imply finite determination by an initial collection of strict time guards.

## 5 Rational metric and exact elliptic contact formula

Lines 176–218 are correct. For v≠0 rational, S=[v,Av] is invertible because a nonreal-spectrum matrix has no real eigenvector. Cayley–Hamilton gives AS=SC for C=[[0,−1],[1,t]]. The rational symmetric matrix H=[[1,t/2],[t/2,1]] is positive definite when |t|<2 and satisfies CᵀHC=H. Therefore Q=S^(−T)HS^(−1) is rational positive definite and AᵀQA=Q.

A unit-modulus eigenvalue is a root of unity only if t is a rational algebraic integer, hence an integer. Within (−2,2), the possible traces are exactly −1,0,1, giving orders 3,4,6. All remaining rational traces give an irrational rotation angle and dense forward and backward nonzero orbits on each Q-ellipse.

For a supplied row h_i, the support maximum on xᵀQx=ρ² is ρ√d_i with d_i=h_i Q^(−1)h_iᵀ. Its unique maximizing point at equality h_i x=b_i is p_i=(b_i/d_i)Q^(−1)h_iᵀ. Thus r²=min_i b_i²/d_i is positive and rational, and E is a finite nonempty set of nonzero rational contacts. Redundant constraints do not invalidate this calculation.

Below r² every guard is strict. On the critical ellipse only the finitely many contact points can violate strictness. Above r² a minimizing guard is violated on a nonempty open arc, eventually reached by density. Hence the exact exceptional kernel is the open inner ellipse together with the critical ellipse minus the backward contact orbits. A real change of basis suffices; rational Euclidean conjugacy is neither used nor generally possible.

## 6 Dense rational tails and the sign-formula obstruction

Lines 220–228 prove the stronger rational-input obstruction, not just nonsemialgebraicity of the real set. Choose p∈E. A has no periodic nonzero point, so k↦A^k p is injective. The finite nonempty contact-index set I has maximum k_*. Restricted to this rational orbit, a contact is reached in nonnegative time exactly for indices k≤k_*; all indices k>k_* are accepted.

Both tails are dense on the same ellipse. Any finite list of real-coefficient polynomials has constant signs on some open ellipse arc after removing the finitely many zeros of restrictions that do not vanish identically. Restrictions vanishing identically carry no distinguishing information. Both rational tails meet every such arc, so no finite Boolean formula in these signs can agree with membership even just on Q².

Every other spectral branch has the displayed finite linear description over real-algebraic coefficients. The claimed semialgebraic if-and-only-if and the rational linear-sign statement therefore follow.

## 7 Contact-basis denominator decision

Lines 242–267 are valid, including the uniform bit-complexity assertion.

For an infinite-order elliptic rational trace a/q in lowest terms, q≥2. For each rational contact p, S=[p,A^(−1)p] is invertible, A^(−1)S=SC, and A^n x=p is equivalent to S^(−1)x=C^n e₁. The displayed formula

    C^n e₁ = (−V_(n−2)/q^(n−2), V_(n−1)/q^(n−1)), n≥2

follows directly from V₀=1, V₁=a and V_k=aV_(k−1)−q²V_(k−2). Modulo every prime dividing q, V_k≡a^k≠0. Consequently the second coordinate has reduced denominator exactly q^(n−1), and the common denominator of the pair is exactly that value for n≥1. This proof covers negative a and composite q.

The special vector e₁ handles n=0. Otherwise D=q^m forces the unique possible positive exponent n=m+1; D=1 gives only n=1, namely e₂. Testing whether D is a pure q-power needs repeated division, not factorization. The final exact vector comparison is essential because the denominator condition alone is insufficient.

All rational 2-by-2 basis operations and contacts have polynomial bit length in the input. Also m≤log₂D, so the candidate exponent and the bit sizes of exact powers are polynomially bounded. Repeating for at most m_guard contacts proves uniform polynomial time for this branch. The finite-order cases have at most six times. No algebraic target and no unbounded orbit enumeration is used.

## 8 Exponential explicit-facet lower bound

Lines 280–314 are correct. For A_M=[[λ,1],[0,λ]], λ=1−1/M, the nth positive-quadrant upper guard has graph

    f_n(x)=λ^(1−n)/n−λx/n.

The adjacent intersection abscissae x_n decrease strictly because x_n−x_(n−1)=−n(1−λ)²λ^(−n−1). For x_n<x<x_(n−1), adjacent differences have the sign showing that f_n is strictly below every other f_j, including arbitrarily large j. This is a universal telescoping argument, not a finite numerical horizon.

For 1≤n≤floor((M−1)/2), the segment lies in 0<x<1, 0<y<1. Bernoulli's inequality supplies the required upper bound on y. All lower guards are automatic because iterates remain positive, and all second-coordinate upper guards are strict because λ^j y<1. The time-0 first-coordinate guard is strict as well. Thus each displayed segment is a genuine exposed boundary segment of the closed kernel and of K.

Distinct n give distinct line slopes −λ/n. An exact finite Boolean formula using affine signs must have an atom vanishing identically on each facet line: otherwise choose a generic point on that segment avoiding every atomic zero and obtain locally constant truth across a true boundary. This gives Ω(M) atoms with O(log M) input bits.

The result is an output-size lower bound for explicit affine-sign representations. It does not establish lower bounds for succinct membership algorithms, unrestricted nonlinear atom languages, or quantified auxiliary representations. The packet states this limitation correctly.

## 9 Literature verdict and optional refinements

All six substantive source attributions were checked against primary papers or primary-paper indexed excerpts. Detailed URLs, locations, and access qualifications are in `LITERATURE.md`.

No novelty conclusion is justified by this audit. In particular, stable finite determination, the general rational point Orbit Problem, semialgebraic irrational-rotation obstructions, and low-dimensional orbit decidability are established prior tools.

Two nonblocking refinements could be made in a future version; no frozen source was changed:

1. `PRIOR_WORK.md` line 11: describe Gilbert–Tan §V more specifically as the semisimple +1/stable setting. “Lyapunov-stable setting” is true as a broad description of that setting but may sound as though all unit-circle spectra are treated there.
2. `PRIOR_WORK.md` line 59 and `PROOF.md` line 322: Ouaknine–Worrell §6 explicitly transfers strict-positivity results below order 5; rational-to-integer scaling is also explicit. Therefore a uniform counting-hierarchy upper bound can already be transferred to this problem. Singular A needs a finite-prefix observation under that paper's nonzero-last-coefficient LRS convention. This strengthens context and does not establish uniform polynomial time or contradict the packet's deliberately narrower claim.

The exact reduction for the second refinement is elementary. If s=tr(A), d=det(A), and u_n=b−hA^n x, then

    u_(n+3)=(s+1)u_(n+2)−(s+d)u_(n+1)+d u_n.

Thus the recurrence has order at most three. If d=0, checking n=0,1 removes every possible planar zero-eigenvalue transient; the remaining recurrence has no zero characteristic root after zero factors are dropped. Rational scaling preserves strict positivity. Multiple guards are combined by checking each sequence. No optimal uniform complexity claim is made here.

## 10 Computational evidence and limitations

`independent_exact_checks.py` was newly written for this audit, displayed and inspected before execution, and imports only Python's standard-library exact rational arithmetic. It does not read the author packet, import the author script, or run any physical trajectory.

Its checks exercise rational metric and contact identities under rational conjugation; denominator growth for all reduced traces a/q with 2≤q≤18 and |a|<2q; positive versus negative contact-orbit directions; a mixed-spectrum rational grid; the essential time-2 zero-stable witness; nilpotent, negative-Jordan, irrational-real-stable and complex-stable contraction fixtures; and new stable-facet samples.

Normal and optimized Python runs both passed and agreed byte-for-byte. `independent_results.json` records 1,212 preserved-metric identities, 1,212 rational-contact identities, 7,676 denominator instances, 8,484 forward/backward orbit decisions, 490 mixed-spectrum grid points, the zero-stable witness, four stable contraction fixtures, and 180 interior samples on 90 facet lines. `independent_results_optimized.json` confirms checks remain active under `-O`. These finite checks support algebraic accuracy only. The universal conclusions rest on the conventional arguments audited above.
