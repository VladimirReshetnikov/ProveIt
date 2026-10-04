# Periodic collision macros with at most four signals

Research draft, 4 October 2026. Conventional proofs, not proof-assistant checked. No priority claim is made. This packet concerns a supplied periodic collision word, not arbitrary signal-machine runs. No upstream program, saved schedule, downloaded code, or physical simulator was executed.

## 1. Main results and parameters

Fix a rational signal machine whose local rules preserve the number of live signals. Speeds are rational constants. Incoming and outgoing signals at each collision have pairwise distinct speeds, as in the standard definition. A **complete batch** comprises every collision site at its time, with all incident signals and the specified local rule at each site. Subsequent batches must have strictly positive time separation.

Fix an outgoing collision section, a nonempty finite word W of complete batches, and a final section with exactly the same ordered labels and outgoing co-location pattern as the initial section. The word, rules, speeds, and sections are compiler data. Assume the population N is at most four. The variable input is the vector of positive gaps between the distinct sites of the initial section. An overall spatial translation and positive rational common denominator may be supplied separately.

**Theorem A (infinite periodic validity).** One can effectively construct a Boolean combination of rational polynomial sign tests, each of degree at most two in the initial gaps, that holds exactly when every finite prefix of W^omega is the genuine complete collision history from that section. No event horizon is used. For integer gap numerators, the formula has an explicitly constructed sum-of-squares Diophantine representation of degree at most four with exactly one natural witness tuple on every accepted input and no witness on a rejected input. Its arity depends on W and the fixed machine data, but not on the number of repetitions. There is no claim of one fixed arity uniformly over all supplied words.

**Theorem B (the physical clock).** On the valid inputs of Theorem A, whether the infinitely many batches have finite total elapsed time is decidable by another degree-at-most-two sign formula. Thus validity plus Zeno, and validity plus non-Zeno, each have the same explicit unique-witness quartic construction. In the Zeno case with rational initial gaps, the accumulation time is rational and effectively computable. Exact equality to, or strict comparison with, a supplied rational deadline is again included by degree-at-most-two integer sign tests.

**Theorem C (rational limit obstruction, any fixed finite population).** For any number of signals, a valid ultimately periodic complete collision macro with rational speeds and rational initial positions can have only rational finite accumulation times and rational limiting positions of its periodically named collision sites. This is conditional on validity of the infinite macro. It does not assert effective recognition in arbitrary dimension. Consequently a rational signal-machine execution accumulating at an irrational time or irrational spatial location cannot have an ultimately periodic complete macro in the sense used here.

Theorem A's degree statement holds because all matrix and macro coefficients are fixed before the initial gap variables are introduced. Making those coefficients polynomial inputs would change the degree accounting. This is a lasso certificate class, not a Diophantine representation of arbitrary nontermination, a solution to general Positivity/Skolem, or semantics at/after an accumulation.

## 2. Collision sections really have dimension at most two

Immediately after a complete batch, list the N outgoing signals in increasing spatial order. Within each co-located outgoing group, list them in strictly increasing speed order. Let g_i be the gap between signals i and i+1, for 1 <= i < N. Let Z be the set of zero gaps inside co-located groups. All other gaps are strictly positive. Translation of the entire configuration has been removed.

Because this is a collision section, at least one group has size at least two, so |Z| >= 1. Let d=N-1-|Z| and let L:R^d -> R^(N-1) insert zeros at the indices in Z; let R select the complementary coordinates. Then R L=I, and every configuration in the section has g=Lx with all coordinates of x positive. Therefore d<=N-2<=2.

This count includes simultaneous disjoint collisions: two binary groups at N=4 give |Z|=2 and d=1. A triple group also gives d=1; a four-signal group gives d=0. Outgoing co-location has not been replaced by an arbitrary later observation phase. Doing that would add a phase coordinate and invalidate this dimension argument. If d=0, homogeneity forces every proposed positive flight time to be zero, so a nonempty repeated macro is impossible.

The outgoing order is not an optional encoding convention. Its strict speed order makes each initially co-located group separate immediately; equal-speed co-located outputs are excluded by the standard rule definition. Distinct equal-speed signals at different positions are allowed. Zero-duration cascades are not silently merged into this theorem: they are excluded, and a batch must already contain every collision at its timestamp.

## 3. An explicit one-macro linear chamber

At a fixed outgoing mode, let v_i be the speed of the i-th signal and c_i=v_i-v_(i+1). During a collision-free interval of length tau,

    g'_i = g_i - c_i tau.

Only an adjacent pair with c_i>0 can generate the next collision. Such a closing pair has g_i>0: if it were co-located in the outgoing section its order would have c_i<0. Its candidate time is g_i/c_i. If there is no closing adjacent pair, a proposed next batch is impossible.

Let S be the specified set of incoming zero-gap indices at the proposed next batch, and choose a pivot j in S. Require c_j>0 and put tau=g_j/c_j. Require tau>0. For every other closing index i require

    g_i/c_i - tau = 0       if i is in S,
    g_i/c_i - tau > 0       if i is not in S.

Reject structurally if an index in S is not closing. Add the specified zero/strict-positive gap conditions in both the starting and resulting outgoing sections. Check the labels and rule of each maximal consecutive block of S; replace all blocks at once and sort each output block by increasing speed. Each block preserves its size, so the gap indices outside the blocks continue to mean the same ordered inter-site gaps; gaps within an output block are zero.

These conditions are necessary and sufficient for the indicated complete next batch. Necessity follows from first-collision semantics. For sufficiency, all adjacent gaps remain nonnegative until tau; a nonadjacent crossing would require an earlier adjacent crossing. The strict inequalities exclude earlier competing collisions and omitted simultaneous sites. Every maximal zero block includes all co-located incoming signals, and the strict gaps between blocks prevent two purported sites from being the same site. Requiring all tied closing indices prevents omitted inputs to a multiple collision. Speed-sorted distinct outputs establish the next outgoing section. Thus no collision is hidden by the encoding.

Every gap and time after one step is a homogeneous rational linear form in the initial gaps. Iterating this *symbolic construction over the fixed finite word*, without executing a trajectory, produces rational matrices E,G,T and rows ell,r such that:

    one macro is legal  iff  E x=0 and G x>0;
    final full gap vector = T L x;
    macro elapsed time = ell x;
    leftmost position increment = r x.

Here E includes the final zero-gap conditions of the original section. G includes positive time separation for every batch and every specified strict gap. The final labels and zero pattern must exactly equal the initial ones; a mismatch is structural rejection. Set M=R T L. On the chamber, T L x=L M x. We may keep redundant rows. For a word of m batches, a direct construction uses at most

    (2m+1)(N-1)+m <= 7m+3

zero/strict rows: all m+1 section gap conditions, at most N-1 candidate-time comparisons per batch, and one positive flight-time row per batch. This is only a row bound, not an optimized arithmetic-operation count.

Induction now proves the exact infinite criterion

    E M^n x=0 and G M^n x>0 for every n>=0.               (1)

The induction uses the final section equalities at each stage. It does not assume that M maps the entire ambient vector space into the physical section. Given (1), every finite prefix is the unique actual history. Conversely an actual W^omega prefix sequence gives (1).

## 4. Exact order-two guard classification

Pad d=1 to d=2 with a zero coordinate and a zero second row/column; this changes no physical sequence. Equalities a M^n x=0 for all n are equivalent to the two linear equalities a x=0 and a M x=0, by Cayley-Hamilton. For d=1 one equality already suffices, but the padding is harmless.

For inequalities first inspect the rational constant discriminant

    delta_M = (tr M)^2 - 4 det M.

### 4.1 Nonreal spectrum

If delta_M<0, a scalar sequence a M^n x has the form

    rho^n (A cos(n theta)+B sin(n theta)),  0<theta<pi.

A nonzero sequence of this form cannot stay nonnegative. If theta/(2pi) is rational, the finitely many values over a full period sum to zero, and nonnegativity would make all of them zero. If it is irrational, the powers of exp(i theta) are dense on the unit circle, so a nonzero real linear functional takes negative values along them. The usual elementary density proof follows from the pigeonhole principle applied to fractional parts, producing arbitrarily small nonzero rotation steps. Thus weak nonnegativity holds only for the zero sequence, and strict positivity never holds.

Our macro contains at least one strictly positive flight-time guard. Hence delta_M<0 makes (1) empty. This branch is checked before squaring M; in particular, a pure-imaginary spectrum whose square is a negative scalar matrix is not misclassified as positive spectrum.

### 4.2 Real spectrum, including negative and zero roots

Suppose delta_M>=0. Put B=M^2. Its eigenvalues alpha>=beta>=0 are the squares of the real eigenvalues of M. For each guard row a and each parity epsilon in {0,1}, put

    A0 = a M^epsilon x,
    A1 = a M^(epsilon+2) x.

The subsequence a M^(2n+epsilon) x is determined by A0,A1 and the characteristic polynomial of B. Write t=tr B, h=det B, Delta=t^2-4h. The following tests are necessary and sufficient.

1. If alpha>beta>0, strict positivity is

       A0>0 and A1-beta*A0>=0.                           (2)

   Weak nonnegativity replaces A0>0 by A0>=0. Indeed, after division by alpha^n the nth term is

       D + (A0-D)(beta/alpha)^n,
       D=(A1-beta*A0)/(alpha-beta).

   It is a convex interpolation of the initial value A0 and the limiting value D. This proves both directions, including D=0. There is no finite-index cutoff hidden in this argument.

2. If alpha>beta=0, strict positivity is A0>0 and A1>0; weak nonnegativity is A0>=0 and A1>=0. The initial term is A0 and all later terms are A1 alpha^(n-1).

3. If alpha=beta=lambda>0, strict positivity is

       A0>0 and A1-lambda*A0>=0.                         (3)

   Weak nonnegativity replaces the first sign by >=. Cayley-Hamilton gives the exact Jordan formula

       lambda^n (A0+n(A1/lambda-A0)).

   This includes the diagonalizable scalar case, where the linear term is zero. It does not assume diagonalizability.

4. If alpha=beta=0, B^2=0, so strict positivity for all n is impossible. Weak nonnegativity is exactly A0>=0 and A1>=0. In the actual M^2 situation M^2=0 already, but the more general statement is harmless.

Apply the relevant test to both parities. This automatically handles distinct eigenvalues of M with opposite signs, a repeated negative eigenvalue and its Jordan block, and a zero eigenvalue. For example, when M has eigenvalues lambda,-lambda, B is scalar and both parity initial values must be positive; a sign-alternating nonzero trajectory therefore fails.

### 4.3 Eliminate the square root explicitly

Only (2) may contain a nonrational coefficient. Set

    C=2 A1-t A0,
    H=Delta*A0^2-C^2.

Under A0>=0 and Delta>0,

    A1-beta*A0>=0
      iff C>=0 or (C<0 and H>=0).                       (4)

This follows by writing twice the left side as C+A0 sqrt(Delta), separating the sign of C, and squaring only when the nonnegative sides may be compared. Formula (4) remains correct at A0=0. The repeated eigenvalue lambda=t/2 is rational, so (3) has rational coefficients. All fixed rational denominators can be cleared by positive integers.

Thus every strict or weak infinite guard becomes a Boolean formula in linear and quadratic integer polynomials in x. A strict guard needs at most six distinct polynomial-sign atoms (A0,C,H for each parity); the other spectral cases need fewer. Every infinite equality needs at most two linear atoms. The construction is uniform as an algorithm in the finite machine/word description, but the degree bound treats that description as fixed constants.

This proves the sign-formula part of Theorem A. It is a special order-two calculation, not a finite spectral test for arbitrary linear recurrences.

## 5. A literal unique-witness quartic compiler

Let Phi(p) be any Boolean formula of sign tests of integer polynomials Q_j(p), each of degree at most two. Integer gap numerators p are natural inputs; a common positive denominator does not change homogeneous guard signs. For each distinct Q introduce natural witnesses e_-,e_0,e_+,z and the six residuals

    e_-(e_--1),  e_0(e_0-1),  e_+(e_+-1),
    e_-+e_0+e_+-1,
    Q-(e_+-e_-)(z+1),
    e_0 z.                                               (5)

Every residual has degree at most two. For every input there is exactly one solution of (5): the three flags indicate the sign of Q; when Q!=0, z=abs(Q)-1; when Q=0, e_0=1 and z=0. In particular the zero branch has no free slack.

Read Q>0 as e_+, Q=0 as e_0, and Q>=0 as the Boolean negation of e_-. Translate Phi to a finite AND/OR/NOT circuit. Give each gate one natural witness b and one defining residual:

    AND: b-u v;  OR: b-u-v+u v;  NOT: b-1+u.

Inputs to each gate are already Boolean; induction makes every gate output Boolean and uniquely determined. Add the final residual b_out-1. Sum the squares of all residuals. The resulting ordinary integer polynomial has degree at most four and exactly the asserted natural zero fibers. A constant-false formula is represented by 1; constant true by 0. No quadratic guard is multiplied by a selector. The sign equation in (5), not selector gating of Q, is what preserves residual degree two.

For A distinct sign atoms and J logic gates this direct construction has exactly 4A+J natural witnesses and 6A+J+1 residuals. Zero or reused constant output cases can be simplified separately. With S strict/weak infinite guard rows and E equality rows, one may use A<=6S+2E before adding the clock/deadline predicates. Natural witnesses may be shifted by +1 if a positive-witness convention is desired, preserving degree and uniqueness.

This proves the polynomial part of Theorem A constructively, without MRDP, Pell equations, exponentiation atoms, or an unbounded history code. It is a certificate for a *fixed supplied periodic schedule*; uniqueness here has no bearing on the open general finite-fold/single-fold MRDP questions.

## 6. Decide summability from the clock, not from the whole matrix

Let ell x be the sum of the positive flight times in one macro. Under (1), u_n=ell M^n x is strictly positive. Total elapsed time is sum_(n>=0) u_n. Test its even and odd subsequences using the preceding notation A0,A1 for the clock row ell.

In the distinct positive-root case alpha>beta>0:

- If alpha<1, both subsequences are summable.
- If alpha>=1>beta, a subsequence is summable exactly when its dominant coefficient is zero, i.e. A1-beta*A0=0.
- If beta>=1, no strictly positive subsequence is summable.

In the case alpha>beta=0, strict validity forces A1>0, and summability is exactly alpha<1. In the repeated positive-root case, strict validity forces A0>0 and nonnegative Jordan slope, and summability is exactly lambda<1. The nilpotent case has no valid infinite strict clock.

For the cancellation case alpha>=1>beta>0 with Delta>0 and A0>0, the exact equality is

    C<0 and H=0,                                         (6)

using Section 4.3. This again uses only linear/quadratic signs. The comparisons of alpha,beta with 1 are comparisons of fixed real quadratic algebraic constants, so can be decided exactly while compiling. These choices do not introduce algebraic constants into the emitted polynomial. This proves Theorem B's Zeno and non-Zeno sign classifications.

For a rational input x=p/q, write a_e=ell p, b_e=ell M^2 p, a_o=ell M p, b_o=ell M^3 p. If 1-t+h !=0 and the series converges, its sum is

    T = [b_e+b_o+(1-t)(a_e+a_o)]/[q(1-t+h)].              (7)

If 1-t+h=0 and a valid convergent clock exists, B has a simple eigenvalue 1 and another eigenvalue beta<1; both eigenvalue-1 clock coefficients vanish. In that case

    T = (a_e+a_o)/[q(2-t)].                              (8)

The repeated eigenvalue 1 admits no valid summable clock. Equations (7)-(8) follow either by summing the two elementary formulas or by cancelling the rational generating function. Each is a rational linear function of p divided by q. Clear its fixed rational coefficients to write T=L(p)/(Dq) with an integer linear form L and positive integer D. For a supplied rational deadline H/K with K>0, equality is

    D q H - K L(p)=0,

and T<H/K means the same degree-at-most-two integer polynomial is positive. Conditions q>0 and K>0 can be encoded by the same sign compiler when they are not domain promises. Add an initial rational time offset by ordinary denominator cross-multiplication if desired; the stated degree bound uses section time zero.

An eigenvalue of modulus >=1 in the full matrix need not prevent Zeno behavior: it may be invisible to the clock along the given input. Conversely, mere stability of one visible component does not certify legality. Both the exact guards and clock cancellation tests are essential.

## 7. A four-signal example with an included limiting boundary

Use five meta-signals, with speeds

    L:+1, R:-1, P:+3, Q:-3, S:-2.

The two nontransparent rules are

    {P,R}->{Q,R},
    {L,Q}->{L,P}.

Every other allowed incoming set may use the transparent rule C->C. Thus every collision preserves the number of live signals and has distinct incoming/outgoing speeds. No computation after the first unprescribed collision is used. Start immediately after a left bounce with

    L and P at 0, R at d, S at d+y, with d,y>0.

The outgoing order is L,P,R,S and the gap vector is (0,d,y). The proposed macro consists of one P-R bounce followed by one Q-L bounce.

The first bounce occurs after d/4 provided y>d/4: the other closing candidate is R-S at time y. At this first bounce the outgoing order is L,Q,R,S and the gaps are (d/2,0,y-d/4). The second bounce occurs after a further d/8 provided y-d/4>d/8. Thus the exact one-macro chamber is

    d>0 and y>3d/8,

and the return data are

    M(d,y)=(d/4, y-3d/8),
    ell(d,y)=3d/8,
    leftmost displacement=3d/8.                         (9)

The spectator remains strictly to the right of R during each legal prefix. The shuttle is between L and R until each bounce, so no spectator-shuttle or spectator-left-wall collision can precede the R-S candidate. This verifies the complete, not merely selected, collision chronology.

After k legal cycles,

    d_k=d/4^k,
    y_k=y-(d/2)(1-4^(-k)),
    t_k=(d/2)(1-4^(-k)).                                (10)

For K>=1, the first K complete *strict* cycles are valid exactly when

    y>(d/2)(1-4^(-K)).                                  (11)

At equality in (11), the endpoint batch has an additional spectator collision and is not the prescribed complete batch. Intersecting (11) over all finite K yields exactly

    d>0 and y>=d/2.                                    (12)

At y=d/2 every finite batch is legal and the spectator first reaches the common limiting location only at the accumulation time. No continuation through that time has been specified or certified. All three core signals accumulate at space-time (d/2,d/2); the spectator's limiting location is y, which equals d/2 precisely on the boundary.

The full return matrix in (9) has eigenvalues 1/4 and 1, so spectral radius 1. Nevertheless every input in (12) is Zeno with T=d/2: the neutral spectator-gap coordinate is invisible to the clock. This is an explicit signal-realizable counterexample to the unsound test "Zeno iff the whole return matrix has spectral radius <1".

There is no finite repetition bound, depending only on this fixed machine and macro, whose successful prefix test certifies infinite validity for all rational/integer seeds. For any K>=0 choose d=4^(K+1) and y=d/2-1. Then the first K cycles are legal but the (K+1)-st is not: its endpoint threshold is d/2-1/2, greater than y. K=0 is the valid empty prefix; the first proposed bounce then has a competing tie. The eventual failure is a genuine additional R-S collision.

For positive integer d,y the entire infinite-validity set (12) already has the elementary unique-witness quadratic

    (2y-d-z)^2=0,  z in N.

This small polynomial is an example, not the source of the general quartic theorem. The shrinking-wall shuttle itself is classical; the spectator, limiting-boundary comparison, and spectral-observability warning are used here to expose the exact scope of the new certificate class.

## 8. Rational accumulation limits in every finite dimension

Retain any fixed finite population and a valid repeated macro, with gap return matrix M and rational initial vector x. Let f_n=ell M^n x. Its generating function is the rational function

    F(z)=ell(I-zM)^(-1)x in Q(z).

If sum f_n converges, Abel's theorem gives lim_(z->1-) F(z)=sum f_n. A rational function with rational coefficients that has a finite limit at the rational point 1 has a rational limit: cancel the common powers of z-1, then evaluate a ratio of rational polynomials. The limit is effectively computable by polynomial arithmetic. This proves rationality of the accumulation time conditional on valid summability, without asserting that summability or validity is automatically recognized in every dimension.

For positions, number conservation permits the k-th spatially ordered signal position X_k(t) to be followed continuously through a collision: all replaced positions at the site agree. Because the set of speeds is finite, each X_k is V-Lipschitz on every finite prefix, for V=max|speed|. If T is finite, each X_k(t) has a limit as t approaches T from below, and every gap has a limit as well.

The displacement of X_1 over macro n is r M^n x, and its absolute value is at most V f_n. Its series therefore converges absolutely. The same rational-generating-function argument gives a rational total displacement. Each component of M^n x has a limit. For any convergent rational-matrix sequence h_n, Abel summation gives

    lim h_n = lim_(z->1-) (1-z) sum h_n z^n,

again a finite limit of a rational function over Q, hence rational. Thus all limiting gaps and all limiting ordered positions are rational. Any fixed named site inside the macro differs from the appropriate macro-boundary position by at most V times that macro's duration, which tends to zero. Its limit is consequently one of these rational positions. An ultimately periodic prefix contributes only finitely many rational positions/times before the repeated part and changes none of the conclusion.

This proves Theorem C. The signal-machine literature permits much more general accumulation coordinates; this theorem is an obstruction to describing those examples by a finite exact periodic macro, not a contradiction of that literature.

## 9. Literature, novelty boundary, and remaining work

- Repository pin: e3e58a8820593857650bb7a0193a11ec32db67d6, checked 4 October 2026. The signal-machine report's Parts I-II give rational linear chambers for **finite** complete schemas, including ties, and explicitly disclaim accumulation semantics. Its independent review states that a physical-time bound is not an event bound. The present construction re-proves the special conservative one-macro chamber needed here and extends a supplied periodic word to all repetitions.
- Becker, Chapelle, Durand-Lose, Levorato and Senot, *Abstract Geometrical Computation 8: Small Machines, Accumulations & Rationality*, arXiv:1307.6468v1, Definition 1 and Sections 2.1, 3.1. The distinct-speed rule convention and the shrinking-wall shuttle are standard. Four **speeds** in that paper must not be confused with four simultaneously live **signals** here. The example above has five speed values after adding its spectator.
- Ouaknine and Worrell, *Positivity Problems for Low-Order Linear Recurrence Sequences*, arXiv:1307.2779, especially Section 6 on strictness. Low-order positivity is established mathematics, and strict versus non-strict variants cannot be conflated in higher-order citations. The elementary order-two formulas here are proved in full and used as a compiler; no novelty is claimed for deciding order-two recurrence signs.
- No claim of an optimal population bound is made. Above four signals the return section gives larger-order recurrence guards. Established low-order results can sometimes give additional decidability, but they do not by themselves supply this degree-two sign formula or justify arbitrary-dimension finite spectral tests. No faithful reduction from arbitrary Positivity instances to collision macros is asserted.
- Targeted repository searches for "periodic collision" and "collision word" found no matches. This is a bounded duplicate check, not an exhaustive literature novelty search. Existing exponential-trajectory certificates and finite-prefix collision geometry were inspected as neighboring work.

Primary and repository links:

1. https://github.com/VladimirReshetnikov/ProveIt/blob/e3e58a8820593857650bb7a0193a11ec32db67d6/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/README.md
2. https://github.com/VladimirReshetnikov/ProveIt/blob/e3e58a8820593857650bb7a0193a11ec32db67d6/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/incoming_signal_review_808b.md
3. https://arxiv.org/html/1307.6468v1
4. https://www.cs.ox.ac.uk/james.worrell/pos12.pdf
5. https://arxiv.org/abs/1307.2779

Remaining engineering work is a general parser/emitter from an arbitrary supplied machine+macro to its chamber rows and the quartic DAG. The mathematical construction is explicit; this packet does not claim that general frontend has been implemented. The accompanying new arithmetic checks exercise the order-two formulas, sign-witness gadget and the displayed return-map identities; they are not a physical simulator, do not execute a stored schedule, and are not a substitute for the proofs.
