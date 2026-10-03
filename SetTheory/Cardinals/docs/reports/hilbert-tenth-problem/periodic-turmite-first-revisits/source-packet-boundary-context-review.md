# Independent audit: one-visit turmite decision boundary

## Verdict

The proposed total first-position-revisit procedure is sound after the timing invariant and the exact scope of the first-hit corollary are made explicit. I found no mathematical obstruction. The no-revisit branch admits the claimed exact finite-pattern/heading/congruence first-hit algorithm, and in fact finite head-relative colour observations alone are eventually periodic with the head's cycle length.

The following are qualifications rather than counterexamples:

1. The no-revisit first-hit theorem does not decide an arbitrary target after a first revisit has occurred. On a collision branch it can decide targets only up to and including the collision arrival, unless another argument is supplied.
2. Eventual translated periodicity is a statement about the head path. It is not generally a translated periodicity of the complete infinite board configuration.
3. History must contain positions at strictly earlier times than the current restart. A defect arrival is appended once, before restarting after its departure.
4. Presburger quantifier elimination should be stated in the language augmented with fixed-modulus congruence/divisibility predicates.
5. No complexity bound or novelty claim follows merely from the decision proof.

## 1. Static-shadow lemma and time convention

Write the configuration at integer time t before departure as (p_t,h_t,c_t). At time t the colour at p_t determines a quarter-turn, that cell is incremented modulo m, and the head moves one unit in the new direction.

Let B_0 be the initial board, given by a u-by-v periodic board B with a finite override map D. Until the first position repetition, every departing cell has not been departed from previously. Therefore its current colour is B_0(p_t). The actual head trajectory consequently agrees with the static deterministic walk which consults B_0 but never changes it.

More precisely, if t* is the first repeated-position arrival, agreement holds for p_t and h_t through t=t*. The colour identity

c_t(y) = B_0(y) + 1_{there exists s<t with p_s=y} modulo m

also holds through t=t*. It generally ceases to hold after the departure at t*.

The hypothetical background excursion reads B, not B_0. Its trajectory is valid until its first arrival at D or its first repeated position, whichever comes first. Looking for events later in the hypothetical excursion is harmless because the algorithm selects the minimum event time.

## 2. Improvement: every background excursion is a pure affine cycle

On Q=(Z/uZ)x(Z/vZ)x{N,E,S,W}, define the background map

F(p,h)=(p+R_{B(p)}h, R_{B(p)}h).

It is a permutation. Given the successor (p',h'), the predecessor position is p=p'-h', and the predecessor heading is h=R_{B(p)}^{-1}h'. Thus no transient is required: the projected trajectory from every restart is periodic from its first state, with period L at most 4uv.

Lift one period to Z^2. For phase i in {0,...,L-1}, let P_i and H_i be its lifted position and heading, and let delta be the displacement after L steps. Then

p_{r+i+nL}=P_i+n delta,
h_{r+i+nL}=H_i,

for n>=0 in the hypothetical excursion. The displacement lies in uZ x vZ, because the projected cycle returns to the same residue and heading. Keeping a transient-plus-cycle presentation is still correct, but the permutation argument simplifies both the representation and proof.

If delta=0, a position collision occurs by time r+L. A no-event certificate therefore necessarily has delta!=0.

## 3. Exact history ownership

Maintain this invariant at a restart time r:

- The compressed history contains exactly the positions and headings at times 0<=s<r
- Those historical positions are distinct
- The current p_r is not included in history, and is not assumed fresh until collision checking at r
- The head state at r is the true state

For the new hypothetical background excursion, find the earliest of:

A. A visit to a point in D
B. An intersection with the historical positions
C. A self-intersection within the new excursion, with the other occurrence strictly earlier

If a collision and defect arrival tie, return the collision. This includes revisits to previously processed defects.

If the earliest event is a fresh defect arrival at time d, append the positions at r<=s<=d, using the background excursion formulas clipped at d. Execute the departure from that defect using B_0(p_d), and restart at r=d+1. The enlarged history is now exactly the positions at times s<r. In particular, the defect is appended once; the next current position is excluded until the next stage.

At a fresh defect event the position cannot be one of the previously processed defects, because that would be a history collision. There are therefore at most |D| successful defect departures and at most |D|+1 hypothetical-excursion analyses. If no event exists, the current infinite excursion is correct forever, avoids D, is injective, and avoids history.

## 4. Lane intersection and earliest-time minimization

A lane has position b+n v and time a+n tau, with tau>0 and integer index 0<=n<=N; N may be infinity. A singleton can be represented with N=0. A clipped phase lane at a defect event d has upper index floor((d-r-i)/L), and is omitted if that bound is negative.

Compare a new lane i with an older lane j. Solve

v_i n - v_j m = b_j-b_i,
0<=n<=N_i,
0<=m<=N_j,
a_j+tau_j m < a_i+tau_i n.

The final inequality matters for within-excursion pairs and excludes comparison of a time with itself. It is redundant but harmless when lane j belongs to history. Test every ordered phase pair, including a lane paired with itself.

Set A=v_i, B=-v_j, c=b_j-b_i.

### Rank 2

If det(A,B)!=0, the only rational solution is

n=det(c,B)/det(A,B),
m=det(A,c)/det(A,B).

Require both to be integers and check all bounds and the strict-time inequality. If valid, its new time is the only candidate for this pair.

### Rank 1

First check c is collinear with the nonzero columns. Choose a coordinate in which a=A_coordinate and b=B_coordinate are not both zero. The vector equation is then equivalent to a n+b m=c_coordinate.

Let g=gcd(|a|,|b|). If g does not divide c_coordinate there is no solution. Otherwise extended Euclid gives a particular solution (n0,m0), and all solutions are

n=n0+(b/g)k,
m=m0-(a/g)k,

for integer k. The index bounds and strict-time inequality become finitely many one-variable linear inequalities in k. Their conjunction is an explicitly computable integer interval, possibly empty or unbounded. Minimize a_i+tau_i n over that interval by selecting the appropriate endpoint, or any feasible k if the objective is constant. If the objective is nonconstant, its minimizing direction cannot be unbounded while n>=0, since tau_i>0.

This treatment includes the case in which exactly one spatial step vector vanishes.

### Rank 0

Both spatial step vectors vanish. If c!=0 there is no intersection. If c=0, the earliest old time is a_j (indices start at zero). The least new index is

max(0, floor((a_j-a_i)/tau_i)+1),

provided it respects the new upper bound and both lanes are nonempty. This explicitly handles the strict-time inequality and candidate zero-drift cycles.

### Defect intersections

For a defect point d, solve b+n v=d with the lane bounds. If v=0, equality of b and d gives minimum n=0. Otherwise use a nonzero coordinate of v to determine n, require integrality, and check the other coordinate and bounds.

Taking the minimum new time over finitely many point and lane candidates gives an exact event time and coordinate. Before the first collision there is at most one genuinely earlier occurrence of its coordinate; returning that earlier witness is optional but straightforward.

## 5. Presburger first-hit extension

On the no-revisit branch the complete time-position-heading graph is a finite disjunction of bounded affine lanes and the final unbounded affine phase lanes. Every relation in this graph is Presburger-definable: multiplication is only by fixed integer coefficients.

The initial colour predicate B_0(y)=j is a finite disjunction of defect point equalities and periodic residue conditions, with the periodic clause explicitly excluding D. Define

VisitedBefore(t,y) := exists s (0<=s<t and Position(s,y)).

Then colour j at time t is expressed as the disjunction of

- B_0(y)=j and not VisitedBefore(t,y)
- B_0(y)=j-1 modulo m and VisitedBefore(t,y)

This remains correct for m=1. A finite head-relative pattern is obtained by setting y=p_t+f for each fixed offset f. If offsets are relative to the head's orientation, use the finite disjunction over the four headings and rotate each offset accordingly.

One may conjoin finite absolute-site colour conditions, heading tests, and coordinate or time congruences with fixed input moduli. Arbitrary finite Boolean combinations are still Presburger formulas. This establishes a formula Hit(t).

First decide exists t>=0 Hit(t). If false, report never. If true, the least t can be obtained either by increasing enumeration, which now is guaranteed to terminate, or by exponential search for a bound B satisfying exists 0<=t<=B Hit(t), followed by binary search for the minimum bound. Thus no separate integer-optimization theorem is needed.

On a collision branch, restrict t<=t* for a valid bounded-prefix first-hit result. An unrestricted negative answer about all future times is not justified on that branch.

## 6. Stronger eventual-periodicity statement and elementary proof

Let the final tail begin at T, with

p_{T+i+nL}=P_i+n delta,

where delta!=0 and delta lies in uZ x vZ. Fix phase i and finite offset f. The observed site is Y_n=P_i+f+n delta.

### Initial colours

Its periodic-background colour is independent of n. The line Y_n hits any fixed defect at most once because delta!=0. Thus its actual initial colour is eventually constant in n.

### Earlier finite history

The finite pre-tail history can contain Y_n for only finitely many n. This is effective even if that history is huge: in any coordinate where delta is nonzero, take the minimum and maximum of the finite-history lane endpoints and all defect coordinates. Beyond a computable n, the moving observation point is outside that coordinate range.

### Visits from the infinite tail

A tail visit in phase j and index k satisfies

P_j+k delta=P_i+f+n delta.

Equivalently, P_j-P_i-f=d delta with d=n-k. If the fixed vector on the left is not an integral multiple of delta, there is no such visit. Otherwise d is unique, k=n-d, and the strict-past condition is

j-i-dL<0.

It is independent of n. Existence is therefore either always false or a threshold condition n>=max(0,d). Taking the maximum threshold over finitely many phases and offsets proves that the visited-before bits are eventually constant for each phase.

Consequently every fixed finite head-relative colour observation, together with heading, is eventually L-periodic in absolute time. Finite absolute-site colour observations also stabilize, since each fixed site is visited at most once.

Additional fixed-modulus coordinate/time congruences add a computable finite period in n. For a congruence of a linear form ell(p_t,t) modulo q, its value changes between consecutive cycles by the fixed amount ell(delta,L); a valid period is q/gcd(q,ell(delta,L)). The lcm of these periods works simultaneously. Therefore the complete allowed event predicate is effectively ultimately periodic.

This gives an elementary alternate first-hit proof: compute a sufficient threshold and period, examine the finite exceptional prefix and one eventual period. It establishes total computability, not a practical complexity bound. Presburger reasoning is usually cleaner when a compressed output rather than a potentially enormous scan is desired.

## 7. Literature and overlap check

A targeted web search did not uncover a direct published first-position-revisit theorem for finite-defect periodic turmites. This is not a comprehensive novelty search.

The main relevant primary source is Maldonado, Gajardo, Hellouin de Menibus and Moreira, [Nontrivial Turmites are Turing-universal](https://arxiv.org/pdf/1702.05547), arXiv:1702.05547 (2017). Their formal rule matches the departure convention here. Their universality construction uses a periodic background with finite input-dependent perturbation; the discussion in §5, printed p.18, states that the construction uses each cell at most twice. This supplies relevant context for a one-visit/two-visit boundary, but their universal construction is not itself a theorem that every prescribed target property is undecidable under every visit promise. A reduction must still connect the chosen target to simulated computation.

A primary constructive source for the logical ingredient is Marcus Kracht, [A New Proof of a Theorem by Ginsburg and Spanier](https://wwwhomes.uni-bielefeld.de/~mkracht/html/presburger.pdf), December 18, 2002, Theorems 2.9–2.10. It proves quantifier elimination using congruence predicates and the equivalence between Presburger-definability and semilinearity. The original cited semilinearity paper is Ginsburg and Spanier, “Semigroups, Presburger Formulas, and Languages,” Pacific Journal of Mathematics 16 (1966), 285–296.

No repository was identified or inspected, and no external code was cloned or executed.

## Final assessment

Recommended theorem wording: for every explicitly encoded finite cyclic turmite and periodic board with finitely many defects, a total algorithm either returns the exact first repeated-position arrival or certifies no repeated position and returns a finite affine-lane description of the entire trajectory. In the latter case, the first occurrence of any specified finite head-relative colour pattern, heading constraint, finite absolute-site colour conditions, and fixed-modulus coordinate/time congruences is decidable and has an exactly computable least time. The associated truth sequence is effectively ultimately periodic.

## Final completed-proof and implementation review

Reviewed the completed `proof.md` and `one_visit.py` on 2026-10-03, including the added colour-query domain guard and compressed excursion/cut certificate description. No mathematical error was found in the theorem or its proof, and the independent executable checks found no implementation discrepancy.

### Items checked

- **Operation count.** At stage j, with j completed defect departures, there are at most S new lanes and jS historical lanes. The ordered internal/history comparisons cost at most (j+1)S² calls, and the defect comparisons at most SK. Summing j=0,...,K gives exactly the stated upper bound S²(K+1)(K+2)/2+SK(K+1). The (K+1)S successor-step and compressed-lane bounds also hold. These are deliberately not bit-complexity claims.
- **Endpoints.** History contains exactly s<r. A successful defect segment is clipped inclusively through F, followed by the exceptional departure and restart at F+1. Collision time is included in the output domain, but its departure is excluded. This matches the code.
- **First-hit formula.** Equations (3)–(5) use only fixed-coefficient integer arithmetic and fixed moduli. Past visitation correctly excludes the current and future arrivals. Negated visit tests are legitimate Presburger formulas. Existential occurrence, exponential bracketing and bounded-existence binary search establish an exact least time. The general first-hit solver is clearly identified as proved but unimplemented.
- **Eventual bound.** Both signs in the finite-exception threshold are correct. The tail equation gives k=n-d, and its strict-past condition is j-i-dL<0. Taking maxima gives a sufficient threshold without expanding the finite history. Coordinate congruences add the stated lcm period. Optional finite head-position restrictions vanish eventually.
- **Scope.** The proof consistently confines unrestricted future queries to the certified no-revisit branch. It does not claim global board translation-periodicity, physical halting, novelty, a verified literal two-visit loader, or a general post-collision query procedure.
- **Code.** The rank-two determinants, rank-one parameter interval inequalities and rank-zero chronological ceiling all match the proof. Time minimization is index minimization because every lane period is positive. The new `visited_before` domain guard also protects `colour_at` from negative and post-collision queries.
- **Certificate clarity.** For an independently checked path certificate, verify each clipped excursion has no defect hit before its cut and that the final tail avoids D, in addition to checking local cycle transitions and position disjointness. These checks are already supplied by the event primitive. The prose can make this explicit. Empty threshold maxima and lcms may conventionally be taken as 0 and 1.

### Independent executable checks

The independent checker is retained as `review_checks.py`, with its output in `review-check-results.txt`. It does not edit the implementation.

All checks passed:

- 30,000 randomized lane-pair instances, including bounded and unbounded lanes, zero and nonzero spatial steps, negative coefficients/coordinates/times, and both chronological and static-point semantics
- 1,200 independently generated random turmite instances with 1–6 colours, tiles up to 5-by-5, finite defects, arbitrary tested headings and negative starts
- 146,844 head position/heading comparisons against direct evolving-board simulation
- 89,796 colour comparisons against the independently updated board

For bounded new lanes the lane oracle enumerates all admissible new indices. For an unbounded new lane it checks every index through 2,000; any returned witness is separately validated, and an alleged larger minimum is accepted only if no smaller enumerated witness exists. This is a randomized regression check, not a proof of all unbounded arithmetic cases. Turmite simulations compare through the first reported repeat or the 1,000-step observation horizon. The theorem, not a finite simulation, establishes a no-revisit conclusion.

### Final citation check

The earlier suggestion in this audit to use Kracht as the algorithmic source is superseded. I downloaded and rendered the actual Kracht PDF. Its printed p.8 contains the reversed lower/upper bounds in the final interval-congruence elimination display, as well as the related prose-index typo. These are real printed errors rather than an OCR artifact. They do not undermine standard Presburger decidability, but that display should not be used verbatim as an implementation specification.

I successfully downloaded the primary scan of D. C. Cooper, [Theorem Proving in Arithmetic without Multiplication](https://www21.in.tum.de/teaching/logik/SS16/Exercises/Cooper.pdf), Machine Intelligence 7 (1972), 91–99, and visually read printed pp.92–95. Page 92 specifies the integer language with fixed divisibility and explains iterative quantifier elimination. Pages 94–95 give the finite residue/boundary disjunction and its correctness argument. Cooper is a suitable replacement citation for the sole external logical ingredient used here. The turmite paper's author names and cited scope remain correct.

### Final verdict

The completed lower-side result is established as stated. The reference implementation supports accelerated first-revisit decision and certified-domain snapshots/colours; it does not purport to implement the general first-hit quantifier-elimination subroutine. No blocking issue remains.

Final verification: the proof now explicitly checks defect avoidance before each cut and along the final tail, and defines the empty maximum and lcm as 0 and 1. Both minor clarity suggestions are resolved.

Reviewed final implementation SHA-256: dcfbb782b4396aca7b486f12b80e48c86458d3ed8fe8a03357ab7653ab820bd6.
