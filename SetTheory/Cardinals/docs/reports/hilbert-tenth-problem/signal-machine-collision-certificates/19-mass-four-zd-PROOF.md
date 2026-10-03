# Four mass units in every finite spatial dimension

Research proof source, 3 October 2026. This delivery copy replaces only environment-specific provenance paths with report identifiers. See Report 29 for the typeset exposition. This is an effective mathematical decision argument, not a claim of priority, an implemented general CA compiler, or a proof-assistant formalization. The literature record is separate in `literature.md`.

## Result

Let d≥1 be finite. Let F be a deterministic, translation-equivariant, finite-range cellular automaton on Z^d over a finite alphabet A. Let 0 be its quiescent vacuum, with w(0)=0 and w(a) a strictly positive integer for a≠0. Assume finite total mass is conserved and at most one alphabet symbol has weight one.

**Theorem.** For every finite input c of mass at most four, one can effectively decide:

1. Whether a specified finite configuration is F^t(c) for some integer t≥0
2. The same question up to translation
3. Whether a specified finite pattern occurs in a specified finite window at some time, or occurs at some translation at some time

Patterns may prescribe zeros, which are enforced. The procedure is effective from d, the finite local rule, a finite neighborhood bound, weights and the input, under the hypotheses. In particular the result holds in every fixed finite spatial dimension. It does not require reversibility.

The proof also gives an effective, fixed-input Presburger description of the untimed orbit in the frame that fixes isolated unit particles. Its alternatives are independent finite-phase objects, a whole configuration periodic up to translation, or a one-counter expanding shuttle with quadratic section times. It makes no assertion of uniform timed Presburger definability.

The proof extends the one-dimensional Report 12 argument. The additional geometric step needed for this extension is §6: successful flights lie on exact lattice arithmetic rays, and a switch to a nonparallel ray forces a bounded full configuration. Missing a marker is a terminal alternative, and must not be ruled out by a one-dimensional crossing argument.

## 1. Metric, normalization and independence

Use the maximum norm ||x||∞ on Z^d. A radius bound R means that every output at x depends only on x+[-R,R]^d. Write diam(c)=max{||x−y||∞:x,y in supp(c)}. Normalize a nonempty configuration by subtracting its lexicographically first occupied site. This normalization commutes with translation.

If a unit symbol u exists, an isolated u must evolve to one u at a displacement δ∈Z^d, ||δ||∞≤R: conservation and positivity leave no other mass-one output. Set G=τ_(−δ)F and S=max(1,R+||δ||∞). Then G has radius at most S, fixes every isolated u, and F^t=τ_(tδ)G^t.

Join occupied sites at maximum-norm distance at most 2S. A component of mass m has at most m sites, hence diameter at most 2S(m−1). Different components at distance greater than 2S have disjoint radius-S input influence neighborhoods. Their one-step evolutions are independent and have disjoint output supports. Until the first time independently evolved components have distance at most 2S, the independent evolution equals the full evolution. Equality holds also at that first-contact configuration; the step after contact is resolved by the full rule.

Every configuration of bounded diameter and mass at most four belongs to a finite effective list modulo translation. Its finite successor can be computed by evaluating the local rule on the finite S-neighborhood of its support.

## 2. Mass-two packets remain bounded

**Lemma 2.1.** A mass-two configuration of diameter at most 2S remains within that diameter under G and has an effective eventually periodic profile up to translation.

A weight-two singleton has next support within its radius-S cube, of diameter at most 2S. Otherwise the configuration consists of two u's at 0 and v, ||v||∞≤2S. If ||v||∞>S, each original site sees just its own isolated unit and therefore stays u. These two sites exhaust the mass and the configuration is fixed.

If ||v||∞≤S, every newly occupied site other than the two originals must see both units: a neighborhood seeing zero or one unit has the corresponding vacuum or stationary-singleton output. The intersection of the two radius-S cubes contains both original sites and has each coordinate width 2S−|v_i|≤2S. Hence the complete successor support is inside this intersection and has diameter at most 2S.

Normalize shapes. There are finitely many, and each shape has a determined next normalized shape and translation increment. Repetition yields a finite transient and then

    P(r+kp) = kD + P_r,   0≤r<p, k≥0,

after shifting the time origin to the periodic part. Here D∈Z^d and all finite phase shapes P_r are explicit. A separated pair of units farther than 2S is fixed. All weighted dimer symbols, pair shapes and phases are included; no binary-only assumption is made.

## 3. Effective mass-three profiles

**Lemma 3.1.** Every fixed mass-three input has an effective finite prefix followed by either a whole configuration periodic up to one vector translation, or an independent stationary unit and a mass-two finite-phase packet. Three separated units are a constant special case.

Take as core every normalized mass-three configuration of diameter at most 4S. Outside this finite core, the component partition is 2+1 or 1+1+1. In the latter case everything is stationary. In the former, apply Lemma 2.1 to the dimer. In every eventual phase the complete occupied coordinates have the form p+kD for finitely many offsets p, and one fixed unit. Membership in the diameter-4S core is a finite conjunction of coordinatewise linear inequalities in k. Find the least k in each phase satisfying them, then the earliest corresponding time, after checking the finite transient. This is a finite integer interval calculation. If there is no core return, there can be no later contact, because a dimer-unit contact is connected and has diameter at most 4S.

From each core state take one exact step and, when necessary, the just-computed first return. This is a finite deterministic graph of normalized core returns, labeled by finite elapsed times and translation vectors, with terminal independent tails. Repetition of a normalized core state gives equality of two complete configurations up to translation. Determinism and equivariance propagate that equality to every later time, including intermediate excursions. This gives the claimed profile effectively. A finite period may be enormous; it can still be enumerated.

Consequently mass at most three has a fixed-input timed Presburger description in every d, also after restoring the drift δt.

### A finite local encounter library

Let E be every normalized connected mass-three configuration. It is finite, since its diameter is at most 4S. A dimer's first contact with a unit is one such seed. Record, as a finite bookkeeping tag, which coordinate was the incoming target unit. The tag records a geometric role; it is not an additional CA symbol or physical identity.

For each tagged seed compute Lemma 3.1's profile and extend a finite prefix until one of these checkpoints:

- **Compact:** the whole triple is periodic up to translation, with finitely many bounded phase shapes
- **Emission:** one stationary unit remains, and an independent bounded dimer has a nonzero drift D and is thereafter never within 2S of the remaining unit

An independent dimer with D=0 makes the complete triple eventually periodic, so belongs to Compact. With D≠0, one coordinate of D is nonzero, so the finite prefix can be extended effectively until every future phase stays beyond the contact box on that coordinate. This yields Emission, with a purely periodic dimer profile whose launch offsets relative to the residual unit are fixed finite data.

Choose B to bound all occupied offsets in every finite seed prefix, every compact phase representative, and every emission's initial-period phase representative, together with the residual-unit offsets. There are finitely many such data. B is computed exclusively from the original diameter-4S seed library, before choosing the mass-four core. In particular this construction is noncircular. Compact phase diameters are at most 2B.

## 4. Compact triples cannot carry a second unbounded gap

Place a library seed at a and a fourth unit at b with ||b−a||∞>B+2S. The entire precomputed prefix through its checkpoint stays independent of that unit. At an emission the old remote unit stays put and the nearby residual marker changes by a fixed, seed-dependent vector.

For a compact outcome, compute its first contact with the fourth unit by enumerating phases and solving the coordinatewise linear inequalities for distance at most 2S from an actual occupied site. It can miss the unit, even with nonzero drift; if so it is a terminal independent profile. If contact occurs, the full configuration has diameter at most 2B+2S. Thus an arbitrarily long trip of a translating triple ends either in a terminal tail or a bounded full encounter. It cannot continue to carry two independent unbounded gaps.

This argument includes triples that detach and recombine during their periodic orbit. Every phase of that entire orbit was retained in the compact profile, so its diameter has a fixed bound.

## 5. Exact arithmetic rays for successful dimer flights

At an emission checkpoint put the source residual unit at 0. Let the dimer profile be

    Q(r+kp) = kD + Q_r,   D≠0, 0≤r<p, k≥0.

The packet never meets its source again in this isolated profile. For a target unit at v, its contact at time r+kp is exactly

    v = a + kD

for some a in the finite set Q_r+[-2S,2S]^d. Retain r with a; multiple occurrences are harmless. This is an exact support test, not a hull approximation.

Thus successful marker vectors are a finite union of lattice arithmetic rays. If there is no solution with k≥0, the full future consists of this packet and the two stationary markers and is terminal. All earlier times are independently described. If several candidates exist, minimize the actual integer time r+pk; this handles phase ties and simultaneous contact sites.

Write D=mν, where ν is the primitive integer vector on its unoriented line, chosen with first nonzero coordinate positive, and m is a nonzero integer. Compute an integer linear functional λ with λ(ν)=1, using Bezout coefficients of ν's coordinates. Every vector v has the unique decomposition

    v=nν+z,   n=λ(v), z=v−λ(v)ν, λ(z)=0.

For an offset a write l=λ(a), z_a=a−lν. The contact candidates become

    z=z_a,   n≡l (mod |m|),   k=(n−l)/m≥0,
    time=(p/m)n + r−(p/m)l.

For |n| greater than the maximum |λ(a)| and on the drift-facing sign, all candidate k are nonnegative. The eligible candidates and the earliest constant term then depend only on the finite transverse offset z and n modulo |m|. On the opposite sign there is no candidate.

The entire contact seed, tagged by the target coordinate, is also determined by these finite data: relative to target v, the dimer shape is Q_r−a. Ties at one actual time describe the same complete configuration; choose a fixed enumeration tie-break if a unique bookkeeping witness is desired. Resolve the seed by the precomputed library.

All flight phases are retained: coordinates are affine in the marker vector and one integer period variable k, with a linear precontact-time bound. All local-prefix phases are retained as well.

## 6. Nonparallel switches are confined to an effective bounded set

An emitted dimer from marker A hits the other marker B. At its next emission the contacted marker is B+c, where c belongs to a finite library of marker-update vectors C. The old source A remains stationary. For the incoming marker vector v=B−A and the next outgoing target vector v', therefore

    v'=A−(B+c)=−v−c.

Suppose both flights successfully cross between the two markers, with respective nonzero drift vectors D and D'. Section 5 yields

    v=a+kD,   v'=a'+k'D',   k,k'≥0,
    kD+k'D'=−(a+a'+c).                         (6.1)

Here a,a',c range over finite effective sets.

**Lemma 6.1.** If D and D' are nonparallel, the set of possible v in (6.1) is finite and effectively computable.

Choose coordinates i,j with determinant D_i D'_j−D_j D'_i≠0. For each finite right-hand side, the i,j equations have at most one rational pair (k,k'), obtained by Cramer's rule. Retain it only if both entries are nonnegative integers and every remaining coordinate equation holds. Then compute v=a+kD. There are finitely many inputs to this calculation, so the full exceptional set is finite. This proves an effective bound without an asymptotic-angle argument.

In particular, outside a computable bound, every continuing live excursion uses one fixed unoriented rational line. An outgoing nonparallel packet that misses the old marker is terminal, not a new counter mode. A compact triple is handled by §4 and resets to the bounded core or is terminal.

## 7. A finite-control one-counter section, with vector output

For every primitive line ν present in the emission library fix one λ as above. Order the two markers by their λ coordinates, calling the smaller L and the larger R. This is only a bookkeeping order on this line; it is not a global order on Z^d. Write

    R−L=xν+z,   x=λ(R−L)>0, λ(z)=0.

For a successful long flight, z belongs to the finite set consisting of all ±(a−λ(a)ν) for contact offsets a from profiles on this line. The sign depends on which marker is the source. The mode records the line ν, source side, complete emission profile and launch shape, this transverse offset z, and any seed tag needed by the library.

### Choosing thresholds effectively

Choose a common positive integer N, or line-specific integers if preferred, sufficiently large to dominate the following finite lists:

1. Every |λ(a)| in a contact candidate, so the large-gap formulas of §5 hold
2. Every |λ(c)| for a marker update, so changing the contacted marker cannot reverse its λ order
3. Every |λ(v)| for the exceptional nonparallel-switch vectors of §6
4. A safety bound ensuring that x>N implies the remote marker is farther than B+6S from an incoming target seed anchor. For example impose N>max_λ ||λ||_1(B+10S+1), since |λ(v)|≤||λ||_1||v||∞

All these quantities depend only on the finite seed/phase libraries. Enlarge N further when needed for a finite launch offset; this is a finite explicit maximum, not an iteration over a new core.

Now choose W larger than 6S, B+6S, 2B+2S and the diameter of every successful emission launch with 0<x≤N. The last collection is finite: ν and z range over finite lists, x ranges over {1,…,N}, and the packet launch shape has fixed finite offsets. Include any finite small or degenerate-sign successful cases from the contact formulas. Thus W is effectively computable after N, with no circularity.

Call configurations of diameter at most W ordinary. At designated emission checkpoints use the live representation if the next cross-marker flight succeeds and x>N; otherwise use ordinary if its diameter is at most W, or its explicit terminal independent profile if that flight misses. At other dispatch states test the ordinary condition first. Ordinary and tagged-live sets may overlap, and this convention is part of the decision algorithm, not extra CA memory.

### Transition form

On a live-to-live edge, §6 prevents a nonparallel line change. Only the contacted marker changes by c. Its λ order is unchanged. Hence

    x'=x+c_0,   L'=L+e,   z'=z+c_perp,

for constants selected from a finite effective list; e is an integer vector, not another control counter. The exact first-contact seed depends only on mode and x modulo |m|. Add the seed's fixed prefix duration to the flight time. Taking M as the least common multiple of the positive integers |m| of all emission drifts gives

    q'=f(q,x mod M),
    x'=x+c_0,  L'=L+e,  h=αx+β,               (7.1)

where α=p/|m|>0 is rational and h is a positive integer on the allowed residue class. The transverse offset has been folded into q.

There is no additional clock that controls the dynamics: the CA is time-independent, residual units are stationary, and every moving packet's internal phase is already in q. Absolute anchor L and accumulated time are outputs. The vector L does not affect the next mode or counter increment.

An emission whose resulting successful gap has x'≤N has bounded full diameter and resets to ordinary. A compact outcome is accelerated by §4 to ordinary or terminal. An outgoing emission that will not hit the other marker is terminal. The choice to continue live, take an emission miss, or exit through a compact outcome depends on finite mode/residue data for x>N, except for the explicit lower-bound guard after bounded counter updates. Whether a compact exit subsequently hits the remote marker is decided separately by its exact phase calculation; it is never treated as another live edge.

## 8. Complete dispatch from arbitrary mass-four inputs

The 2S-component mass partitions are

    4; 3+1; 2+2; 2+1+1; 1+1+1+1.

- A connected mass-four state has diameter at most 6S and is ordinary
- Four monomers are fixed
- For 3+1 outside the ordinary core, the connected triple seed and the fourth unit satisfy the safety bound because its seed diameter is at most 4S and W>B+6S. Apply the library and §4
- For 2+2, combine the two finite transients and their phase periods. In each common phase, relative occupied coordinates are affine in one integer period variable. The first distance-at-most-2S event is the minimum over finitely many coordinatewise interval tests. If absent the tail is independent. At contact both packet diameters are at most 2S, so the total diameter is at most 6S and is ordinary
- For 2+1+1, compute the packet's first contact with either monomer using §5, including a finite transient if needed. If absent, the tail is independent. A simultaneous contact with both produces a connected mass-four state of diameter at most 6S. Otherwise it forms a tagged triple seed. If the full state is ordinary reset there; if not, the distant remaining unit satisfies the safety condition and apply the library

This dispatch includes contacts with multiple sites, ties between markers, and packet phase ties. It uses actual supports and compares actual times. It never assumes a moving object hits a marker merely because some coordinate moves toward it.

From any ordinary state take one exact CA step before dispatch. This gives a positive-time edge for each of the finitely many normalized ordinary states to an ordinary state, a live checkpoint, or a terminal profile. All intervening configurations have an effective finite-phase description. A live edge includes a positive-length flight because its target is safely distant. Zero-time section loops are absent.

## 9. Termination of the analysis and the orbit normal form

Enlarge q by x modulo M. Follow the effective section machine from the given input.

If a normalized ordinary state repeats, two complete configurations are translates. The whole future is periodic up to translation, at all intermediate times.

Within one uninterrupted live excursion, the unoriented line is fixed and there are finitely many enlarged modes. At a repeated mode let Δ be the scalar-counter change. Since the residue is included, Δ is divisible by M and a repeated cycle has exactly the same residue itinerary.

- If Δ=0, the whole launch configuration repeats up to the anchor translation; the entire future is periodic up to translation
- If Δ>0, every intermediate lower-bound guard remains valid for every later cycle and the same transition itinerary repeats forever. This is an expanding shuttle
- If Δ<0, compute the greatest number of full cycle repeats for which every intermediate counter exceeds N. This is a finite collection of linear inequalities. Execute or accelerate those repeats, then the finite residual cycle prefix exits the live region to an ordinary state or a terminal profile. An exit from live mode would already have occurred in the first cycle, since the choice to continue live above N depends only on enlarged mode

There are only finitely many normalized ordinary states. Therefore this algorithm terminates with a finite prefix and one of:

A. Independent finite-phase objects
B. A whole configuration periodic up to translation
C. An expanding shuttle

The procedure is effective even without acceleration: the bounded number of decreasing-counter cycles is finite, although potentially enormous. Acceleration is convenient and gives an exact finite-prefix length, but no complexity bound is claimed.

### Expanding shuttle formulas

Suppose the repeated live cycle has Δ>0 and total anchor update E∈Z^d. At corresponding sections,

    x_n=x_0+nΔ,   L_n=L_0+nE.

There are finitely many edges and phases per cycle. In a local-prefix phase every occupied coordinate is affine in n. In a free-flight phase every occupied coordinate is affine in (n,j), where j≥0 is the packet-period count, restricted by linear inequalities coming from the first-contact cutoff. All labels are fixed within a phase. These formulas include every intermediate configuration, and their union is Presburger.

The duration of one whole cycle is affine in n, because every edge has duration αx+β. Its slope A is strictly positive: each edge has α>0 and x increases by Δ between corresponding cycles. Thus the section times are

    T_n=T_0+A n(n−1)/2+C n,   A>0.

The coefficients are effective rationals taking integral values on natural n. Exact vector anchor updates and exact time are both retained.

There are computable constants K_0,K_1 such that every support point y throughout cycle n satisfies

    ||y||∞ ≤ K_0+K_1 n.                        (9.1)

Indeed both marker positions are affine in n, the launch and local offsets are bounded, and each flight period count j has an affine upper bound in n. Every drift/phase offset is fixed finite data. This bound does not rely on coordinatewise monotonicity of a packet, a line passing through the spatial origin, or confinement in a one-dimensional interval.

## 10. Exact reachability and pattern tests

In alternatives A and B, use a common period to express all coordinates and time affinely in a nonnegative integer parameter; retain the finite transient. Multiple clocks cause no problem: take their least common multiple and record finitely many phases. Exact targets, translated targets, anchored patterns, and translated patterns are finite Presburger predicates on these coordinates. Zero entries mean no occupied coordinate equals the prescribed zero site. At most four occupied sites occur, so these absences are a finite conjunction. Higher-weight label choices are finite.

In alternative C, the untimed stationary-frame orbit is the finite union of the affine-in-(n,j) phase formulas of §9, plus the finite prefix. This decides exact target reachability and pattern occurrence in G, with or without existentially quantified translation. Translation-invariant questions have the same answers for F and G.

If δ=0 this already finishes all F questions. If δ≠0, choose a coordinate i with δ_i≠0. By (9.1), throughout cycle n an occupied F-coordinate in that coordinate direction satisfies, for δ_i>0,

    y_i(F^t(c)) ≥ δ_i T_n−K_0−K_1 n,

and for δ_i<0,

    y_i(F^t(c)) ≤ δ_i T_n+K_0+K_1 n.

Here t≥T_n; multiplication by negative δ_i reverses the inequality as used. Since T_n has positive quadratic leading coefficient, these bounds eventually lie permanently beyond any specified finite target window. Compute such an n_* by a rational quadratic inequality, or increase n until the bound is beyond the window and its derivative/difference is thereafter outward. This is an effective cutoff uniform over every phase in the cycle.

An anchored pattern containing a nonzero symbol and a nonempty exact target can occur only before T_(n_*). This is a finite, computable time interval and can simply be simulated, however large. A wholly zero pattern occurs after that cutoff. A mass-zero input and an empty exact target are handled immediately by conservation.

This resolves absolute translation without invoking an unrestricted quadratic Diophantine solver. No unrecorded absolute-position counter is needed.

## 11. No unit symbol

If no symbol has weight one, mass at most four occupies at most two sites. An isolated site of weight two or three cannot split; it is a finite-state walker whose label and vector increments become periodic. A weight-four singleton may split into two weight-two walkers, initially within diameter 2R.

Take a finite core of two-site/single-site configurations of diameter at most 2R (enlarge to 2 max(1,R) if R=0). Outside it the only nontrivial possibility is two independent weight-two finite-state walkers. Use common phases and coordinatewise affine inequalities to compute their first core encounter or prove it never happens. A core return has a fixed finite elapsed time and translation. The finite-core return graph therefore yields an eventually translated-periodic whole orbit or a terminal independent-two-walker profile, exactly as in §3. These are timed Presburger and decide all observations. This covers the missing case and completes the theorem.

## 12. Algorithm specification

Input: d, local finite rule F and radius R, alphabet weights, finite c with mass≤4, and an exact configuration or finite pattern observation. Hypotheses are a promise; the algorithm need not certify mass conservation for an arbitrary submitted rule.

1. Check trivial mass and alphabet cases; use §11 if there is no unit symbol
2. Compute isolated-unit drift δ and G
3. Enumerate all normalized mass-two diameter-2S states, compute their finite profiles
4. Enumerate all normalized mass-three diameter-4S states and their finite-core graph; compute the tagged connected-seed library, B, compact and emission profiles
5. Enumerate exact contact offsets a for every emission phase. Compute primitive directions and Bezout λ functionals
6. Enumerate marker shifts c from the encounter library. Solve (6.1) for every finite offset/profile pair with nonparallel drift to compute exceptional switch vectors
7. Choose N and W as §7. Build ordinary-state dispatch and live mode/residue transitions, or compute them lazily as visited
8. Run §9's section algorithm until A, B or C is established, retaining exact elapsed times and complete phase formulas
9. Check the finite prefix and the eventual form by §10

Every enumeration is finite; every unbounded-event search is reduced either to one-variable linear inequalities/equalities or to the one-counter termination argument. Presburger satisfiability is used only after explicit formulas have been constructed. None of the steps relies on a bounded search being mistaken for an unbounded proof.

## 13. Scope, sharpness and nonclaims

- The unit uniqueness assumption fixes all mass-one particles to the same drift. Several unit labels can act as distinct finite-state walkers and invalidate the bounded-dimer lemma
- Signed/zero-cost nonvacuum symbols, infinite alphabets, active vacuum, infinite initial configurations, time-dependent or spatially nonuniform rules are outside the theorem
- Four units do not imply eventual timed semilinearity: Report 12's one-dimensional binary quadratic shuttle embeds into every dimension by acting independently on lines
- The existing one-dimensional binary five-particle universal CA embeds into Z^d by applying its 1D local rule independently on lines parallel to the first coordinate. Finite total mass conservation, reversibility and any full-shift involution decomposition are preserved linewise. Inputs supported on one line have exactly the 1D dynamics. Thus the supplied Report 16/26 five-particle upper bound extends to every d; this paragraph inherits those reports' source and compilation proofs and does not independently reprove universality
- In that inherited effective finite-input/finite-observation setting, the four/five mass boundary is therefore dimension-independent. This is a mathematical consequence, not a present-day novelty assertion
- A planar finite-state walker with two stationary pebbles can store a vector separation, but it can query the other pebble only along one of finitely many affine rays. A direction change that would query an independent unbounded coordinate is forced into the bounded region by (6.1). This is why mere vector-valued separation does not yield two freely testable counters here
- The executable arithmetic checks in this packet audit formulas and adversarial cases; they do not prove the theorem over all cellular automata

## Provenance

Proof starting point: `Report 12: four-mass-decidability.tex`, SHA-256 `803bf0c4194bb9d0f1942e6ad3eb762c79d7a811bd785742ee63f0c46a775595`.

Upper-bound context: `Report 16: report16.tex`, SHA-256 `7e644e82b986903d473a6f99b379f8141e9a71e18fb01ecf3d4e554009563d81`; `Report 26: report26.tex`, SHA-256 `a156d7d973721f18c896cf71f0e9eedbaa214a613b8c7a77cf4704be90850dab`.

Those releases were read, not modified. This proof packet stands alone and does not revise their 1D statements.
