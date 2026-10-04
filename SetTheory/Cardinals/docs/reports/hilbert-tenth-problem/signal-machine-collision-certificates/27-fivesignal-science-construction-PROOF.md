# A five-signal periodic return with rational irrational-angle rotation

Research construction, 4 October 2026. Conventional proof, not proof-assistant checked. No priority claim. All executed arithmetic was newly written symbolic linear algebra on the formulas below. A fresh static grammar emitter produced the inert rule table without computing positions, times, or event choices. No physical simulator, upstream code, or stored collision schedule was executed.

## Result

There is a finite rational number-preserving one-dimensional signal machine, with exactly five live signals, and a fixed word of 138 strictly time-separated binary collisions whose outgoing-section return on the three positive gaps is

    M = (1/30) [[7,-2,10], [14,11,-10], [-6,6,15]].

It is rationally conjugate to diag(1/2, (1/2)R), where

    R = [[3/5,-4/5], [4/5,3/5]].

The exact infinite-word validity set over real initial gaps is nonsemialgebraic. Every valid input is Zeno. Thus neither an all-real-spectrum obstruction nor a general peripheral-roots-of-unity obstruction applies to physical periodic collision returns under the standard number-preserving distinct-speed conventions.

Deleting the final contraction gives a word of 114 collisions with return 2M, rationally conjugate to diag(1,R), and non-Zeno valid orbits. The contraction is optional for the nonsemialgebraicity result. For this uncontracted machine variant, close the messenger phase cycle after event 114 instead of event 138; merely truncating a prefix of the contracted rule table is not being called a periodic return.

The construction includes complete chronology, not merely selected collisions. Its finite label/rule table is given by an explicit finite-index schema in Section 6.

## 1. Five signals and section coordinates

Use four stationary markers at positions

    L=0 < X=x < Y=y < D=d

and a messenger co-located with L, moving right at speed +1. Their stationary meta-signals are distinct labels L0,X0,Y0,D0, all of speed zero. The messenger has finitely many phase labels, with speeds +1 or -1. During a primitive, exactly one designated marker can acquire a speed a strictly between -1 and +1; it is restored to its original stationary label before the primitive ends.

The outgoing section has order L0,messenger,X0,Y0,D0 and three positive gaps

    g=(x, y-x, d-y).

The zero gap inside the left collision is excluded from g. Translation has been removed. There are exactly five signals at every instant.

All coordinates below are spatial coordinates relative to L. The rightmost marker is denoted D but its coordinate is d.

## 2. Two exact primitives

### 2.1 Scaling one marker about the left anchor

Suppose a target stationary marker is at z>0, the messenger is at 0 moving +1, and all other markers are stationary. Pick u>0 and set

    a=(u-1)/(u+1), so -1<a<1.

The primitive L_z(u) does this:

1. The messenger travels right, transparently crossing stationary markers below z, and hits z. It reflects to -1; the target changes from speed 0 to a.
2. The messenger travels to 0, crossing the same intervening markers transparently, and reflects to +1.
3. It again crosses those stationary markers and meets the moving target. The target is restored to speed 0; the messenger reflects to -1.
4. The messenger returns through the intervening markers to 0 and reflects to +1.

The first target hit is at (z,z), and the intermediate left bounce is at time 2z. The second target hit satisfies

    t-2z = z+a(t-z),

so its spatial position is

    z' = ((1+a)/(1-a))z = uz.

The target moves monotonically between z and uz. Therefore this is exactly the specified complete positive-time collision word if both endpoints lie strictly between its unchanged nearest stationary neighbors. For a target with no right neighbor, only its lower-neighbor constraint is needed. The strict endpoint conditions keep the target away from every spectator for its entire motion. Because |a|<1, the messenger separates at the first target hit, reaches the left anchor strictly before returning to the target, and then returns strictly to the anchor. All transparent spectator hits have distinct positions and strictly positive intervening flights.

### 2.2 Homothety toward a stationary reflector

Let the target be x and let a stationary reflector be at z>x. The messenger again starts at 0 moving +1. Pick v>0 and set

    a=(1-v)/(1+v), so -1<a<1.

The primitive H_z(v) does this:

1. On its outward hit at x, the messenger keeps speed +1 and the target changes 0 to a.
2. It transparently crosses any stationary markers strictly between x and z, then reflects at z to speed -1.
3. It transparently crosses those markers on its way back, meets the moving target and restores its stationary label, keeping messenger speed -1.
4. It reaches 0 and reflects to +1.

The reflector hit is at time z. Solving

    2z-t = x+a(t-x)

gives the restored target location

    x' = v x+(1-v)z.

Again the target moves monotonically between its endpoints. The complete specified word is valid exactly when both endpoints stay strictly between the target's unchanged nearest neighbors. Its inward messenger hit precedes the anchor hit precisely because x'>0. All spectator crossings are included, with positive separation, by the same ordering argument.

Here and below a reflected primitive means applying these instructions in the coordinate w=d-position. Its anchor is D, messenger initial speed is -1, and every displayed nonzero velocity is negated in physical coordinates.

## 3. Translation and shear gadgets

For c<1, define

    T_z(c) = H_z(1-c) after L_x(1/(1-c)).

This acts on the target x by

    x -> x+c z.

Both primitives use the same target speed a=c/(2-c). Their intermediate target location x/(1-c) lies between x and x+cz whenever both final endpoints lie between 0 and z. Consequently, if the target has a stationary nearer neighbor y<=z, the exact guard for the entire translation gadget is simply

    0 < x < y,       0 < x+c z < y,

together with the unchanged marker order. It is necessary because the target is stationary at these section endpoints, and sufficient by the primitive proofs. The target moves monotonically in the direction of c throughout this two-primitive gadget.

Two translations T_y(c), then T_d(-2c/3), act by

    x -> x+c(y-2d/3).

Doing this pair twice with c=-1/4 realizes

    A: x -> x-(1/2)(y-2d/3),     y -> y.

All parameters are less than 1. The target speeds used by these translations are respectively -1/9 and +1/11.

For the other shear, transfer the messenger from L to D by transparently crossing X,Y and reflecting at D. In reflected coordinates

    r=d-y,       s=d-x,

do T_s(2/5), then T_d(-4/15), twice. This realizes

    r -> r+(4/5)(s-2d/3),

or, in the original coordinates,

    B: y -> y+(4/5)(x-d/3),      x -> x.

The reflected target speeds are +1/4 and -2/17; their physical velocities are -1/4 and +2/17. Transfer back from D to L by transparently crossing Y,X and reflecting at L.

The rotation macro is A, then B, then A. Write

    ξ=x-d/3,       η=y-2d/3.

Its exact return is

    (ξ',η') = [[1,-1/2],[0,1]] [[1,0],[4/5,1]]
               [[1,-1/2],[0,1]] (ξ,η)
             = R(ξ,η),
    d'=d.

Equivalently,

    x'=3x/5-4y/5+2d/3,
    y'=4x/5+3y/5.

Each A or B uses 36 binary collisions: two translations with the nearer reflector use 8 collisions each, and two with the farther reflector use 10 each. The two messenger transfers use 3 each. Total: 114.

## 4. The exact finite chamber, with all competitor/tie guards

The following endpoint inequalities are necessary and sufficient, not merely sufficient safe-region tests.

For an A block at current coordinates (x,y,d), form

    a0=x,
    a1=x-y/4,
    a2=x-y/4+d/6,
    a3=x-y/2+d/6,
    a4=x-y/2+d/3.

Require

    0<y<d,       0<a_i<y for i=0,...,4,

and replace x by a4. These are exactly the four translation gadgets' start/end conditions. Their internal scaling locations lie between the corresponding translation endpoints by Section 3.

For the B block, at its incoming coordinates form r=d-y and s=d-x, then

    b0=r,
    b1=r+2s/5,
    b2=r+2s/5-4d/15,
    b3=r+4s/5-4d/15,
    b4=r+4s/5-8d/15.

Require

    0<s<d,       0<b_i<s for i=0,...,4,

and replace y by d-b4. These conditions also make both transfers legal: all intermediate data markers are distinct and strictly between their stationary anchors.

Apply A's 12 rows, B's 12 rows to A's output, and A's 12 rows to B's output. This gives 36 strict homogeneous rational linear inequalities in initial (d,x,y), and no additional equality constraints. Let C denote this open cone and P its d=1 slice, in centered (ξ,η) coordinates. The expanded rows are in GUARDS.txt.

Why there are no missing competitor or tie guards: in every primitive only one marker moves, monotonically between its two checked endpoint positions, so it cannot meet any stationary marker. The messenger has speed ±1 and every moving target has speed in (-1,1). Thus its complete collision order is exactly the hit/crossing order specified in Section 2. Every intervening stationary marker crossing is explicitly part of the word, and all marker positions are strictly separated at it. These facts exclude all additional, earlier, or simultaneous collisions. Conversely a failed endpoint order or tie contradicts the proposed outgoing section at that point. Hence the 36 rows are equivalent to the complete macro's legality.

At x=d/3, y=2d/3, all A-block endpoints are d/3 or d/6. All reflected B endpoints are d/3 or 3d/5. They lie strictly between 0 and their other marker at 2d/3. Therefore P contains an open neighborhood of (0,0). It is bounded because its initial rows require 0<x<y<1.

For an explicit independent arithmetic check, a row c d+aξ+bη>0 has squared distance c²/(a²+b²) from the center on d=1. The minimum for the first A block is 1/45; for B it is 4/1845; for the last A block it is 4/153. The unique globally nearest row is B's first translation endpoint upper bound:

    d/15-3ξ/5+13η/10 > 0.

Its tangency point and squared distance are

    p=(4/205,-26/615),       ρ²=4/1845.

Every other row has larger distance. Thus the radius-ρ closed disk is inside the closed chamber and touches its boundary only at p.

## 5. Contraction and Zeno behavior

Append L_x(1/2), then L_y(1/2), then L_d(1/2), with transparent crossings of every already-scaled inner marker. These use target speed -1/3 and 4,8,12 binary collisions respectively.

When scaling target z, all inner stationary markers already have positions half their former positions. The target decreases monotonically from z to z/2, and remains strictly above every already-scaled inner marker because original order was strict. It stays below every unscaled outer marker. Thus this three-primitive homothety is valid for every ordered input, with no new guard beyond the final rotation section's strict ordering. The complete word has 138 binary collisions.

The gap return is therefore

    g'=(1/30) [[7,-2,10], [14,11,-10], [-6,6,15]] g.

Under the rational coordinate change g -> (d,ξ,η), this is diag(1/2,R/2). All eigenvalues have modulus 1/2. The normalized chamber remains P and normalized data rotate by R at each repetition.

Every macro duration is a fixed homogeneous rational linear form ℓ(g)>0 on C. Along any infinitely valid input its normalized configurations lie in the compact radius-ρ disk and d_n=2^(-n)d_0. Hence durations are bounded by K d_0 2^(-n), proving finite total elapsed time. For rational input the sum is the rational number ℓ(I-M)^(-1)g. The construction does not specify any continuation at or after the accumulation.

Without contraction, d stays fixed and valid normalized configurations remain in that same compact disk. There is a uniform positive lower bound on macro duration: the messenger transfers between the anchors, which are distance d apart, twice per rotation macro. Thus infinitely valid uncontracted executions are non-Zeno.

## 6. Explicit finite-index rule table schema

This supplies the whole finite machine; no arbitrary program interpreter is assumed. RULES.json contains its explicit 138 indexed binary rules and 169 meta-signals. The fresh script emit_static_rules.py only expands this static grammar and checks labels/speeds; it does not compute positions, times, or a physical trajectory.

Expand the fixed word in this exact order:

1. Twice: T_y(-1/4), T_d(1/6), with x the target.
2. Transfer L to D: cross X, cross Y, reflect at D.
3. In reflected coordinates r=d-y,s=d-x, twice: T_s(2/5), T_d(-4/15), with r the target.
4. Transfer D to L: cross Y, cross X, reflect at L.
5. Twice: T_y(-1/4), T_d(1/6), with x the target.
6. L_x(1/2), L_y(1/2), L_d(1/2).

Expand each T_z(c) into the L then H primitives of Section 3. Expand every primitive into the complete binary-event list of Section 2, including the listed transparent spectator crossings. The sequence has m=138 events. Associate a distinct messenger label Q_j to the state immediately before event j, for j=0,...,m-1; use Q_m=Q_0. Its speed is the messenger's prescribed direction for that leg. Q_0 has speed +1. Give each temporary moving-marker phase its own label Z_{k,a}, of rational speed a, where k identifies the primitive and Z is its fixed marker identity. The four stationary labels remain L0,X0,Y0,D0.

At indexed event j, let Z_in and Z_out be the marker labels prescribed by that event. Include exactly this binary rule:

    {Q_j,Z_in} -> {Q_(j+1 mod m),Z_out}.

For a transparent spectator crossing Z_in=Z_out=Z0 and the two Q speeds agree. At an anchor/reflector bounce Z_in=Z_out=Z0 and the Q speed changes sign. At a target launch Z_in=Z0, Z_out=Z_{k,a}; at target restoration the labels are reversed. Messenger directions are exactly those in the primitive lists. Reflecting a primitive negates all its nonzero physical speeds. Every rule has two distinct input speeds and two distinct output speeds, since marker speeds have absolute value <1 and messenger speeds have absolute value 1.

Every indexed input contains its unique Q_j, so no two prescribed rules conflict. After the last event all four markers again have their original stationary labels, Q_0 is at L moving +1, and the original outgoing label/zero pattern is restored. All unused collision input sets with pairwise distinct speeds may be assigned the transparent rule S->S. This completes a finite number-preserving machine. Finite phase labels implement a fixed finite word; they are not an unbounded control store.

The physical speed set is contained in

    {0,+1,-1,-1/9,+1/11,-1/4,+2/17,-1/3}.

Exactly five signals are live throughout; the number of meta-signal types is larger and is not being conflated with population.

## 7. Exact nonsemialgebraic infinite validity

R has infinite order. If its eigenvalue ζ=(3+4i)/5 were a root of unity, ζ+ζ^(-1)=6/5 would be a rational algebraic integer, hence an integer, a contradiction. Its powers are therefore dense in the planar rotation group.

For d=1, the exact infinitely valid set is

    {z: ||z||<ρ} union
    ({z: ||z||=ρ} minus {R^(-n)p : n>=0}),

where ρ²=4/1845 and p=(4/205,-26/615).

Proof: radii below ρ stay strictly in all chamber half-planes. At radius ρ only p lies outside the open chamber, because it is the unique tangency point. A point on that circle fails exactly when an iterate equals p. At larger radius some chamber half-plane excludes a nonempty open arc, which every dense rotational orbit visits. Contraction cancels on normalization and does not change this criterion.

The excluded set on the circle is countably infinite and dense, while its complement is uncountable. A semialgebraic subset of a real circle is a finite union of points and arcs; this boundary subset is neither. Consequently the validity set on d=1, and therefore the homogeneous positive-gap validity cone, is not semialgebraic.

All excluded tangency-orbit points have rational coordinates. In fact the rational boundary points {R^k p:k>=1} are all accepted: if R^n R^k p=p for some n>=0, then R^(n+k)p=p, contradicting infinite order. This accepted positive orbit and the rejected nonpositive orbit {R^(-n)p:n>=0} are disjoint dense rational subsets of the same circle. A semialgebraic formula agreeing on all rational inputs would restrict to finitely many points/arcs on that circle, which cannot separate these two dense rational sets. Thus no finite rational-polynomial sign formula even agrees with this physical validity predicate on all rational gap inputs.

The same obstruction applies to finite polynomial-sign formulas restricted to positive integer gaps, by the following homogenization-at-infinity argument. Suppose a Boolean formula F in finitely many polynomial signs agreed with the homogeneous validity predicate on all positive integer vectors. Replace each polynomial sign by the sign of its highest-degree nonzero homogeneous component at the input (a finite lexicographic case distinction among homogeneous components), yielding a semialgebraic formula F_infinity. For every positive integer vector v, F(kv) is constant in positive integers k by assumed agreement and homogeneity, and eventually equals F_infinity(v). Thus F_infinity agrees on all positive integer vectors. Its signs are invariant under positive rescaling, so clearing a rational vector's denominator extends agreement to all positive rational vectors, contradicting the preceding paragraph. This does not exclude existential Diophantine representations over natural witnesses.

## 8. Relation to prior work and limits

The signal-machine conventions and elementary moving-wall/shuttle geometries are standard. Primary introductory material and standard rational signal-machine definitions can be found in Jérôme Durand-Lose's AGC introduction and Becker et al., Abstract Geometrical Computation 8: Small Machines, Accumulations & Rationality (arXiv:1307.6468).

- https://www.univ-orleans.fr/lifo/Members/Jerome.Durand-Lose/Recherche/AGC/intro_AGC.html
- https://arxiv.org/abs/1307.6468

A targeted web check used the phrases "signal machines affine linear", "signal machine rotation collision", "abstract geometrical computation linear transformation", and "signal machines semialgebraic". It surfaced earlier affine bending/shrinking constructions in Durand-Lose, Abstract Geometrical Computation 5: Embedding Computable Analysis, but no matching fixed-five-live-signal periodic-return semialgebraicity result in this bounded search. That is not an exhaustive duplicate check.

- https://www.univ-orleans.fr/lifo/membres/Jerome.Durand-Lose/Recherche/Publications/2011_NC_UC.pdf

This packet makes no exhaustive novelty claim, gives no arbitrary Positivity-to-signal-macro reduction, and asserts no undecidability. The obstruction is to a finite semialgebraic sign-test classification extending the at-most-four-population result, not to all possible Diophantine representations or algorithms on rational seeds.
