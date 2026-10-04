# Independent adversarial audit: five-live-signal obstruction

4 October 2026. Conventional mathematical/source audit, not a proof-assistant certificate.

## Verdict and scope

**PASS for the stated five-signal physical construction, its exact finite chamber, its nonsemialgebraic infinite-complete-word validity set, its elementary rational-input decision criterion, and its rational Zeno clock.** No substantive mathematical or rule-table defect was found in the frozen packet identified below. The initial integer-input sign-formula claim needed an additional argument; the now-frozen proof supplies the correct eventual-ray argument.

This audit independently derived the primitive geometry, all gadget endpoint maps, all 36 rows, return matrices, distance comparisons, contact coordinates, and duration forms. It read and checked every one of the 138 explicit binary rules against independently written phase templates, including all transparent crossings, marker phase labels, messenger velocities, local output order, and cyclic return. It did not execute the author's emitter, scripts, membership checker, a physical simulator, the saved rule program, or an upstream program. Executed code was newly written exact rational algebra and inert structural validation only. There was no trajectory replay or numerical sampling of physical executions.

Two small interpretive qualifications should accompany reuse:

1. The 114-event uncontracted construction is a **variant machine**: its event 113 must return the messenger to Q0, rather than Q114. Repeating the prefix of the unchanged 138-event machine would not give that variant. The finite-index schema with m=114 supplies the required relabeling immediately, and the frozen proof explicitly states this qualification in its Result section.
2. “Rational machine” here means finite rational speeds/rules, with a real-input extension for the semialgebraicity theorem. Some standard sources reserve “rational signal machine” for rational initial coordinates too. The separate rational- and integer-input sign obstructions avoid any dependence on that terminology.

The audit does not establish a literature priority claim. It also does not independently prove the separate at-most-four-population theorem: a claimed sharp four-versus-five threshold is conditional on that theorem and its precise fixed-complete-macro scope. No undecidability or general Diophantine obstruction follows.

## 1. Frozen sources and receipts

Audited source SHA-256 values:

- PROOF.md: `1bea81f8f2e6693d4b7958fb44763eb644663d208fe70c577e0137184e17a725`
- GUARDS.txt: `d8c1dec4945dd4f3dedfdf469d3b6e51ea9991e8234cccb1daf49c0d8cbc6ce9`
- RULES.json: `0e145aecc4f60685570c41be57d04905eab5b3bfa1a25b185d0b7bcf27e2f2db`
- BOUNDARY_AND_ARITHMETIC.md: `9642699a09f3ebc558fb1268c61370fb514839404e834acf288f9504e3e81b77`
- rational_membership.py, read only: `14a31600583a89def7f81e27cfa56c9eff187df7c8a4bca31fddca4c7379d33f`

Exact frozen copies are in `inert_sources/`. The two independent owned audits are `audit_exact_algebra.py` and `audit_inert_rules.py`. Their receipts are `exact_algebra_receipt.json` and `inert_rules_receipt.json`. The former includes all 36 exact supporting-line distances, sorted; the latter includes the 29 phase blocks. `all_138_local_rule_checks.tsv` enumerates all 138 checked input/output pairs and their physically forced incoming/outgoing left-to-right local order.

## 2. Complete primitive geometry

Work first in coordinates based at a stationary anchor 0, with initial messenger velocity +1. In every primitive all other markers are stationary; the one moving target has velocity a with −1<a<1. Reflection replaces position q by d−q and negates every nonzero physical velocity, preserving all the following statements.

### Scaling primitive L_z(u)

For u>0 let a=(u−1)/(u+1). The target starts at z. The four principal events have times and positions

- launch: (t,q)=(z,z)
- first anchor reflection: (2z,0)
- target restoration: (2z+uz,uz)
- final anchor reflection: (2z+2uz,0)

The target line q=z+a(t−z) passes through its stated restoration point because a(1+u)=u−1. Its motion is monotone between z and uz. Thus requiring both endpoints strictly between its fixed nearest neighbors excludes **every target/stationary collision**, including remote collisions elsewhere while the messenger travels.

For each inner stationary marker at s<min(z,uz), the four messenger crossing times are

    s, 2z−s, 2z+s, 2z+2uz−s.

These occur in the stated outward/inward/outward/inward orders, with positive gaps between all successive events. Outer stationary markers are never reached. At launch, relative velocity between the inward messenger and target is −1−a<0; on its returning outward leg it is 1−a>0. Therefore they separate after launch and meet only at the stated restoration. After restoration the messenger departs left from a stationary target. This verifies the complete word, not just the selected principal collisions.

If an endpoint reaches a neighbor, there is a forbidden coincident contact; if it passes a neighbor, a target/stationary collision occurs no later than that endpoint. Hence the strict endpoint condition is necessary as well as sufficient for this prescribed complete word. The duration is exactly 2(z+uz).

### Reflector homothety H_z(v)

Here the target at x is the nearest marker to the anchor, as in every use in this construction; z>x is a stationary reflector. Put a=(1−v)/(1+v). The messenger travels q=t to t=z, then q=2z−t back to the anchor. It launches the target at t=x and restores it at

    x'=v x+(1−v)z,    t_restore=2z−x'.

The target follows its straight line between x and x'. If both endpoints lie strictly between 0 and its nearest fixed neighbor y≤z, it never meets a fixed marker. Every spectator s between y and z is crossed at t=s and t=2z−s. Since x'<s, each return crossing is strictly before target restoration. Since 0<x'<z, restoration is strictly after reflector bounce and before final anchor bounce. The messenger and target have nonzero separating/catching relative velocities because |a|<1. All events are binary and globally time-separated. Duration is 2z.

Necessity follows as for L: a failed endpoint incurs an extra or coincident collision. The generic presentation should be understood with the applicable target/anchor order; no use here requires an unlisted stationary marker below the H target.

### Translation T_z(c)

For c<1, compose L_x(1/(1−c)) followed by H_z(1−c). Their target velocity is the same a=c/(2−c), and the target locations are

    x -> w=x/(1−c) -> x'=x+cz.

When 0<x,x'<y≤z, w lies between x and x'. For c>0, x<w<x' follows from x'<z; for c<0, x>w>x' follows from x<z. Thus the two endpoint guards imply every intermediate primitive endpoint guard. The physical target moves monotonically throughout the gadget. This proves the claimed exact guard reduction rather than only a sufficient safe region.

All four c values used are less than 1. Their physical target velocities are −1/9,+1/11 for the left-based translations and −1/4,+2/17 for the reflected translations.

## 3. Every finite phase and binary event

The inert rule table matches the following complete collision-identity words. Indices are zero-based and inclusive. A marker letter denotes a collision of the messenger with that identity; launch/restoration uses the exact temporary label listed in the JSON. All messenger velocities and those labels were individually checked; the full per-event receipt gives them without compression.

| Phase | Events | Marker word |
|---|---:|---|
| L01 | 0–3 | XLXL |
| H02 | 4–7 | XYXL |
| L03 | 8–11 | XLXL |
| H04 | 12–17 | XYDYXL |
| L05 | 18–21 | XLXL |
| H06 | 22–25 | XYXL |
| L07 | 26–29 | XLXL |
| H08 | 30–35 | XYDYXL |
| transfer_right | 36–38 | XYD |
| L09 | 39–42 | YDYD |
| H10 | 43–46 | YXYD |
| L11 | 47–50 | YDYD |
| H12 | 51–56 | YXLXYD |
| L13 | 57–60 | YDYD |
| H14 | 61–64 | YXYD |
| L15 | 65–68 | YDYD |
| H16 | 69–74 | YXLXYD |
| transfer_left | 75–77 | YXL |
| L17 | 78–81 | XLXL |
| H18 | 82–85 | XYXL |
| L19 | 86–89 | XLXL |
| H20 | 90–95 | XYDYXL |
| L21 | 96–99 | XLXL |
| H22 | 100–103 | XYXL |
| L23 | 104–107 | XLXL |
| H24 | 108–113 | XYDYXL |
| L25 | 114–117 | XLXL |
| L26 | 118–125 | XYXLXYXL |
| L27 | 126–137 | XYDYXLXYDYXL |

The reflected blocks start with messenger −1 at D; the others start +1 at L. Each L principal collision reverses the messenger. Each H launch and restoration preserves its direction, and the reflector and anchor reverse it. Transparent crossings preserve direction. This verifies all 138 listed Q input/output speeds against phase geometry.

There are exactly 138 Q labels, 27 temporary marker labels, and 4 stationary labels: 169 meta-signals total. The exact speed set is

    {−1, −1/3, −1/4, −1/9, 0, 1/11, 2/17, 1}.

Every explicit rule consumes one messenger and one marker and emits one messenger and the same marker identity. Temporary labels occur once as launched output and once as restored input. No moving marker survives a primitive. Each Q_j occurs as the messenger input of exactly one explicit rule, so input sets do not conflict. Every pair has distinct velocities before and after the rule. The identity default on every other distinct-speed input set is a finite, deterministic, globally number-preserving completion.

For a binary contact, incoming local spatial order is decreasing velocity and outgoing local spatial order is increasing velocity. This exact order was recorded for every table row. Since the messenger has speed ±1 and the marker speed lies in (−1,1), every declared departure separates immediately, with no second zero-time event. The endpoint proofs put every uninvolved marker strictly outside the contact location, eliminating ties with them. No pair of stationary markers can collide. These observations cover all adjacent and remote competitors.

Event 137 emits {Q0,L0}; the other three marker labels are stationary, and the messenger is at L moving +1. The original outgoing section's label and zero-gap pattern is restored. The conserved live population is five, counting incoming/outgoing strands at binary collisions; the two signals at the outgoing collision section share a spatial point, so this is not a count of distinct occupied points.

## 4. Composition, chamber, and contraction

Two translation pairs with c=−1/4 produce

    A: x -> x−y/2+d/3,    y unchanged.

The outward/inward transfers take time d each and have exactly three collisions each. In reflected coordinates r=d−y, s=d−x, two pairs with c=2/5 produce r->r+4s/5−8d/15. Thus

    B: y -> y+4x/5−4d/15,    x unchanged.

In centered coordinates ξ=x−d/3, η=y−2d/3, the chronological composition A,B,A is

    (ξ,η) -> (3ξ/5−4η/5, 4ξ/5+3η/5).

For each A block, the two fixed-neighbor rows plus the lower/upper bounds at its five translation endpoints are necessary and sufficient by Section 2. The same argument applies to the B block in reflected coordinates. Pulling all rows back through preceding blocks gives exactly the 36 lines in GUARDS.txt, coefficient for coefficient. They are an exact system, not asserted to be irredundant.

There are no missing contraction guards. First x is halved while y,d stay fixed. Then y is halved, and its lower neighbor has already become x/2<y/2. Then d is halved, and its inner neighbors are x/2<y/2<d/2. Every target stays between its relevant initial and final positions. These steps have 4,8,12 collisions. Together with 36+36+36 shear collisions and six transfer collisions the total is 138.

The coordinate change from gap g=(g1,g2,g3) is

    (d,ξ,η) = Qg,
    Q = [[1,1,1],[2/3,−1/3,−1/3],[1/3,1/3,−2/3]].

Exact conjugacy gives

    Q M Q^−1 = diag(1/2,R/2),
    M = (1/30)[[7,−2,10],[14,11,−10],[−6,6,15]],
    R = [[3/5,−4/5],[4/5,3/5]].

Hence the eigenvalues are 1/2 and (3±4i)/10. The peripheral phases relative to modulus 1/2 are 1 and (3±4i)/5; the latter have infinite order.

## 5. Exact geometry and the physical failed contact

For each row a d+bξ+cη>0, a>0. Its supporting-line squared distance from the normalized center is a²/(b²+c²). Independent rational comparison gives block minima

    first A: 1/45;    B: 4/1845;    final A: 4/153.

The unique global minimizer is row 18, in one-based guard numbering:

    d/15−3ξ/5+13η/10>0.

The contact is the perpendicular projection of 0 to that line:

    p=(4/205,−26/615),    ||p||²=ρ²=4/1845.

All other rows are strictly positive at every point of that closed disk; the minimum row vanishes only at p. The initial order rows also show P is bounded and its center is interior.

At d=1, p means x=217/615,y=128/205. After the first A, x=46/123. In the first reflected L phase,

    r=1−y=77/205,    s=1−x=77/123,    (5/3)r=s.

The target reaches X exactly at its nominal restoration. Event 41 expects {Q41,Y_L09}, but the actual contact also includes X0. Its incoming speeds are −1,−1/4,0, all distinct. Thus p is rejected by a real forbidden triple collision, not an artificial safety margin. Every R^−n p reaches the same failure in macro n.

Integer boundary examples, checked by exact coordinate conversion, are rejected gaps (217,167,231) and accepted gaps (233,171,211). Their sums are both 615; the second is Rp with Rp=(28/615,−2/205). These fixtures expose the necessary orientation of the excluded orbit.

## 6. Infinite validity and sign-formula obstructions

The rotation eigenvalue ζ=(3+4i)/5 is not a root of unity: otherwise ζ+ζ^−1=6/5 would be a rational algebraic integer and therefore an integer. Thus positive and negative powers are dense in the rotation group.

Below radius ρ, every rotated point satisfies every strict chamber row. At radius ρ the only excluded point in a single chamber is p, so a point fails some future macro exactly when it belongs to {R^−n p:n≥0}. Above radius ρ the nearest half-plane excludes a nonempty open arc; every forward orbit visits it. Therefore the normalized exact validity set is

    K={w:||w||<ρ} ∪ ({w:||w||=ρ}\{R^−n p:n≥0}).

Its critical-circle exclusion is countably infinite, so K cannot be semialgebraic: a semialgebraic subset of a circle is a finite union of points and arcs. The real gap set is the positive homogeneous cone over K and is likewise nonsemialgebraic. This also excludes finite real-quantifier polynomial descriptions of that exact real set, by quantifier elimination.

For rational inputs a stronger agreement obstruction holds. The rejected nonpositive orbit and the accepted positive orbit of p are disjoint dense rational subsets of the same circle. An infinite-order rotation cannot identify a positive and nonpositive power. A semialgebraic circle subset and its complement cannot both contain dense sets while one contains every point of one orbit and none of the other: after deleting finitely many partition points its membership is constant on each remaining arc. Thus no finite polynomial-sign formula, even with arbitrary real coefficients, agrees on all rational gaps.

For integer-only formulas, homogeneity of the physical predicate is not enough by itself. The frozen packet now provides the needed bridge. For each polynomial f=Σ f_j with homogeneous components f_j, the sign of f(tg) for all sufficiently large positive t is the sign of the largest-degree nonzero f_j(g), or zero if all vanish. This is a finite semialgebraic case distinction and is itself invariant under positive scaling. Replace every atom of an alleged integer-input formula by that eventual-sign case distinction. On every integer ray, all positive integer multiples have the same correct physical answer, so the eventual formula agrees there. Clearing denominators extends it to every positive rational ray, contradicting the rational obstruction. This validates the integer-gap claim without assuming the alleged original formula is homogeneous.

These statements exclude finite polynomial-sign classifiers without integer-quantified witnesses. They do not exclude general Diophantine definitions or algorithms.

## 7. Exact rational membership, independently checked

On the critical circle, write η=(u+iv)/(p_x+i p_y). The forbidden set is exactly η=((3−4i)/5)^n for n≥0. Let q be the least common positive denominator of the two rational components of η.

For n≥1 the pair of integer coefficients of (3−4i)^n is congruent to (3,1) modulo 5. Indeed in the quotient ring with i²=−1, (3+i)^2=3+i modulo 5. Neither coefficient is divisible by 5, so the least common denominator is exactly 5^n. This argument is valid in that ring; it does not incorrectly assume the quotient is a field.

Consequently q not a power of 5 proves acceptance. If q=5^n, n is forced; one exact integer-power comparison decides rejection. For q=1 the forced n is zero, so only η=1 is rejected. In particular the forward point η=ζ is accepted despite denominator 5. The full rational predicate first checks positive gaps and exact radius comparison, then applies this boundary test. It is total, elementary, and does not use density as an algorithm.

The provided rational_membership.py was inspected as text and implements precisely this test, including exact complex division, least-common denominators, nonnegative exponent extraction, and inverse orientation. It was not executed. Separately owned arithmetic checked the inverse-power denominator identity for n=1,…,100, but the general justification is the preceding modular proof, not those fixtures.

Recursiveness under an explicit rational encoding is compatible with the standard MRDP consequence that an existential-natural Diophantine representation exists. No economical witness count, bounded degree, uniqueness, or useful compiler is proved by that observation.

## 8. Duration, Zeno behavior, and rational accumulation time

Independent duration composition uses L duration 2(z+uz), H duration twice its reflector distance, and two transfers of duration d. It yields rotation-only duration

    (32134/855)d+(30512/1425)ξ−(9942/475)η.

The final three half-scalings contribute

    3(x_rot+y_rot+d)=6d+(21/5)ξ−(3/5)η.

Their sum is

    ℓ(d,ξ,η)=(37264/855)d+(36497/1425)ξ−(10227/475)η.

It is positive on the exact legal chamber because it is the sum of strictly positive physical primitive durations. Let N=diag(1/2,R/2). Rational inversion or the independently checked identity T−TN=ℓ gives

    T(d,ξ,η)=(74528/855)d+(53102/3705)ξ−(144302/3705)η.

All eigenvalues of N have modulus 1/2. Thus ΣℓN^n converges to this exact T on every infinitely valid input. Every such orbit is Zeno, and T is rational whenever the initial gaps are rational.

A direct geometric bound avoids reliance on cancellation in the clock coefficients. Every moving point stays in the initial [0,d] interval of the macro. Its twelve translation L primitives each take <4d, twelve H primitives take ≤2d each, transfers take 2d, and the three half-scales take <9d in total. Therefore ℓ<83d and the infinite duration is <166d_initial. Since d halves every macro, all five strands approach the fixed left anchor 0. The construction does not assert any continuation through the accumulation.

In the correctly reclosed 114-event variant, d is unchanged and each macro contains two full anchor-to-anchor transfers. Its duration is at least 2d>0, so infinitely valid executions are non-Zeno. Its normalized chamber and rotation predicate are the same.

## 9. Independently checked primary-source scope

- Becker, Chapelle, Durand-Lose, Levorato, Senot, *Abstract Geometrical Computation 8: Small Machines, Accumulations & Rationality*, §2.1 Definition 1, allows finitely many meta-signals with coincident speed values but requires the speeds in each collision input and output set to be pairwise distinct. The audited table satisfies this precise convention. This source counts speeds separately from population. [Primary PDF](https://arxiv.org/pdf/1307.6468)
- Dai–Xia, *Non-Termination Sets of Simple Linear Loops* (2012), §4 Theorem 4.1 and Proposition 3, already give nonsemialgebraicity for a three-variable loop using diagonal update diag(2,3,5) and a non-strict linear guard. Abstract three-variable nonsemialgebraicity is therefore not new here. [Primary article](https://arxiv.org/html/1206.0232v1)
- Ouaknine–Worrell, *On Linear Recurrence Sequences and Loop Termination* (2015), Example 3.1, treats an irrational-rotation loop with a non-strict guard and a cone-shaped nontermination set. The strict guard's omitted orbit points are essential to the present obstruction. The displayed cone there should be read with nonnegative axial coordinate under its guard. [Primary PDF](https://www.cs.ox.ac.uk/james.worrell/lrs5.pdf)
- Durand-Lose's introductory overview explicitly describes distance-based counters and multiplication/division geometry, and its rational-machine terminology includes rational initial positions. [Author overview](https://www.univ-orleans.fr/lifo/Members/Jerome.Durand-Lose/Recherche/AGC/intro_AGC.html)
- Durand-Lose, *Abstract Geometrical Computation 5: Embedding Computable Analysis*, contains earlier finite-signal real-number encodings, shrinking, and acceleration structures. It does not by the inspected passages certify a matching fixed-five-signal periodic-return theorem. [Primary manuscript](https://www.univ-orleans.fr/lifo/membres/Jerome.Durand-Lose/Recherche/Publications/2011_NC_UC.pdf)

These checks support only bounded source comparison. The potentially distinctive claim is the explicit, fully guarded five-live-signal rational physical realization and its precise return-domain behavior. No exhaustive novelty or minimal speed/phase/rule count claim is warranted.
