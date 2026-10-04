# Fixed-word invertibility, collision parity, and all rational invertible planar returns

4 October 2026. A new proof packet, preserving the preceding reports. The linear-algebra obstruction is proved directly; the realization corollary uses the positive-determinant compiler in `../five-signal-planar-realization60-20261004/PROOF.md`. No author/upstream program, trajectory simulator, or saved collision schedule was run. The only new executed mathematics is the freshly authored and inspected standard-library symbolic-row checker `static_algebra.py`.

## 1. Results and exact scope

**Theorem A (fixed-word invertibility).** Consider a one-dimensional signal machine with finitely many labels and constant rational speed assigned to each label. Fix a finite complete collision word on a nonempty full-dimensional open chamber of an outgoing binary-collision section. Assume:

1. The population is constant throughout the word; every prescribed event is binary and emits exactly two signals at its collision position.
2. The two incoming speeds and the two outgoing speeds are distinct at every event.
3. The initial section has exactly one outgoing pair at the same position, with every other adjacent gap strictly positive. Each successive event occurs after a strictly positive flight, and no other event occurs in that flight or simultaneously with a prescribed event.
4. The word specifies the discrete phases, partners, and their ordering, so each interval's velocity vector is fixed on the chamber. A literal return restores the outgoing phase, label pattern, and section identification.
5. The coordinates record all positional degrees of freedom of this section, apart from a legitimate quotient by common spatial translation. No additional unrecorded continuous variable is discarded.

Then the fixed-word positional section map is the restriction of a rational invertible homogeneous linear map between the full section spaces. Its quotient by common translation is also rational and invertible.

This is a geometric fixed-itinerary theorem, not a theorem that the whole machine is reversible. Different words can have overlapping images, and collision rules need not be injective as a map on label sets.

**Theorem B (orientation).** For a literal return to the same sorted collision face and outgoing phase, with the same increasing-gap coordinate convention at both ends, a word with m events has

    sign(det return) = (−1)^m.

More precisely, on the translation quotient its determinant is

    det return = (−1)^m product over events j of (s_j^+ / s_j^-),

where s_j^- > 0 is the incoming pair's closing speed and s_j^+ > 0 is the outgoing pair's separation speed, both measured in increasing spatial order. Thus neither invertibility nor section closure forces positive determinant. Different end-coordinate identifications require the corresponding coordinate-orientation factor; they must not be silently substituted for a literal return.

**Theorem C (a seven-event orientation reversal on the original five-signal section).** There is a finite deterministic rational-speed number-preserving machine whose outgoing section is exactly the preceding compiler's section:

    L at 0, X at x, Y at y, R at D, all four stationary,
    one messenger at L with speed +1, and 0 < x < y < D.

A seven-event complete binary return has exact chamber

    0 < x < y < D,    y < 4x,

and return

    D' = D,    x' = −2x/3 + 5y/6,    y' = y.

It restores every section label and outgoing phase. With X_c = x−D/3 and Y_c = y−2D/3, the centered planar matrix is

    J = [[−2/3, 5/6], [0, 1]],       det J = −2/3.

The standard center x=D/3, y=2D/3 is strictly inside the exact chamber. The construction has five live signals, eleven meta-signals in a standalone realization, and seven explicit rules. It also works with four live signals if the untouched rightmost marker R is omitted, but then the translation-quotiented section is only two-dimensional before scale normalization.

**Corollary D (exact planar realizability criterion).** In the precise five-live-signal full-section model above, for rational A and rational λ>0, a return

    (D,X_c,Y_c) -> λ(D,A(X_c,Y_c))

on a full-dimensional nonempty open chamber exists **if and only if det A is nonzero**. It can be chosen to have a bounded exact rational polygon containing the standard center on D=1, literal phase closure, and a finite deterministic number-preserving completion. For negative determinant, append Theorem C to a positive-determinant compiler as described in §7.

The obstruction does not rule out singular maps obtained by projecting away hidden coordinates, restricting to a lower-dimensional boundary or invariant slice, using nonbinary or population-changing collisions, or interpreting an accumulation limit as a new event. Those are different models.

## 2. The transverse-flight isomorphism

Give the n live positional slots temporary names. For a collision pair a, let h_a be the rational row which subtracts the two positions, and let

    H_a = {q in R^n : h_a q = 0}.

Immediately after that collision the position is in H_a. The outgoing speed vector v satisfies h_a v != 0, because its two outgoing speeds are distinct. Suppose the next prescribed collision is pair b. Its incoming speeds are distinct, so h_b v != 0. Its positive flight time and landing point are

    τ(q) = −h_b q / (h_b v),
    F_ab(q) = q + vτ(q) = q − v (h_b q)/(h_b v).

This is a rational homogeneous linear map from H_a to H_b. Although the ambient projection R^n -> H_b has a one-dimensional kernel, its restriction to H_a has none: the kernel direction is v and v is transverse to H_a.

There is an explicit inverse on H_b:

    F_ab^(-1)(r) = r − v (h_a r)/(h_a v).

Substitution proves both inverse identities. The inverse formula is geometric algebra; it does not assert that the machine implements the inverse word or that every point of H_b realizes the forward chronology. On the actual chamber, the forward image is open in H_b and the restriction is a bijection onto that image.

At a collision, both outgoing signals are emitted at the same position as both incoming signals. Identifying the two incoming slots with the two outgoing slots makes the positional map the identity. Choosing the other identification gives a fixed coordinate permutation. Either choice is invertible. A product of these collision identifications and the transverse-flight isomorphisms is therefore a rational homogeneous linear isomorphism between the initial and final section spaces.

The full-dimensional chamber matters when passing from the physical return to a claimed linear formula: agreement on a nonempty open subset uniquely fixes the ambient linear map. Agreement only on a proper slice would not do so.

### 2.1 Coincident strands, sorted slots, and repeated labels

The initial messenger and anchor are two live outgoing strands at one point, not one positional degree of freedom accidentally counted twice. Their equality is exactly the equation defining H_a. Their distinct outgoing speeds give the transversality that removes the apparent projection kernel.

A convenient canonical naming scheme is increasing spatial order. At an event the colliding pair occupies adjacent slots. The incoming left strand has larger speed than the incoming right strand; outgoing slots are assigned in increasing outgoing-speed order. At the collision instant both positional coordinates are equal, so this reassignment changes no position. On each open flight the sorted order is unambiguous and constant.

Labels are not persistent material-particle identities. Their rules can change them, and the theorem does not invent identities across a collision. Temporary slots, or explicit fixed local bijections, are enough.

The same meta-signal may occur at several distinct positions. This creates no continuous identification or loss of information: increasing position distinguishes the instances on a chamber. Two instances of one label have equal speed and cannot form one of the stipulated distinct-speed binary input or output pairs. Sorting or an explicit occurrence index therefore handles repeated labels without changing the argument.

If an allegedly fixed word leaves the occurrence/slot choices ambiguous, refine it into its finitely many ordered charts. The theorem is chartwise; it does not turn an unspecified union of charts into one linear map.

### 2.2 Spatial translations and anchors

Let e=(1,...,1). Every collision row satisfies h_a e=0, and every flight satisfies F_ab e=e. Collision permutations also fix e. The full section isomorphism therefore preserves the common-translation line Re and induces an isomorphism

    H_initial / Re -> H_final / Re.

In particular, fixing a left anchor coordinate to zero is a choice of representative for this quotient, not a destructive projection. If an anchor translates during the word, subtracting its final coordinate is still a valid linear quotient chart. No stationary-anchor hypothesis is needed for Theorem A itself.

For five live signals, the full collision hyperplane has dimension four and its translation quotient has dimension three. On the stationary-marker section these three coordinates are exactly (D,x,y), or equivalently (D,X_c,Y_c). Further fixing D=1 is scale normalization, discussed in §4.

The initial anchor contact is the outgoing section, not an extra zero-time event inserted before the word. The final anchor contact is the word's last event; its two outgoing strands have the restored section phase. The hypothesis of positive flights applies between these actual section events. It is essential that a phase switch is not being substituted for a timed contact.

## 3. Determinant and parity in sorted gaps

Write the n−1 adjacent gaps as

    g_i = q_(i+1) − q_i,    1 <= i <= n−1.

These are coordinates on the translation quotient. A binary collision of sorted rank a lies in the face g_a=0. Give that face the coordinate order (g_1,...,g_(a−1),g_(a+1),...,g_(n−1)).

Let w_i=v_(i+1)−v_i be the gap-velocity vector on a flight from face a to face b. The gap map is

    P_ab g = g − w g_b / w_b.

Its determinant between the two omitted-coordinate face charts is

    det P_ab = (−1)^(a+b) w_a / w_b.                 (1)

One direct proof is to delete row b and column a from I−w e_b^T/w_b. Its adjugate is w e_b^T/w_b, so the complementary minor is the displayed signed ratio. The case a=b gives the identity. The formula also follows by expanding in the one changed coordinate; it is not a positivity assumption.

At the source, w_a>0 because the source pair has just separated. At the target, w_b<0 because the target pair is closing. For faces a_0,...,a_m, multiplication of (1) gives

    sign(det map) = (−1)^(m+a_0+a_m).

For a literal return a_m=a_0 this becomes (−1)^m. The absolute determinant is the product of opening-to-closing speed ratios. Because the final outgoing phase is the initial outgoing phase, the list of source opening speeds is exactly the list of all event outgoing separation speeds cyclically shifted. This proves Theorem B's product formula.

If the initial and final phases differ, the numerator includes the initial opening speed rather than the final one; the per-flight formula still applies. If the final face is reidentified with the initial face by a separate coordinate map C, multiply by det C. More generally, changing initial and final charts contributes det C_out / det C_in. A literal return written in the same chart at both ends is a conjugacy, so its determinant and sign do not change. The sign of an ambient relabeling permutation must not be used without checking its induced action on the actual face quotient.

For the five-signal stationary section, the initial/final pair is (L,messenger), the first gap is zero, and the remaining sorted gaps are (x,y−x,D−y). Their fixed invertible linear relation to (D,x,y) changes the representation by conjugacy. The same parity therefore holds in (D,x,y) and in the centered coordinates.

## 4. The singular obstruction and normalization

Theorem A makes the full three-coordinate homogeneous return N on a five-signal translation-quotiented section invertible. If

    N = λ diag(1,A),      λ>0,

then

    det N = λ^3 det A.

Consequently det A cannot vanish. There is no cancellation or normalization loophole: the first coordinate D is one of the complete section coordinates, and the scale multiplier is strictly positive and fixed.

The same conclusion holds for a normalized affine map w' = Aw+b when D'=λD; its homogeneous block form has determinant λ^3 det A. Thus a singular affine planar map is excluded too.

More generally, an invertible homogeneous section map with a nonconstant positive scale row induces an invertible projective map wherever that normalization is defined. It need not be a linear planar map, but it remains locally nonsingular. Discarding D without a scale normalization that records its projective role would instead be a projection and would be outside this argument.

For a literal m-event return with D'=λD and λ>0, Theorem B also gives

    sign(det A) = (−1)^m.

Thus an odd word is precisely what an orientation-reversing normalized planar return requires in this convention. It is feasible, as the next section demonstrates.

## 5. Explicit seven-event stationary-section primitive

### 5.1 Labels and rules

Use stationary labels L, X_0, Y, R. The marker X has additional labels X_pre, X_fast, X_post with speeds

    speed(X_pre)=−1/2,  speed(X_fast)=+2,  speed(X_post)=−1/2.

The equal speeds of X_pre and X_post are permitted because these labels never meet one another; they distinguish two phases.

Use four messenger labels

    Q_+: +1,   Q_setup: −3/2,   Q_middle: −1/4,   Q_cleanup: −1.

The seven rules, chronologically on the chamber, are

    1. {Q_+, X_0}       -> {Q_setup, X_pre}
    2. {Q_setup, L}     -> {Q_+, L}
    3. {Q_+, X_pre}     -> {Q_middle, X_fast}
    4. {X_fast, Y}      -> {X_post, Y}
    5. {Q_middle, L}    -> {Q_+, L}
    6. {Q_+, X_post}    -> {Q_cleanup, X_0}
    7. {Q_cleanup, L}   -> {Q_+, L}.

All seven input sets are distinct. Every rule has distinct incoming speeds and distinct outgoing speeds. Rule 4 does not involve the messenger, which continues with label Q_middle while X bounces at Y. Treating this event as a messenger phase transition would be an error.

The labels total 4 messenger labels, 4 X labels, and L,Y,R: eleven meta-signals. At the initial outgoing section the live labels are L and Q_+ at 0, X_0 at x, Y at y, R at D. Every rule consumes and emits two signals, and all labels return to these same section roles at the end.

Give every other input set with pairwise distinct speeds the identity output. This finite deterministic completion preserves cardinality, including for larger unprescribed input sets. It does not make an extra event part of the chosen complete binary word. No continuation at an accumulation point is asserted.

### 5.2 Exact event table

Write

    ξ = 5y/4 − x,          F = 2ξ/3 = −2x/3 + 5y/6.

Throughout the table L=0, Y=y, R=D. Only messenger and X positions are shown. All times are measured from the outgoing initial anchor contact, and the speeds are those in §5.1, so the initial messenger has speed +1.

| Event | Time | Messenger position | X position | Contact |
|---|---:|---:|---:|---|
| Initial outgoing section | 0 | 0 | x | L,Q_+ |
| 1 | x | x | x | Q_+,X_0 |
| 2 | 5x/3 | 0 | 2x/3 | Q_setup,L |
| 3 | 19x/9 | 4x/9 | 4x/9 | Q_+,X_pre |
| 4 | 17x/9+y/2 | (4x−y)/8 | y | X_fast,Y |
| 5 | 35x/9 | 0 | ξ | Q_middle,L |
| 6 | 35x/9+F | F | F | Q_+,X_post |
| 7 | 35x/9+2F | 0 | F | Q_cleanup,L |

The seven flight durations are

    x, 2x/3, 4x/9, (9y−4x)/18, (4x−y)/2, F, F.       (2)

The total duration is

    T_J = 23x/9 + 5y/3.

Every line segment in the table has exactly the prescribed speed. For example, from event 3 to event 4 the messenger moves with speed −1/4 and X with speed +2; from event 4 to event 5 the messenger keeps speed −1/4 and X has speed −1/2. These identities are verified by direct subtraction of the displayed rational linear rows.

### 5.3 Complete chronology and no omitted contacts

Assume 0<x<y<D and y<4x. Every duration in (2) is strictly positive. Also

    0 < ξ < y,      0 < F < y,

because ξ=5y/4−x > y/4 and ξ<y is equivalent to x>y/4.

Use the fixed spatial order L,Q,X,Y,R. At each listed event exactly its indicated adjacent gap is zero; every other gap is positive:

* Initially the only zero gap is L/Q; x>0, y−x>0 and D−y>0.
* At event 1 the only zero gap is Q/X; the other gaps are x, y−x and D−y.
* At event 2 the only zero gap is L/Q; 0<2x/3<y.
* At event 3 the only zero gap is Q/X; 0<4x/9<y.
* At event 4 the only zero gap is X/Y. The messenger is at (4x−y)/8>0 and is less than y, since 4x<4y<9y.
* At event 5 the only zero gap is L/Q; 0<ξ<y.
* At event 6 the only zero gap is Q/X; 0<F<y.
* At event 7 the only zero gap is L/Q; 0<F<y.

On each flight every gap is affine in time. A gap that is positive at both endpoints remains positive throughout. The departing contact gap is zero at its initial endpoint, has strictly positive outgoing derivative, and is positive at the next endpoint. The arriving contact gap is positive at the initial endpoint and zero only at the final endpoint. Thus every adjacent gap stays strictly positive in the open flight. Nonadjacent signals cannot meet without an adjacent gap vanishing. This proves that there is no omitted collision or simultaneous remote contact.

In particular, after event 4 X moves left faster than the messenger and could in principle catch it. The above argument does not ignore that possibility: their gap is positive at event 4 and equals ξ>0 at event 5, and is linear between them. It cannot vanish first. The untouched R marker also remains strictly beyond y throughout.

### 5.4 Necessity and first failure

On the initial ordered section 0<x<y<D, the first three events and their trajectories up to event 3 have the stated strict chronology independently of the added guard y<4x. After event 3, the prospective X/Y contact occurs after (9y−4x)/18 time and the messenger/L contact after 16x/9 time. Their difference is exactly the fifth duration in (2).

If y=4x, the X/Y and messenger/L contacts are simultaneous at different positions. If y>4x, messenger/L occurs first, so the specified complete word with event 4 before event 5 fails. This is a first-failure argument; it never continues a hypothetical trajectory through an earlier wrong collision. Hence the exact complete-word chamber is precisely

    0<x<y<D and y<4x,

equivalently

    0<y<D and y/4<x<y.

On D=1 this is a bounded open rational polygon. The standard center (1/3,2/3) satisfies every guard strictly.

### 5.5 Return, parity, and phase closure

At event 7 all four markers are stationary again, Q_+ is outgoing at L, and the marker position is F. The homogeneous return in (D,x,y) is

    M_J = [[1,0,0], [0,−2/3,5/6], [0,0,1]].

It fixes x=D/3,y=2D/3. Therefore its centered action is exactly diag(1,J), with

    J = [[−2/3,5/6],[0,1]],
    J^(-1) = [[−3/2,5/4],[0,1]].

The seven outgoing/incoming pair-speed ratios are

    1, 2/3, 3/2, 1/4, 4, 2/3, 1.

Their product is 2/3; odd parity gives determinant −2/3, agreeing with M_J. No phase label or moving-marker assumption remains at the section. This is a counterexample to any proposed orientation-preservation obstruction in the model of the preceding compiler.

## 6. Static exact evidence

The newly written `static_algebra.py` was displayed and inspected before execution. It uses only Python's standard-library rational arithmetic. It imports no earlier constructor or local module.

The script checks the supplied table as rational row identities: each declared endpoint difference equals its fixed velocity times the declared time difference. It does not select the next collision, search over candidate event times, iterate a numerical trajectory, or execute a stored machine schedule. To certify the whole open chamber rather than sample points, it writes

    r=x−y/4>0, s=y−x>0, t=D−y>0,
    (D,x,y)=((4r+4s)/3+t, (4r+s)/3, (4r+4s)/3).

Every required strict gap and flight-duration row becomes a nonzero nonnegative rational combination of r,s,t. The contact rows are identically zero. This gives an exact finite symbolic certificate of all the inequalities used in §5.3.

Additional checks verify the centered conjugacy, inverse matrix, determinant, speed-ratio product, and center-strict chamber rows. Ninety exact finite instances check the complementary-minor identity used in (1); the general identity is proved in §3 and does not rely on those fixtures.

The run passed. `evidence/static_checks.json` records the exact coefficients and the SHA-256 of the inspected checker. These are arithmetic support, not a proof-assistant formalization.

## 7. Complete GL₂(Q) realization

Let A be a rational 2 by 2 matrix and λ>0 rational.

If det A>0, use the preceding five-signal compiler directly.

If det A<0, define

    B=J^(-1)A.

Then det B>0. First run the preceding compiler for (B,λ), and then the seven-event primitive J. The centered return is

    diag(1,J) [λ diag(1,B)] = λ diag(1,A).

The positive compiler restores the stationary-marker section, so the interface is exact. Its final scale λ does not change J's normalized guards. If P_B is its exact normalized chamber and P_J is the exact normalized chamber of J, the concatenated word has exact chamber

    P = P_B intersect B^(-1) P_J.

This is a bounded open rational polygon, and the origin in centered normalized coordinates lies strictly inside both factors. Necessity and sufficiency follow from the exact chambers of the two blocks: any failure in the first block invalidates its word; after a successful first block, failure of J's guards invalidates the appended word. Pullbacks are rational strict affine rows.

For a literal composite finite machine, use disjoint messenger phase labels at the block interface and wherever needed. Do not blindly reuse J's standalone Q_+ label as the positive compiler's entry label: that would make its X_0 rule ambiguous at the wrong phase. The event-4 marker-only collision leaves the then-current messenger label unchanged. Fresh copies of phase labels, and distinct X_pre/X_post labels, produce an unambiguous finite rule table; the final label is identified with the entire macro's initial messenger label. Every explicit collision is binary with distinct incoming/outgoing speeds, and identity completion handles every other input set. No extra live signal is introduced by these finite label copies.

The negative-determinant extension adds exactly seven events to the selected positive compiler word. That preceding word has even length, so the result has odd length, as required by Theorem B. No minimal word-length or minimal meta-signal claim is made.

The original normalized infinite-word identity is retained:

    K(A,P)= intersection over n>=0 of A^(-n)P.

Here P is the exact chamber of this actual composite word, not an arbitrarily chosen guard polygon or its closure. The preceding time argument also survives. The positive compiler takes at least 2D; J takes less than (38/9) times its entrance scale because x,y<D there. After the λ-scaled positive block this adds less than (38λ/9)D. Thus the total macro duration is bounded above and below by positive constants times D. Every infinitely valid run is Zeno exactly when 0<λ<1, and the rational cyclic-subspace accumulation-time argument from the preceding report applies unchanged. There is still no claimed continuation through the accumulation point.

If det A=0, Theorem A and §4 exclude the requested full-section return. This proves Corollary D in both directions.

## 8. Positioning against primary literature

This packet makes no novelty, priority, or exhaustive-search claim. The appropriate description of Theorem A is a signal-machine specialization of standard transverse constant-flow section geometry.

1. **Signal-machine definitions and distinct speeds.** Becker et al., *Abstract Geometrical Computation 10: An Intrinsically Universal Family of Signal Machines*, §2, Definitions 1–2, PDF pp.4–5, [primary manuscript](https://arxiv.org/pdf/1804.09018). The speed function is attached to labels; incoming and outgoing collision sets each have distinct speeds. Global speed injectivity is not required. Configurations can contain the same label at different positions, and the operational definition uses the smallest positive meeting time. This supports the distinction between label types, live signals, and repeated occurrences used above.

2. **Global reversibility is a different property.** J. Durand-Lose, *Reversible conservative rational abstract geometrical computation is Turing-universal*, CiE 2006, LNCS 3988, pp.163–172, §2, Definitions 1, 3–4, manuscript PDF pp.3–5, [author manuscript](https://www.univ-orleans.fr/lifo/membres/Jerome.Durand-Lose/Recherche/Publications/2006_CiE.pdf). It formulates reversibility using injective collision rules and at least two outgoing signals, with an accumulation qualification. Number preservation here is a special case of its energy-based conservativeness. Its rational-machine convention also restricts starting positions to rationals. Our open real chambers are the natural rational-coefficient geometric extension; all rational inputs in them remain legitimate rational configurations.

3. **Close geometric precedent.** H. N. Alishah, P. Duarte and T. Peixe, *Asymptotic Poincaré Maps along the edges of Polytopes*, Nonlinearity 33(1), 2020, §5, manuscript PDF pp.21–24, [primary manuscript](https://arxiv.org/pdf/1411.6227). Equation (5.2) gives the same kind of oblique constant-flight projection; Proposition 5.4 identifies its trajectory domain; Definition 5.7 and equation (5.5) compose such maps along a fixed itinerary. The proof of Proposition 5.10 explicitly invokes local linear isomorphisms. Its setting is polytope skeleton flows, not the present signal-machine compiler, but it prevents presenting the underlying linear algebra as unprecedented.

A bounded primary-source search found no exact signal-machine statement matching all of Theorems A–C and their parity convention. That is a limitation of this search, not evidence of novelty. The elementary seven-event construction is supplied with a complete direct proof so the conclusion does not depend on historical positioning.

## 9. Meaningful limits and next target

The result resolves the sign/singularity gap in the stated full five-signal model: every invertible rational planar matrix is realizable, and singular matrices are not. The distinction is geometric invertibility, not orientation preservation.

It does not prove a lower bound on the number of live signals in models with additional geometric encodings, clocks, labels carrying parameter-dependent data, projected observations, or nonstandard sections. The four-active-signal version of J is not a planar normalized-section compiler: removing R also removes one homogeneous section degree of freedom.

It does not establish a single unchanged finite rule table for all A, uniform word length, polynomial-size compilation, minimal number of speeds, or injectivity of the machine's global rule map. The finite label completion outside the selected word is only deterministic and number-preserving.

The next structural target is the full three-coordinate homogeneous return problem: characterize rational invertible maps N on (D,X_c,Y_c) when the positive final scale D' may depend on shape, rather than requiring D'=λD. Their normalized actions are projective planar maps, so the fixed-scale planar classification does not automatically settle their infinite-word geometry. The necessary open positive-section compatibility must be stated explicitly. A separate concrete target is compilation efficiency for arbitrary GL₂(Q) inputs. Neither task should assume that the present elementary factorization or seven-event reversal is optimal. Ordinary full-coordinate dimension counting already explains why five live signals are needed to carry a two-dimensional normalized collision section; exotic lower-population encodings would require a separately specified model, not an unqualified new lower-bound claim.
