# Independent adversarial review: mass at most four in finite dimension

Date: 3 October 2026

## Binding, independence and verdict

This review concerns `PROOF.md` in the frozen higher-dimensional particle-threshold research packet, with SHA-256:

`3e8eb41fe43b5b4b61d0e0a5b4bece3b01cf628f834a820ecc369f4da427b30a`

I performed a complete first reading and recorded `initial-assessment.md` before consulting the packet's existing `audit.md`. I subsequently compared the earlier audit and independently verified that its two previously identified wording issues are resolved in the bound proof. The original packet was not edited.

**Verdict:** I found no counterexample, missing dynamical case, circular enumeration, or fatal proof gap in the mass-at-most-four reachability and finite-pattern decision theorem, under its precise hypotheses. The proof gives a valid ordinary mathematical argument for every finite dimension, uniformly effectively in the dimension and supplied local rule. Three implementation-level clarifications would improve the article; they are detailed below and do not require changing the theorem.

The review covers Sections 1–12 and the claimed stationary-frame untimed Presburger normal form. It does not independently reprove the inherited five-particle universal construction, investigate literature priority, implement a general CA compiler, or provide a proof-assistant formalization. In particular, the lower-bound decision theorem passes this review; the sharpness statement remains conditional on the cited five-particle source releases having their stated properties.

## 1. Model and independence

The hypotheses do substantive work:

- Strictly positive integer weights outside the vacuum give at most four occupied sites and prohibit hidden zero-cost memory
- At most one weight-one symbol means an isolated mass-one configuration has a single deterministic displacement, with no internal particle state
- Translation equivariance and time independence allow an isolated trajectory to be reused at any anchor and time
- Finite range and quiescent vacuum keep finite computations finite

When the unit symbol exists, its output must be exactly one copy of that symbol. Passing to the translating frame therefore makes each isolated unit stationary. The enlarged radius bound is valid.

The independence claim must include the first-contact configuration, not the step after it. It does. If components at time t have pairwise distance greater than 2S, their radius-S influence supports are disjoint at time t+1, and the full output equals the disjoint isolated outputs. Thus hypothetical independent trajectories may be followed through their first configuration at distance at most 2S. Only the next update requires the joint local rule. This rules out skipped collisions and duplicated mass at a first-contact seed.

Normalization by a lexicographically first occupied site is translation equivariant in every finite dimension. A fixed diameter bound and mass bound give a finite, effectively enumerable set of normalized labeled configurations.

## 2. Mass-two invariant

I checked both weighted and two-unit cases. A weight-two singleton's successor lies in its radius-S cube. For two units with separation greater than S, the original sites retain the unit symbol; mass conservation then forbids any other output. For separation at most S, a newly occupied site outside the two originals must see both units. The two originals themselves belong to the intersection of their radius-S cubes. Each coordinate width of that intersection is at most 2S. Hence the diameter invariant is valid even for anisotropic local rules and in dimensions greater than one.

This is a finite normalized shape automaton with translation increments. Repetition gives a finite transient, phase period and integral drift vector. A zero drift produces a truly periodic positioned packet; a nonzero drift produces a translated-periodic packet. No reversibility assumption is used.

An arbitrary mass-two component used later really does satisfy this invariant initially: it is either one weight-two site or two unit sites joined by an edge of length at most 2S.

## 3. Completeness and effectivity of the mass-three library

Outside the diameter-4S core, a mass-three configuration cannot be connected. Its only possible partitions are a mass-two component plus a unit, or three units. Three separated units are fixed. In the former case the dimer has the complete finite-phase profile just proved.

For one phase and one period variable k, core membership is a conjunction of inequalities

    -4S <= (p_i + k D_i) - u_i <= 4S

for each packet support point p and coordinate i; the packet's own diameter is already at most 2S. Each condition is an integer interval, a tautology or a contradiction, so their intersection and its least nonnegative integer are computable. The finite transient is separately checked. Taking the earliest actual time over phases is correct.

The calculation cannot be invalidated by an interaction before the calculated core entry. Such an interaction would first create a connected dimer-plus-unit configuration, of diameter at most 4S, and therefore an earlier core entry. This is the required first-event argument.

Every normalized core state therefore has a computable next core return, or a certified independent tail. The finite graph preserves actual elapsed time and translation. Repeated core states give equality of entire configurations up to translation; determinism then propagates this equality through all intervening excursions, not merely to sampled states. Thus a compact profile contains every intermediate phase, including any detach-and-recombine behavior.

The encounter library is finite because connected mass-three seeds have diameter at most 4S. For tagged contact seeds, the tag can simply name an occupied unit coordinate. It is bookkeeping, not a persistent physical label. Untagged connected triples are also needed for the arbitrary 3+1 dispatch, and their profile is the same mass-three construction.

For a nonzero-drift independent dimer tail, a coordinate with nonzero drift eventually separates the entire packet from the residual unit in every phase. Taking the maximum of finitely many phase thresholds yields an effective emission checkpoint. The packet is periodic from that checkpoint and never again approaches its source within 2S. If the drift is zero, the entire triple is eventually periodic and is compact. A tail of three stationary units is also compact. Thus the two library outcomes are exhaustive.

## 4. Prefix safety and the role of B

The intended definition of B is sufficient, provided all seed-prefix coordinates are measured in the original normalized seed-anchor frame. This should be said explicitly in the article.

Let a be a seed's normalized occupied anchor. If the remote unit b satisfies ||b-a|| > B+2S and every isolated seed-prefix occupied coordinate stays within B of a, then every prefix configuration is independent of b. This includes its checkpoint and ensures the remote unit remains farther than 2S from both the residual unit and the launched packet.

In arbitrary 3+1 dispatch, the connected seed has diameter at most 4S. If the whole configuration has diameter greater than W and W>B+6S, a remote-to-seed distance exceeds W, so

    ||b-a|| > W-4S > B+2S.

The same argument applies after a nonsimultaneous dimer contact in the 2+1+1 partition. Thus the ordinary-core diameter criterion implies exactly the prefix safety needed by the library; there is no extra unproved geometric separation assumption.

A compact triple has phase diameter at most 2B. Its first contact with a remote unit has full diameter at most 2B+2S, regardless of how long the compact object has traveled or whether its phase orbit temporarily disconnects. Consequently compact travel cannot preserve an additional unbounded gap after returning to contact. An exact miss is a valid independent terminal alternative.

## 5. Arithmetic rays and first-contact data

For an emission profile Q_r+kD, target contact is exactly membership in the union of occupied-site radius-2S boxes:

    v = a + kD,  a in Q_r + [-2S,2S]^d.

This uses actual support rather than the expanded bounding hull. The distinction is essential in higher dimensions. The finite offset list records phase r, and minimization uses the actual time r+pk. Simultaneous sites and phase witnesses do not lose configurations or introduce an arbitrary physical choice.

Writing D=m nu with nu primitive and choosing an integer functional lambda(nu)=1 yields a unique decomposition. Beyond the maximum absolute lambda-offset, all candidate counts on the drift-facing sign are nonnegative. Eligibility is determined by the finite transverse component and scalar residue modulo |m|. Every eligible candidate has the same time slope p/m, so minimization selects the smallest constant term, independently of the large scalar magnitude. The complete seed relative to the target is Q_r-a and the target unit at 0. Thus the flight count does not survive as an additional hidden control variable.

On the opposite sign there is no large successful candidate. Off-ray vectors also miss, even if a Euclidean or coordinatewise direction appears favorable. The proof explicitly retains these misses.

## 6. Nonparallel switches

The sign in the update equation is correct. With incoming source A, target B and residual marker B+c after the library prefix,

    v=B-A,  v'=A-(B+c)=-v-c.

For two successful flights this gives

    kD + k'D' = -(a+a'+c).

For nonparallel D,D', an integer-coordinate 2 by 2 minor is nonsingular. Its Cramer solution uniquely determines the rational pair (k,k'). Integer and nonnegative checks, followed by checking every remaining coordinate, are sufficient and effective. Taking every finite offset/profile/shift combination can overestimate the exceptional set but cannot miss an actual switch.

This is stronger than a qualitative angular argument. The exceptional set can be very large: with P=1,000,000, D=(P,1), D'=(-P-2,-1), and right-hand side (0,2), the unique nonnegative solution is k=P+2, k'=P, with ||kD||=1,000,002,000,000. The exact determinant construction handles this; a small offset-only radius would not.

Consecutive successful nonparallel flights are therefore impossible outside the computed exceptional bound. An unsuccessful nonparallel launch is terminal and does not start an independent second counter. A compact triple is handled separately, also without a second live counter.

## 7. Threshold construction without circularity

The order of construction is valid: mass-two profiles, mass-three seed library, B, emission offsets, marker shifts, rational lines/functionals and nonparallel exceptions all precede N and W. None requires enumerating the later mass-four ordinary core.

The large-gap safety margin is enough even when lambda has mixed or large coefficients. Since |lambda(v)| <= ||lambda||_1 ||v||, taking

    N > ||lambda||_1 (B+10S+1)

forces the remote-to-target distance beyond B+10S+1 whenever x=|lambda(v)|>N. The target lies within 4S of the normalized triple-seed anchor, leaving more than B+6S+1 to that anchor and hence ample prefix independence. The other finite maxima protect scalar sign, marker order and exceptional switches.

Successful launches with small or zero scalar separation are a finite family. Explicitly, n=lambda(a)+km and |n|<=N imply

    0 <= k <= (N+|lambda(a)|)/|m|.

Enumerating these integers for every offset/profile gives the entire small-success set, including n=0 and lambda-order ties. Adding the finite launch shapes makes its full diameter maximum computable. This supplies an explicit version of the proof's instruction to include small or degenerate-sign cases in W.

A launch that misses need not be forced into the ordinary core. It may be sent to its certified independent profile. Crucially, the two residual monomers are still mutually farther than 2S at such a checkpoint: this follows from the prefix safety margin, not merely from the scalar guard. Thus a missed-flight tail does not overlook a subsequent monomer-monomer interaction.

## 8. Deterministic finite control and cycle analysis

At a live checkpoint, the finite mode records line, source side, full packet profile/launch phase, transverse offset and any needed seed tag. Adding x modulo the common multiple of drift integers determines the complete first-contact seed and its library outcome. No absolute position or elapsed clock is used by the autonomous CA.

Only the contacted marker changes by a bounded, library-selected vector c. The lambda-order is preserved above N. Therefore x changes by a fixed scalar, the left anchor changes by a fixed vector, and the transverse part changes by a fixed vector that is again either an eligible finite transverse value or a miss. Absolute anchor displacement is output, not a control variable.

The corrected finite-control statement is appropriately narrow: live continuation versus a compact/emission exit is determined by finite mode, residue and lower-bound guards. Whether an already selected compact triple later hits the other marker can depend on the actual scalar x; the proof separately calculates that event. It does not incorrectly require this latter decision to be residue-only.

For a repeated enlarged mode:

- Zero counter change repeats the whole launch shape up to translation, and autonomy repeats every intermediate phase
- Positive change preserves all future lower guards and repeats the same itinerary forever
- Negative change eventually violates one of finitely many linear lower guards; its maximum repeat count is computable, and the residual prefix exits live to ordinary or terminal

The last alternative is not incorrectly restricted to ordinary exits. Above N, a new seed type cannot spontaneously appear on a repeated cycle. Every ordinary-state return is positive in time. Finitely many normalized ordinary states, together with this live-cycle trichotomy, suffice for termination.

## 9. Arbitrary input dispatch and omitted-looking cases

All mass-four partitions are covered. Two dimers are handled with a common phase period; first contact is a finite union of coordinatewise integer interval tests, and its full diameter is at most 6S. In 2+1+1, actual first-contact times with both monomers are compared. A simultaneous contact produces a connected four-mass configuration; a single contact gives exactly a library seed plus one remote unit. Four separated monomers are fixed. Connected mass four is ordinary.

One easy case is implicit rather than stated at its point of use: an arbitrary initial dimer can have D=0, whereas Section 5 presents nonzero-drift emission rays. For such a dimer in 2+1+1 dispatch, inspect the finite transient and one complete eventual positioned period against each marker. A missed periodic contact stays missed forever. This is a finite computation already supplied by Lemma 2.1; spelling it out avoids a literal domain mismatch in the reference to Section 5.

The no-unit case is correct. With minimum positive weight at least two, mass at most four occupies at most two sites. An isolated weight-two or weight-three state cannot split and is a finite-state walker. Outside the diameter-2R core, the only nontrivial two-object configuration is two weight-two walkers. Common phases give the same first-return interval algorithm. Weight-four splitting begins within the core, and all finite core dynamics are included. The R=0 convention is harmless.

## 10. Complete orbit formulas and absolute observations

Every phase in an expanding cycle is retained. In a library-prefix phase, all coordinates are affine in cycle index n. In a free-flight phase they are affine in (n,j), with j constrained by a linear precontact bound. Contact endpoint duplication, if retained by both adjacent phases, is harmless. Finite phase labels and at most four occupied sites give an ordinary Presburger encoding of the stationary-frame untimed orbit, including exact labels and prescribed zero sites.

The repeated cycle has fixed positive counter gain Delta and fixed anchor update E. Hence x and the anchor are affine in n. Each flight duration has slope alpha>0 in x. The cycle duration is therefore affine in n with strictly positive slope, so accumulated section time is quadratic with positive leading coefficient. The packet-period parameter j is at most affine in n. All support coordinates in the stationary frame consequently satisfy a uniform linear norm bound K0+K1 n throughout the entire cycle, not just at launch sections.

Restoring a nonzero isolated drift delta adds t delta. For a coordinate with delta_i>0, t>=T_n gives a uniform lower bound delta_i T_n-K0-K1 n. For delta_i<0, it gives the required uniform upper bound delta_i T_n+K0+K1 n. The inequality direction is correct in both cases. Quadratic dominance yields a computable permanent cutoff beyond any finite target window, uniformly over every flight and prefix phase.

Thus any anchored observation requiring a nonzero symbol must occur before a computable finite time; exhaustive simulation is effective even if impractical. A wholly zero finite pattern occurs afterward. Empty exact targets are settled separately by conservation. Translation-invariant observations are unchanged between F and G. For delta=0, the stationary-frame Presburger description already suffices. No unrestricted quadratic Diophantine satisfiability claim is being smuggled into the argument.

For independent or whole-translated-periodic tails, common phase periods make coordinates and time affine in one integer variable. Prescribed zero sites are finite non-equality conditions against the at-most-four occupied sites. These observations also handle arbitrary higher-weight labels and disconnected patterns.

## 11. Clarifications requested for the article

These are exposition/implementation clarifications, not corrections to a false assertion or evidence against the theorem:

1. Explicitly dispatch zero-drift initial dimers by finite transient plus one full period
2. Specify the seed-anchor frame used for B and account for residual-unit reanchoring by finite difference offsets or an enlarged B
3. Display the finite integer bound for |lambda(a)+km|<=N, including lambda-order ties, when defining W

They have been incorporated into Report 29. The frozen research proof remains unchanged.

## 12. Independent finite checks

`check_independent_arithmetic.py` contains fresh finite tests written for this review. In this portable delivery its single proof binding hash is adapted to the delivered proof copy; source lineage records both hashes. It does not import the original packet's arithmetic checker. It uses explicit exceptions rather than Python assert statements, so optimized mode does not disable its checks. Both normal and optimized runs passed and produced byte-identical JSON receipts.

The checks cover:

- 4,335 comparisons between exact phase-ray contact and direct support enumeration, including zero drift, both drift signs, phase ties and misses
- 2,172 checks that fixed transverse data and scalar residue preserve the first-contact seed and affine elapsed-time difference
- 7,040 recoveries of nonparallel flight-count solutions in three dimensions, plus rejection of an inconsistent remaining coordinate
- A large near-parallel exceptional vector of norm 1,000,002,000,000
- 58,800 small-launch finiteness checks, including large geometric direction coefficients
- 28,800 indices beyond outward quadratic cutoffs
- An expanded-bounding-box false positive rejected by the actual-support contact test

The abstract phase data intentionally test the arithmetic identities independently of whether those particular profiles arise from a CA. These tests are supplementary checks, not a proof of the classification theorem or a general-rule execution test.

Run with:

    python check_independent_arithmetic.py --proof PROOF.md
    python -O check_independent_arithmetic.py --proof PROOF.md

The script first verifies the reviewed proof's exact SHA-256. The receipts contain the source hash and arithmetic results, without environment-specific runtime paths.

## Final assessment

The main mathematical risks posed in the audit request are addressed: the mass-three library is exhaustive and effective; N and W are noncircular; live evolution has genuinely finite deterministic control with one additive counter; nonparallel successful switches are effectively bounded; and absolute-frame finite observations admit the claimed cutoff. No new theorem restriction or genuine correction was identified. Publication-level claims should continue to distinguish an ordinary mathematical proof from formal verification, and the inherited five-particle upper bound from the independently reviewed lower-bound argument.
