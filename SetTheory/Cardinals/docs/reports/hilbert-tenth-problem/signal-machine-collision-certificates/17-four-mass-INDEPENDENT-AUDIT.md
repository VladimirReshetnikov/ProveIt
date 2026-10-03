# Independent audit: four mass units with one unit label

Audit date: 3 October 2026. This review concerns the revised mathematical argument presented in the report, its companion `finite-seed-section-lemma.md`, and the explicit shuttle implementation. The mass-three theorem is imported as established. No literature-priority conclusion is part of this audit.

## Verdict

**The revised argument supports the stated decidability theorem.** I found no mathematical counterexample or remaining obstruction in the reduction to one additive gap, the section-machine termination, the fixed-input untimed Presburger description in the stationary frame, or the original-frame anchored-observation cutoff. This is an independent mathematical audit, not a proof-assistant verification.

One genuine threshold inconsistency in the earlier draft has been corrected. With the former definition “packet-plus-unit span at most 4S,” a singleton packet at 0 and units at −4S and 4S give simultaneous encounters while the complete span is 8S. Thus a full-core threshold assumed only to be at least 6S did not automatically contain every simultaneous encounter. The revised definition “distance at most 2S from an occupied packet site” gives a connected mass-three seed and makes a simultaneous contact a connected mass-four configuration of span at most 6S. Alternatively the old convention could have been retained with adequate larger padding, but mixing the conventions was not justified.

The finite-seed note also supplies two important details that should remain in any formal version:

1. Its constants B,N,W are constructed in a noncircular order from a fixed connected mass-three seed family
2. The contacted unit's coordinate is tagged in the entry seed, because three indistinguishable unit symbols do not themselves identify which one was the pre-existing marker

## 1. Exhaustiveness and the proposed missing cases

At mass four the component mass partitions are exactly 4, 3+1, 2+2, 2+1+1, and 1+1+1+1. Components use occupied-site distance at most 2S. A connected component of mass m has at most m occupied sites and diameter at most 2S(m−1).

The imported mass-two diameter invariant is decisive. A mass-two packet cannot split into two different 2S-components. In particular it cannot leave one unit behind, send another to a remote marker, and retain two independent unbounded geometric gaps. Its possible weight-two labels and its possible internal two-unit geometries are finitely many normalized states.

A mass-three local experiment can fragment, transfer which physical unit survives as the marker, detach and recollide repeatedly, or have a long finite transient. None of these defeats the finite library: each connected entry seed has a complete effective isolated mass-three orbit profile. Every finite excursion belongs to a finite prefix or a bounded phase of a coherent translated cycle. An actual unbounded internal gap belongs to an emitted mass-two packet plus a stationary unit, after prolonging to the outward, nonzero-drift periodic regime. A zero-drift separated tail has bounded geometry and can be classified as coherent.

A coherent translating mass-three object must be kept distinct from a bounded-duration scattering prefix. It either remains independent of the fourth unit forever or comes within 2S of it while all three local masses still have uniformly bounded diameter. The latter is a bounded full-mass reset. It cannot transport a second unbounded gap through the reset.

Two separated mass-two packets have independent finite-phase profiles. Their first contact, if any, puts all four masses within 6S. They therefore cannot create an indefinitely recurrent two-gap regime outside the full core.

Four isolated unit components are fixed in G. If no unit label exists at all, a mass-two or mass-three singleton is a finite-state walker. Mass four has either one weight-four site or two weight-two walkers; a finite encounter core and the usual finite-profile first-hit construction settle that case separately.

## 2. The finite constants actually justify local independence

Let B bound absolute coordinates of every finite prefix and initial-period phase representative of every normalized connected mass-three seed. This includes the residual marker coordinate. It does not bound all translates along an indefinitely traveling coherent orbit; only its initial representatives and therefore its diameter are bounded.

With N=4B+12S and W=N+2B, the inequalities needed by the compiler are valid:

- A seed has diameter at most 4S. If its union with the fourth unit is outside W, the remote unit is farther than W−4S>B+2S from the seed anchor
- During the whole finite prefix, including the selected launch instant, all seed support is within B of that anchor, so the remote unit stays farther than 2S from every occupied seed site
- At contact during a live section, the target marker b and new seed anchor a' satisfy |a'−b|≤4S. The old marker is at least D−4S>N−4S>B+2S from a', so the entire next finite local prefix is independent of it
- The new residual marker differs from the contacted marker by at most B+4S. Since D>N>B+4S, marker order cannot reverse
- A small-gap emission D≤N has span at most N+2B=W
- A coherent mass-three phase has diameter at most 2B, and its first proximity to the fourth unit yields span at most 2B+2S<W

These bounds explicitly cover long prefix durations. Independence is geometric at every time, not an inference from the duration being small.

The coherent-tail first-contact calculation must retain each occupied phase coordinate (or equivalent exact phase support data). Compact support may have holes, but a finite union of linear interval conditions suffices. If a coherently drifting object moves from one side of the fourth unit to the other, finite propagation forces a proximity event before it crosses; it cannot teleport over that unit's entire 2S neighborhood.

## 3. Exact residue arithmetic and bounded marker updates

Reflect an inward flight so its packet displacement v per period P is positive. In phase r, let its left edge relative to the source marker be h_r+kv and its diameter be d_r≤2S. Contact with the target marker at distance D is exactly

D−2S−d_r ≤ h_r+kv ≤ D+2S.

This interval criterion is exact even for a two-unit packet: its internal gap is at most 2S, so the 2S-neighborhoods of its occupied endpoints overlap.

Write D=rho+mv, with 0≤rho<v. Define

kappa_(r,rho)=ceil((rho−2S−d_r−h_r)/v).

A phase has a valid first candidate precisely when

h_r+kappa_(r,rho)v ≤ rho+2S.

For a valid candidate, k=m+kappa_(r,rho), and its time is

P m + r + P kappa_(r,rho).

The high-gap threshold makes these k nonnegative. Taking the smallest candidate is therefore a comparison of finitely many constants depending only on rho. At least one candidate exists: the packet begins on the near side, has nonzero drift toward the target, and cannot cross without a proximity event by finite propagation.

It follows that the first-hit phase, the tagged entry seed, and the entry geometry relative to the target depend only on the finite launch type and D mod v. The flight duration is affine in D with positive coefficient P/v. Adding the fixed local prefix gives the asserted affine macro duration.

If the target is the right marker and the local outcome shifts it by beta, the continuing update is D'=D+beta, L'=L. If the target is the left marker, it is D'=D−beta, L'=L+beta. These formulas do not track unit identities. An outward re-emission is terminal; an inward re-emission continues; a coherent outcome terminates or resets globally. Thus every continuing high transition has exactly one additive gap counter, with a separate untested translation coordinate.

A common multiple M of the nonzero packet displacements is sufficient. Including D mod M in finite control ensures that the gap difference Delta on a repeated control is divisible by M. Every repeated cycle then has the same residue itinerary. No extra temporal phase counter is hidden here, because the only remote mass-one label is stationary and has no internal state.

## 4. Section-machine termination

The revised low dispatch is complete and has positive elapsed time: take one exact step, return a W-bounded state if appropriate, otherwise classify components and calculate their next contact or terminal profile. The next seed is either globally bounded or safely isolated by the inequalities above. A live high edge has a nonempty remote flight.

For a repeated high control, write the gap at the i-th intermediate high section in a cycle as D+c_i. Then its gap on the n-th repetition is D+n Delta+c_i.

- If Delta>0, every high guard valid in the first traversal remains valid on every later traversal
- If Delta=0, the complete launch configuration repeats up to translation; determinism and translation equivariance give the complete subsequent orbit identity, including intermediate times
- If Delta<0, the inequalities D+n Delta+c_i>N determine a finite interval of allowed repetition counts. Its last integer is computable. The remaining proper cycle prefix reaches a low state

A high excursion cannot visit infinitely many distinct finite controls without repetition. There are finitely many normalized low states. Repeating a low state again gives a complete translated-periodic orbit. These facts prove termination of the analysis; arbitrary anchor drift does not invalidate it because the rule and all guards are translation invariant.

One presentation clarification is advisable: the geometric sets “span≤W” and “live launch with D>N” can overlap. The compiler should state an explicit representation convention, e.g. an emission with D>N is tagged high even if its span is at most W, whereas an ordinary low dispatcher uses the span test. Overlapping eligible representations are harmless, but the chosen dispatch must be deterministic. They need not be incorrectly claimed to be disjoint geometric sets.

## 5. Expanding-cycle geometry, time, and observations

On an expanding high cycle, section gap and left-marker position are affine in the cycle count n. Finite local prefixes therefore have positions affine in n. In a free-flight phase, introduce the packet-period count j. All occupied positions are affine in (n,j), and the allowed j range is given by linear inequalities. A finite disjunction over cycle edges and phases gives the fixed-input untimed Presburger reachable-configuration set in G.

This argument does not retain time as an affine variable. If the cycle duration is A D+B with A>0 and D_n=D_0+n Delta, then

T_n=T_0+(A Delta)n(n−1)/2+(A D_0+B)n.

The coefficient A Delta is positive. At every intermediate time in cycle n, all G-support is contained in

[L_0+nE−C, L_0+nE+D_0+n Delta+C]

for one computable C. This follows from the finite within-cycle marker shifts, uniformly bounded local prefixes, and the phase-bounded packet overshoot before first contact. It is a bound on every flight time, not merely on section times.

For F^t=tau_(delta t)G^t and t in cycle n:

- If delta>0, the minimum occupied coordinate is at least delta T_n+L_0+nE−C
- If delta<0, the maximum occupied coordinate is at most delta T_n+L_0+nE+D_0+n Delta+C

The first bound tends effectively to +infinity and the second to −infinity. A rational quadratic inequality gives a computable cycle index beyond which a specified finite window is never occupied. Thus anchored occurrence of a pattern containing a nonzero symbol, or anchored reachability of a nonempty exact target, reduces to a finite prefix. All-zero anchored patterns occur after the cutoff. Vacuum targets are decided by conservation. An empty pattern is immediate.

For delta=0, use the untimed Presburger set directly. Anywhere-pattern occurrence and reachability up to translation are invariant under the frame shift and likewise reduce to G. Zeros in mixed patterns must, as the draft says, exclude every occupied coordinate at the corresponding pattern site. Exact reachability still compares the whole finite support, not only the target window.

The theorem concerns a fixed input at a time. Nothing in this audit establishes a uniform timed Presburger formula in all initial gaps, or a unique-witness quartic compiler from decidability alone.

## 6. Independent shuttle check

The implemented weighted rule has labels u,R,L of weights 1,2,2. An active heavy center has no other heavy center within distance 4. Each rewrite touches only coordinates in [x−1,x+2], so distinct active rewrite supports are disjoint. Each rewrite preserves its local mass. Inactive heavy sites and all unaffected sites remain unchanged. Thus conservation holds for every finite configuration, not just the tested configurations.

An output coordinate can depend on a rewrite center at most two sites away, and its radius-four eligibility test, giving radius at most 6. The rule is translation equivariant and the vacuum quiescent. The two heavy labels share weight two, so the example is in the theorem's weighted class, not an ordinary injective numerical-state encoding.

For a section u@0,R@1,u@D, D≥3:

- At relative times 0≤s≤D−2, the configuration is u@0,R@(1+s),u@D
- At D−1≤s≤2D−3, it is u@0,L@(2D−2−s),u@(D+1)
- At time 2D−2 it is the next section u@0,R@1,u@(D+1)

Therefore D_k=d+k and T_k=k²+(2d−3)k. The anchored pattern u@0,R@1 occurs exactly at these section times. Its successive time gaps grow without bound, so this infinite time set is not ultimately periodic and is not Presburger-definable. This explicitly rules out importing the mass-three timed normal form unchanged.

Independent arithmetic checks in `audit_arithmetic.py` passed:

- 951 first-contact comparisons against direct phase enumeration
- 951 residue-preserving gap shifts of size 7·10^70
- 272 exact closed-form shuttle transition checks, including collision boundaries and section indices through 10^80
- 27,360 checks of the original-frame support bounds at every phase for positive and negative delta

These checks supplement the mathematical argument and do not replace it. Their receipt is `audit-arithmetic-results.json`.

## Remaining editorial actions

1. Explicitly dispose of mass≤3 by the imported theorem before the mass-exactly-four component classification
2. State the deterministic low/high representation convention mentioned above
3. Use a different symbol for the final observation cutoff index instead of reusing the geometric threshold N
4. Retain the finite-seed lemma's exact constants, the target-marker tag, and all-intermediate-time support bound in a formal write-up
5. Keep decidability, fixed-input stationary-frame semilinearity, failure of timed semilinearity, and any literature-priority question separate

## Additional binary result

The subsequently supplied binary four-particle shuttle has also passed independent review. Unlike the weighted example in Section 6, it uses the ordinary binary alphabet, with pair geometry carrying direction. Its exact anchored 10011 hit times from {0,3,4,d} are k²+(2d−11)k. Full proof checks, the exact conservation-certificate verification, and a noninjectivity example are in `BINARY-INDEPENDENT-AUDIT.md`. The separate executable receipt is `binary-independent-audit-results.json`.
