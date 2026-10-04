# Adversarial audit: uniform four-mass timed charts

Date: 4 October 2026 UTC

## Verdict

**PASS for the precise residue-cell theorem and its canonical-quotient lift, conditional on the pinned source-17 dynamics and source-18 fixed-input chart theorem.** No counterexample or substantive proof gap was found. The imports actually supply the uniform large-gap mechanism used by the new deduction; the argument does not merely promote a separate fixed-input result to a uniform one.

The accepted conclusions are:

1. For each fixed rule and input-label tuple of mass at most four, one finite effective chart family works for all ordered initial positions.
2. On finitely many disjoint Presburger input cells, each chart uses at most **two free natural evolution parameters**, has an affine stationary-frame spatial map, and has a time map of total degree at most two jointly in the inputs and evolution parameters.
3. Literal affine domains are obtained with at most three additional, uniquely input-determined initial-gap quotients. This is at most five natural parameters, not a two-total-variable theorem.
4. Uniform untimed stationary-frame configuration reachability is Presburger.
5. The copied-input compiler gives a fixed-rule/input-and-output-label-case quartic with empty or singleton natural witness fibers for complete timed configurations. Its witnesses include the copies, quotients, selectors, and slacks; the two-evolution-parameter bound is not a quartic witness bound.

This audit is a mathematical review with independent finite arithmetic tests. It is not a formal verification, a rule-to-chart implementation, a publication-priority determination, or an approval to write an article.

## Frozen material and independence

The target was read without modification:

- Packet: `/workspace/shared/uniform-four-particle-charts-20261004`
- `MANIFEST.json`: SHA-256 `0fb634cca9f665b44c3601509a6cef49391599064a9715164227fc475260be4c`
- `PROOF-NOTE.md`: SHA-256 `2e6484f4a2dbc0419e9662bf1ca02d4154469a1f4dcf93f4320f9951c9124962`
- `pinned/inherited-article-source.tex`: SHA-256 `17d3c0d9b449c689f88c1dc082ffee9b116993e4f5585b65d52c4fe591b2d962`

Every file listed by the frozen manifest was verified against its recorded byte length and SHA-256. The prior `REVIEW.md` and arithmetic program were read as material under audit; neither its PASS nor its test results were used as an independent test oracle. No upstream program and no saved schedule was executed. The new `check_adversarial.py` was written for this audit and executed locally.

The mathematical source inspection included source 16's stationary-frame/no-split/core arguments, source 17's actual seed-library and section proofs, and source 18's half-open chart construction and compiler. Source line numbers below refer to the pinned article; note line numbers refer to the frozen proof note.

## 1. The imported mechanism is uniform enough

### 1.1 A finite library independent of arbitrary input gaps

Source 16, around lines 5470–5550, proves the relevant no-split fact. A mass-two packet initially of diameter at most `2S` remains within that diameter in the stationary-unit frame. For two units at distance `d>S`, the original sites each see their isolated-unit neighborhood and retain both conserved units. For `d<=S`, a new occupied site must see both units and hence lies in `[d-S,S]`. This is stronger than a generic finite-propagation estimate and prevents the packet from leaving a separately moving fragment behind.

Consequently the normalized mass-two shapes form a finite deterministic system with fixed finite-phase profiles. Source 16's mass-three core is finite modulo translation. Fixed core exits have either computable first returns or independent terminal profiles, and a repeated core shape repeats the entire subsequent orbit up to translation, including intermediate configurations. Thus the finitely many connected mass-three entry seeds have computable complete profiles.

Source 17, lines 6083–6121, builds its library from these original connected seeds, each of diameter at most `4S`. It chooses one fixed prefix and compact/emission outcome for each seed, and then chooses a single `B>=4S` bounding all those prefixes and initial-period representatives. The seed set is fixed by the rule and radius. It does not grow with the later arbitrary input gap or depend circularly on the large ordinary-state threshold.

The fixed thresholds are

    N = 4B + 12S,     W = N + 2B.

The safe-prefix lemma therefore applies uniformly, not separately with an input-dependent safety radius.

### 1.2 Every current live gap `D>N` suffices

The potentially dangerous phrase “sufficiently large” occurs at source lines 6166–6168. Reading the subsequent proof resolves it: the displayed `N` is already sufficient for every subsequent live transition. There is no unmentioned increasing threshold.

At target contact, the connected seed's left edge `a'` obeys `|a'-b|<=4S`, where `b` was the target marker. Thus the other marker `p` has

    |p-a'| >= D-4S > N-4S > B+2S.

The entire fixed scattering prefix is therefore independent of that marker. The new residual marker moves from `b` by at most `4S+B`; because `D>N>B+4S`, marker order cannot reverse. These are explicit source lines 6179–6195. They give fixed additive changes in gap and anchor.

For the flight, source lines 6204–6223 use packet period `p`, nonzero drift `d`, phase offset `h_r`, and phase width `d_r<=2S`. After reflection, `d>0`, and target contact in phase `r` is exactly

    D-2S-d_r <= h_r+k*d <= D+2S.

The emitted launch offsets and their phase representatives have magnitude at most `2B`. Since `D>N`, even the lower numerator is strictly positive: `D-2S-d_r-h_r > N-4S-2B = 2B+8S`. The periodic candidate count is therefore natural; no unbounded transient or new input-dependent lower cutoff has been hidden.

On a fixed residue of `D mod d`, every candidate count is `D/d` plus a fixed rational offset. Candidate times all have the same leading coefficient `p/d`. Their validity and earliest-phase ordering consequently depend only on that residue, not on a further comparison between arbitrarily large gaps. Finite propagation ensures that some phase contacts the target. This establishes precisely the residue-only control update and affine duration used in note lines 90–96.

The source preserves each flight phase and each scattering-prefix state. Its uniform section mechanism is stronger data than the eventual normal-form proposition alone. If only the latter proposition had been imported, the new uniformity claim would not follow; the actual pinned packet imports and uses the stronger data.

### 1.3 There are no omitted large-gap branches

Source lines 6197–6202 distinguish:

- an outward emission, which is permanently independent
- an inward emission with new gap above `N`, which continues live
- an inward emission with new gap at most `N`, whose complete launch span is at most `N+2B=W`
- a compact mass-three outcome, followed independently until escape or bounded full contact

A moving compact mass-three packet is not a fixed-duration local reaction. Its first contact with the fourth unit has complete span at most `2B+2S<W`. This is the key reason a second arbitrary gap does not survive a compact reset.

The geometric ordinary and live sets can overlap. The deterministic live-tag convention at designated emission checkpoints, source lines 6159–6164, is essential. “First ordinary reset” in the new proof means the first ordinary dispatch/reset under this convention, not the first intermediate instant at which the untagged geometric span happens to be at most `W`. With that interpretation, the note is consistent with the source and does not truncate a live edge incorrectly.

## 2. Initial dispatch is genuinely uniform

The component mass partitions `4`, `3+1`, `2+2`, `2+1+1`, and `1+1+1+1` are exhaustive. Every component's normalized initial shape comes from a fixed finite set. All bounded internal gaps can be enumerated by affine equalities.

For `2+2`, an initial gap is retained only until the first packet contact. First contact has complete span at most `6S`, hence enters the fixed ordinary core. For `2+1+1`, the first packet contact is with either or both units. A simultaneous contact is a connected four-mass configuration of span at most `6S`; a single contact gives a connected three-mass seed plus the remaining unit. The note's tie-breaking chooses an arithmetic witness, not a single physical collision, and does not delete simultaneous contacts.

For `3+1`, an outside-`W` configuration is safely distant because the connected seed's diameter is at most `4S` and

    |b-a| > W-4S > B+2S.

Its fixed seed prefix is followed by an emission or a compact profile. The compact profile's possibly arbitrarily long flight is handled by first-contact arithmetic and ends in a bounded ordinary state. Each initial dispatch path therefore has a bounded number of symbolic stages: at most one packet contact, one seed prefix, and one compact flight. This bound is independent of all initial gaps.

### First-contact arithmetic and ownership

For each synchronized periodic phase and monitored occupied-site pair, contact is an interval `-2S<=A(x)+d*k<=2S` with fixed drift `d`. If `d=0`, the phase either never contacts or first contacts at `k=0`. Otherwise the earliest natural candidate is a clamped ceiling of an affine form divided by a fixed integer. Fixed congruence refinement makes this ceiling affine. Candidate eligibility, clamping, and selection of the earliest candidate use finite affine comparisons. Fixed transients are finitely many additional cases.

The use of occupied-site pairs is safe for compact shapes with holes. A hull test is not an exact test at an arbitrary phase for an arbitrary compact shape, even though it is exact for a mass-two packet of width at most `2S`.

Before the first proximity, distinct objects evolve independently; the preceding independent step also gives the true configuration at the first-contact time with disjoint occupied sites. Half-open precontact charts omit that time, and the next segment owns it. Variable entry times and anchors introduce only affine substitutions into these first-contact formulas.

All first-contact divisions are by fixed rule-dependent integers. An integer-valued rational-affine expression arising after an earlier split is dealt with on its integrality cell, using the congruence pullback audited below. There is no variable division.

## 3. Cycle acceleration and every endpoint

Enlarging control by a fixed modulus makes the unguarded continuation map finite and deterministic. A repeated control fixes one cycle word. Its additive changes, phase data, and durations are fixed constants. Since the control includes the residue, its net gap change is a multiple of the control modulus and the residue itinerary repeats.

Write `c_0=0`, `c_m=Delta`, and let `c_s` be all intermediate additive gap offsets. Put `b=min(c_0,...,c_m)`. A complete cycle starting at gap `d+n*Delta` is live-to-live exactly when

    d+n*Delta+b > N.

This includes the final endpoint as well as each interior endpoint. The frozen formula retains all of them.

If `Delta=-a<0`, the number of completed cycles is exactly

    K = max(0, ceil((d+b-N)/a)).

This follows by counting natural integers `n` satisfying the strict inequality `a*n<d+b-N`. It correctly handles `K=0` and exact divisibility. When `K>0`, the final-endpoint guard of cycle `K-1` proves that cycle `K` still starts live; when `K=0`, that is the entry assumption. Therefore the first failed endpoint is in `1,...,m`. The edge arriving there really is traversed and its terminal launch belongs only to the reset template.

The final gap is bounded above by `N`, and bounded below by `N+c+1` for the fixed decrement `c` of the failing edge. More strongly, the source's marker-order argument keeps it positive. The complete endpoint launch has bounded span, and its normalized shape is selected from a fixed finite set. Its anchor is affine after substituting the affine residue-cell formula for `K`.

For `Delta>=0`, a valid first cycle stays valid forever. A failed first cycle is handled by its first failed endpoint. A zero-net cycle must retain the variable input gap in its clock: its physical period can be `A*d+B`. The note correctly uses two-parameter cycle/flight charts instead of treating this as a uniform fixed-period tail.

### Concrete failures of weakened variants

These are counterexamples to tempting shortcuts, not to the frozen formula:

- With `N=10`, starting gap `12`, and word `(-3)`, checking only the starting endpoint falsely accepts one whole live-to-live cycle; its final gap is `9`
- With `N=10`, starting gap `13`, and word `(-5,+6)`, both the start and final endpoint are live and the net drift is positive, but the interior gap is `8`; checking only start/final endpoints falsely gives an infinite valid cycle
- With a strict guard, replacing the ceiling count by `floor(v/a)+1` fails when `v` is a positive multiple of `a`

## 4. Degree, intermediate times, and reset composition

Summing the affine edge durations gives the exact edge-start clock

    S_s(n) = T_* + n(A*d+B) + A*Delta*n(n-1)/2
             + A_s(d+n*Delta) + B_s.

Before the first reset, `T_*`, `d`, and the anchor are affine in the external inputs on each cell. Thus `n*d` and `n(n-1)` are the only new quadratic forms; no input-dependent coefficient multiplies `n^2`.

For each packet phase, `r+p*j<h_s(d+n*Delta)` is affine in the inputs, cycle number, and flight quotient. Fixed local-prefix phases require no flight quotient. Each complete contracting cycle has the affine guard `n<K(x)`. The last partial cycle substitutes `n=K(x)`, leaving at most the flight quotient free. Its output time remains quadratic because substitution of an affine expression into a quadratic polynomial preserves degree two.

The proof does not use the nonlinear inequality `t<Q(x)` as a chart-domain condition. It enforces chronological ownership through the affine cycle/phase guards and then outputs the quadratic time. That distinction is necessary for the asserted affine domains.

At the first ordinary reset, only the translated anchor and quadratic elapsed time remain input-dependent. Every other piece of complete geometry belongs to a finite normalized shape `o`. Precompute the source-18 complete fixed-input family for each such `o` once, using the stationary-frame rule. Then the entire suffix is

    time = Q(x) + t_o(z),
    stationary positions = a(x) + v_o(z).

This is additive composition, not substitution of `Q` into a second quadratic clock. The possibly enormous finite history inside a template depends on the fixed rule and one of finitely many bounded shapes, not on an initial arbitrary gap. No cycle-count witness from the first excursion survives into these suffix charts.

The half-open first-contact segments, half-open live edges, first failed endpoint, Euclidean phase quotient, and first-reset ownership together account for every time exactly once for each fixed input. Source 18 supplies the same ownership inside the fixed suffix templates. Distinct occupied sites have affine stationary-frame differences, so strict sorting is a finite affine refinement. Repeated labels do not create extra permutations because the occupied coordinates are distinct.

The bijection is fiberwise in the initial configuration. It is not a global injectivity claim after forgetting the initial configuration, which would fail for noninjective rules.

## 5. Small masses and absence of a unit symbol

For mass at most three with a unit symbol, source 16's bounded core and fixed templates give the same first-entry construction with affine clocks and positions. Its explicit proof does not require a four-mass shuttle cycle.

If no unit symbol exists, every occupied site has weight at least two. At mass at most four there are at most two sites, and a two-site state must have weights `2+2`. An isolated weight-two site cannot split and is a finite-state walker. Isolated weight-three sites also cannot split. Weight-four states may split, which is why merely calling every occupied site a walker would be wrong.

The note correctly includes all singletons and all states of diameter at most `2S` in a finite normalized core. A weight-four split is retained there or in a fixed outgoing excursion. Outside the core there are exactly two independent weight-two walkers. Their uniform first proximity is affine after phase/residue refinement. From a fixed core shape, the first return or escape is fixed computable data. A repeated core shape gives a translated-periodic whole-orbit template; an escape gives an independent terminal template. This establishes the no-unit case without smuggling in stationary unit markers.

Vacuum and radius-zero cases are harmless: the vacuum has a one-clock empty-support chart, and padding `S>=1` includes radius zero. For readability, a future manuscript should explicitly set `S=max(1,R+|delta|)` in its opening unit-symbol clause; the frozen note currently obtains that definition through its source-17 import. This is an expository clarification, not a missing hypothesis.

## 6. Arithmetic domains and the quartic

### Congruences and the parameter ledger

All input congruence tests ultimately involve relative coordinates. Every integral affine combination invariant under a common translation can be rewritten in the initial gaps. If `(a dot g+c)/d` is integer-valued on the current cell, its residue `rho mod M` is equivalent there to

    a dot g+c = d*rho (mod d*M).

The multiplier must be `d*M`, not just `lcm(d,M)`. For example, deciding whether `D/2` is even requires `D mod 4`; `D mod 2` does not suffice. The frozen note explicitly makes the correct pullback before choosing its common modulus `H`.

There are only finitely many symbolic branches, finite-control cycles, fixed divisors, and bounded reset shapes. The final common `H` is therefore a fixed finite integer. On each gap-residue vector, the equations `g_i=H*u_i+r_i` give unique natural quotients for ordered inputs. They add at most `m-1` parameters and no duplicate witnesses. They convert all remaining domains to literal integer-affine constraints after positive denominator clearing.

Dropping the time output then leaves only affine maps, affine domains, and fixed congruences, so existential projection is Presburger. This argument does not show that the timed relation, original-frame untimed relation, or least-time function is Presburger. Forgetting time can also destroy the original chart's single-fold witness property; the asserted timed quartic retains time externally.

### Selector-safe external input copies

A naive uniform use of source 18's constant-term lift is indeed invalid: a term quadratic in an external input would become cubic when multiplied by a selector and sextic when squared. The frozen note contains the necessary repair.

For each chart, natural private copies obey `X_hi^+-e_h*x_i^+=0` and `X_hi^--e_h*x_i^-=0`. These residuals are quadratic in all variables. Replacing every occurrence of the original input in the chart by `X_hi^+-X_hi^-` leaves affine domain forms and quadratic output forms in private variables only. Constant-term lifting now multiplies only genuine numerical constants by the selector.

Include copies and canonical quotients in the inactive-zero sum together with evolution variables and slacks. At a natural zero, the selector sum is one. An inactive chart's gate forces every one of its natural private variables to zero. The active chart's copies equal the fixed external canonical input, its input quotients are uniquely determined, and its inequality slacks are uniquely determined after integer denominator clearing. The source-18 fiber proof therefore applies with no additional multiplicity.

Every residual has degree at most two, including the copying equations, inactive-zero gates, and optional canonical signed-pair products. The sum of squares has degree at most four. The note's bound of `2m+(m-1)+2=3m+1<=13` private variables per nonempty-input chart before selectors and inequality slacks is conservative and correct. Vacuum is treated separately. The full witness count depends on the finite chart family and is not bounded by two or five.

The natural domain is essential. Inactive-zero sums could cancel for signed private variables, and arbitrary difference-pair representations would destroy uniqueness. The note uses unique natural input pairs and natural private variables, so that failure is avoided. No real- or rational-witness exactness is established.

## 7. Fresh adversarial checks

`check_adversarial.py` is a self-contained checker of arithmetic fixtures written for this audit. It uses Python's standard library and installed SymPy. The section oracle advances one edge and one elapsed time at a time; the separate chart construction uses the closed cycle clock and accelerated reset count.

The recorded run passed:

- 7,020 abstract section systems/input cases, including positive, zero, and negative net cycle drifts
- 7,353,761 individual timed phase descriptions compared, with no missing or duplicate timestamp
- 3,242 bounded-reset cases, including additive composition with a fixed prefix/periodic reset template
- 2,196 synchronized first-contact cases with signed and zero drifts, multiple phases, and multiple monitored site pairs
- 703,125 natural witness tuples in finite boxes for a two-chart copied-input quartic with parity cells, canonical quotients, genuinely quadratic external-input dependence, inactive gates, and empty/singleton output fibers
- symbolic verification that the copied-input polynomial has total degree four and the naive selector-times-external-square variant has degree six
- 10,374 denominator-inside-congruence comparisons
- explicit rejection of incomplete endpoint guards, a generic compact-shape hull shortcut, and an insufficient congruence modulus

The checker covers these fixtures only. Its abstract sections are not claims of realizability by particular CAs, and the finite witness boxes do not themselves prove the full natural-fiber theorem. The mathematical arguments above carry the all-input claims.

## Recommendation

The frozen result is suitable to advance as the stated conditional uniform extension. Preserve its input-residue/quotient distinction, the deterministic live-tag convention, natural-witness restriction, and explicit dependence on the source-17 section mechanism and source-18 templates. Do not strengthen it to two total raw-affine auxiliaries, a generic real-witness certificate, an implemented compiler, or a novelty claim without additional work.

No frozen file was edited. No article was written or changed.
