# Independent audit: reversible binary four-particle quadratic clock

4 October 2026. **PASS within the mathematical scope below.** No defect was found in the full-shift reversibility proof, the literal six-row rule, the complete four-particle orbit, or its exact anchored hit-time formula. The proof applies to arbitrary malformed and infinite binary configurations, not only the intended particle encoding. The inherited mass-at-most-three theorem does cover exact anchored words including zeros, so four is the sharp particle threshold for this particular failure of eventual periodicity in one-dimensional binary number-conserving CAs, including their globally reversible subclass.

This does **not** establish a new universality threshold, Diophantine arity or degree record, or literature priority. The independent checker and periodic implementation were written for this audit from the six literal rows. No author/upstream executable or schedule was imported or run. Author files were read only.

## 1. Frozen object and literal rule

The audited `candidate-specification.md` has SHA-256
`505f6d8b6be6e226bd8128785913d2e8b30e0da0e328f44cf99d7b06872053ab`.

A raw key is **(row, anchor)**, with endpoint side deliberately omitted. Its predicate is equality of the occupied set in the translated inclusive read interval to one of the two endpoints:

| Block | Row | Endpoint 0 | Endpoint 1 | Read interval |
|---|---|---|---|---|
| A | AR | {0,1} | {0,2} | [-4,6] |
| A | AL | {0,4} | {0,3} | [-4,8] |
| A | AC | {0,1,6} | {-1,2,7} | [-5,8] |
| B | BR | {0,2} | {1,2} | [-4,6] |
| B | BL | {0,3} | {-1,3} | [-5,7] |
| B | BC | {-5,0,3} | {-5,0,1} | [-5,8] |

For each block, a raw key at x is selected iff there is no other raw key at anchor distance at most 30, and hypothetically swapping this endpoint preserves every raw key at anchor distance at most 15. All selected swaps act simultaneously. F applies A first and B second.

All endpoints are contained in their own read interval, all write supports lie in [-7,7], all read intervals lie in [-8,8], and each endpoint pair has equal weight. The six own-key predicates are symmetric under their swaps. Thus b=7, r=8 and H=30 satisfy the generic hypotheses.

## 2. Independent full-shift proof

Write K(c) for the entire raw-key set of an arbitrary bi-infinite configuration c. For a present key k at x, let S_k c be its hypothetical swap, and let P_k(c) assert equality of raw-key sets within distance b+r from x.

### Raw-key preservation is genuinely global

A write at x can change a raw predicate at y only if its radius-b write window meets the radius-r read window at y. Hence |x-y|<=b+r. Outside this anchor interval the raw predicate is identical. Consequently P_k(c) is equivalent to the global equality K(S_k c)=K(c), although deciding it uses only finite data.

Selected keys have pairwise anchor distances greater than H=2(b+r), including keys with different row types at a common anchor. Their write windows are disjoint. A raw read window cannot meet two selected write windows: otherwise the triangle inequality would give distance at most 2(b+r) between their anchors.

Let T denote the simultaneous block. Every raw predicate therefore sees either no change or precisely the change made by one hypothetical selected swap. In the latter case P_k ensures that the predicate's truth value is unchanged. This proves K(Tc)=K(c) for every configuration, with no finiteness or legal-encoding assumption.

### Selection invariance includes every rejected key

Isolation depends only on K, so it is preserved. For a raw key at x, evaluating P_k uses input only within radius b+2r: test anchors range within b+r, and each read has radius r.

Every other selected key at y is more than H from x, since its own isolation test sees the raw key at x. Its radius-b write window therefore misses [x-(b+2r),x+(b+2r)]. This assertion applies even when x itself is rejected.

- If k is selected, its own swap exchanges the two configurations whose raw sets P_k compares. Other selected swaps cannot affect that comparison. P_k remains true.
- If k is isolated but prospectively rejected, no own swap occurs and all other selected writes miss the comparison window. It stays rejected.
- If k is nonisolated, its isolation remains false because K is unchanged. It remains rejected regardless of prospectivity. In fact the same separation argument preserves its prospective status too.

No new raw key can appear because K is unchanged. Therefore the selected set is identical on c and Tc. A second application uses the same disjoint endpoint involutions and returns c. This is a full-shift involution, rather than injectivity only on finite supports.

### Locality, conservation, and inverse

To determine the output at a site z, only candidate anchors within b of z need be considered. Isolation at such an anchor reads out to H+r, and prospectivity reads out to b+2r. Thus the block radius is at most

b + max(H+r, b+2r) = 3(b+r) = 45.

The output is translation-equivariant because every definition uses relative positions. Each selected swap preserves the number of occupied sites and the write windows are disjoint. On finite support, only finitely many positive-weight endpoints are present, so summing these equal-weight changes proves finite number conservation. Vacuum has no raw key and is fixed.

Accordingly A and B are globally reversible, quiescent, binary number-conserving CAs. Their composition F has radius at most 90, and F^{-1}=A composed with B also has radius at most 90. These are upper bounds, not claimed minimal radii. The finite-number-conserving convention is the standard one used in Morita's RNCCA definition.

### Why the prospective condition must not be removed

A compact independent witness is X={-8,-5,0,1}. Its sole A raw key is (AR,0). The hypothetical swap gives Y={-8,-5,0,2}, which has both (AR,0) and (AC,-7). The actual rule rejects the swap. An isolation-only variant instead sends X to Y and fixes Y, hence is noninjective.

Adding the distant pair {70,71} to X gives a simultaneous test of a rejected and an accepted isolated key: (AR,0) remains rejected, (AR,70) is selected, and only the distant pair changes to {70,72}. Both statuses are preserved exactly. The audit checks this example directly.

## 3. Complete orbit, with both collision boundaries

For D>=13, put C_D={0,5,6,D} and L_D=2D-22. The exact state at every integer 0<=s<L_D is

- R phase, 0<=s<=D-11: {0,5+s,6+s,D}
- L phase, D-10<=s<=2D-23: {0,2D-18-s,2D-14-s,D+1}

At s=L_D the state is C_(D+1).

These phase intervals are adjacent, disjoint, and cover all times in a cycle. At D=13 the L phase consists of the single state s=3, so the minimum-parameter boundary is covered.

The exact half-step transformations are:

1. Right flight, 5<=p<=D-7:
   {0,p,p+1,D} --AR(p)--> {0,p,p+2,D} --BR(p)--> {0,p+1,p+2,D}
2. Right contact, p=D-6:
   {0,D-6,D-5,D} --AC(D-6)--> {0,D-7,D-4,D+1}
   --BL(D-7)--> {0,D-8,D-4,D+1}
3. Left flight, 6<=q<=D-8:
   {0,q,q+4,D+1} --AL(q)--> {0,q,q+3,D+1}
   --BL(q)--> {0,q-1,q+3,D+1}
4. Left contact, q=5:
   {0,5,9,D+1} --AL(5)--> {0,5,8,D+1}
   --BC(5)--> {0,5,6,D+1}

An empty left-flight range when D=13 causes no problem.

### Why these intended moves are the actual guarded moves

At every listed state and half-state there is exactly one pair at distance at most four; every other pair has distance at least five. Each literal endpoint contains a close pair, so every possible raw key must use this unique pair.

For A, gap 1 or 2 belongs to AR; the only competing endpoint at gap 1 is AC's input. It requires the third particle six sites right of the pair's left site, exactly the point included by AR's right guard. At right contact this produces AC and blocks AR; during right flight the right marker is farther away. Gap 3 or 4 belongs to AL; the only competing gap-3 endpoint is AC's output. Its right marker is eight sites right of the pair's left site, exactly the point included in AL's guard. This excludes AL on the reverse side of AC, and no such marker occurs in the free left-flight half-states.

For B, gap 1 or 2 belongs to BR, with the only competing gap-1 endpoint BC's output. Gap 3 or 4 belongs to BL, with the only competing gap-3 endpoint BC's input. Both BC endpoints require the extra particle five sites left of the close pair's left site. This marker is included by the relevant BR/BL guard, so BC and the free move never coexist. It occurs exactly at the left contact or its reversed half-step, and not during free flights. At the right collision the left pair site is D-7>=6, so the origin cannot accidentally trigger BC.

For contact AC, the unused origin lies outside [D-11,D+2], because D>=13. For contact BC, the unused right marker D+1>=14 lies outside [0,13]. The corresponding free moves' guards also exclude the two spectator markers by the displayed bounds.

Thus each half-step has exactly one raw key before and after its hypothetical swap, and it is the same row-anchor key. Its isolation and prospective tests both pass. Induction proves the complete formula for every D>=13, not only the tested D.

## 4. Exact anchored hits and arithmetic corollary

The observation is the exact word 1000011 on [0,6], including zeros at 1,2,3,4. During an R phase, the adjacent moving pair is at {5,6} iff s=0. During an L phase its gap is four; the other occupied sites are 0 and D+1>=14, so the word cannot occur. There are no other hits.

Starting at C_d, the k-th hit is C_(d+k), at

 t_k = sum_(j=0)^(k-1) [2(d+j)-22] = k²+(2d-23)k, k>=0.

The successive gaps are 2k+2d-22 and are unbounded. An infinite eventually periodic subset of N has bounded successive gaps: after its periodicity threshold at least one residue class recurs every period. Hence the exact hit set is not eventually periodic or Presburger-definable.

Set d=13+x with x,t in N. The single-residual quartic

 Q(x,t;k) = [k²+(2x+3)k-t]²

has one natural witness k. Its fiber is empty unless t is a hit, and is a singleton at every hit, since consecutive values of the unsquared timing polynomial differ by 2k+2x+4>0.

The same statement holds for k in the nonnegative rationals: a rational root of the monic integer polynomial k²+(2x+3)k-t is an integer (the rational-root theorem). Restricting to nonnegative rationals therefore recovers exactly the natural roots. This does not extend to unrestricted rational/integer uniqueness, because the second root at a genuine hit is -k-(2x+3). Nor does it extend to nonnegative real exactness: x=0,t=1 has the false real witness (sqrt(13)-3)/2.

This is an elementary certificate for the displayed timing relation, already of the same form as the nonreversible shuttle's arithmetic corollary. It is not a new general arity, degree, single-fold universality, or universal-polynomial record.

## 5. Sharpness of the four-particle timing threshold

I retrieved the actual inherited source theorem and read its full relevant proof, rather than relying only on an implementation audit. The inspected `article.tex` blob is `ec10c7a579e04d3d27a92035d9a180dfcb695ff2` in the signal-machine-collision-certificates report.

- Lines 5406–5419 specify fixed deterministic, time-independent, translation-equivariant, one-dimensional finite-radius CAs, positive integer nonvacuum weights, a unique weight-zero vacuum, at most one weight-one label, and conservation on every finite support. They explicitly impose **no reversibility restriction**.
- Lines 5426–5459 state effective uniform timed Presburger evolution at total mass at most three, and eventual periodicity of fixed-input, fixed-observation hit times.
- Lines 5464–5731 supply the stationary-unit frame, mass-two no-split lemma, finite encounter core, complete intermediate-time orbit decomposition, and uniform Presburger construction. I checked that the eventual translations act on all intermediate times, not only section returns.
- Lines 5737–5743 explicitly translate an exact finite pattern into conditions on all occupied output sites. Required zeros mean that no output particle occupies those sites. Absolute anchoring is allowed; it is not a claim merely up to spatial translation.

An ordinary binary CA with weights 0 and 1 satisfies the alphabet and unit-label assumptions. Global reversibility only narrows the class, so the theorem applies to all globally reversible binary NCCAs with finite initial particle count at most three. The present four-particle construction supplies the upper witness. Therefore:

**Within one-dimensional binary finite-radius, time-independent, number-conserving CAs on Z with finite-support initial states, four is the least particle count permitting a non-eventually-periodic fixed-input exact anchored finite-pattern occurrence set. The same least count is four after requiring global reversibility.**

This is a timing threshold. It is not a claim that four particles permit universal computation; the inherited four-mass decidability result remains compatible with the clock. It says nothing about several internally typed weight-one labels, signed weights, nonautonomous rules, or other dimensions. Sharpness here is a deduction using the identified inherited theorem, not a literature-priority claim.

Source: [actual theorem and model](https://github.com/VladimirReshetnikov/ProveIt/blob/main/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/article.tex#L5406-L5459), [exact pattern treatment](https://github.com/VladimirReshetnikov/ProveIt/blob/main/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/article.tex#L5735-L5747). The relevant retrieved excerpt is preserved locally for audit reproducibility.

## 6. Independent executable evidence

### Sparse finite-support implementation

`independent_checker.py` finds all raw keys by aligning occupied sites with every endpoint offset, then performs the exact read-window test. It never uses the intended orbit's phase formulas to implement the CA. It rediscovers the **complete** raw-key set after each hypothetical swap, including births. It verifies all raw, isolated, prospective, and selected statuses, mass, and inverses.

Passed evidence in `independent-results.json`:

- All 540 potentially changing source-side/target-row/relative-anchor interactions, covering 49,840 complete local assignments; at most 12 free bits in any table
- 48 assignments genuinely change another raw predicate under a hypothetical swap, exercising prospective rejection rather than making that test vacuous
- Every step of 108 cycles D=13 through 120: 11,988 complete steps, with unique selected raw keys at every half-step
- 36 large-coordinate phase/boundary transitions, through D=10^100
- A continuous 3,780-step orbit with exactly the 61 hits k²+3k for k=0..60
- 4,736 arbitrary/malformed finite configurations, including random dense/sparse supports and 2,736 endpoint-island arrangements around guard boundaries
- 9,472 checked blocks, of which 4,179 move, 2,962 have multiple selected keys, and 21 contain an isolated prospectively rejected key
- Both composition inverse identities and translation covariance on those finite configurations

`critical-overlap-truth-tables.json` records every table. Each fixes one source endpoint on its exact read interval and exhausts every unconstrained bit of the target read interval. Bits outside their union cannot affect this interaction. This is exhaustive for pairwise raw-predicate interactions, **not** an enumeration of every radius-45 global neighborhood. The full-shift result is established by Section 2's proof.

### Separate 64-periodic bit implementation

`exhaustive_periodic.cpp` independently implements all read predicates by rotated bit masks, with no sparse-alignment code. It passed every one of the 262,144 binary words of width 18 padded with zeros into a 64-periodic configuration, plus 252 two-island configurations. There were 524,792 verified block applications, 53,764 changed blocks, 80 isolated-rejection blocks, and 216 blocks with multiple selected keys. Both left and right inverse identities passed.

These are exact induced tests on infinite periodic configurations. Period 64 exceeds 2H=60, so the isolation neighborhood has no duplicate lifts, and exceeds 2(b+r)=30, so the affected raw-key neighborhoods of periodic copies do not overlap. The ring computation of prospective equality therefore matches the specified single-anchor local test. Only the stated subset of 64-periodic configurations was enumerated; this is not an exhaustive test of all 2^64 periodic words.

### Compact edge cases and quartic checks

`check_corollaries.py` verifies the compact candidate-birth example, simultaneous distant selected/rejected keys, 42 large-integer quartic cases, and 1,516,800 rational trials. The general rational claim rests on the monic theorem, not the finite trials.

Replay, from this directory:

```sh
python independent_checker.py
g++ -std=c++17 -O2 -Wall -Wextra -pedantic exhaustive_periodic.cpp -o exhaustive_periodic
./exhaustive_periodic > periodic-results.json
python check_corollaries.py
```

The Python checks use explicit failure tests and remain active under optimization. The C++ code uses explicit checks, not disabled assertions. Runtime versions used were Python 3.12.14 and Debian g++ 14.2.0. A fresh full C++ replay under UndefinedBehaviorSanitizer also passed, and its JSON receipt was byte-identical to the optimized run.

## 7. Source and novelty boundaries

The generic prospective-isolation mechanism was already present in the repository's [parallel-particle review](https://github.com/VladimirReshetnikov/ProveIt/blob/main/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_parallel_particle_reports.md), fetched blob `30c7366beb6afa71ee2f72e87776c9781c77e1e2`. The new issue audited here is the six-row four-particle realization and its exact orbit.

The repository's [older binary four-particle shuttle audit](https://github.com/VladimirReshetnikov/ProveIt/blob/main/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/17-four-mass-BINARY-INDEPENDENT-AUDIT.md), fetched blob `0aa7b9707374304f496dce793a1501c15d3c2f85`, explicitly proves that its different radius-six rule is noninjective. It therefore does not itself settle the globally reversible four-particle example.

[Morita's 2012 primary paper](https://arxiv.org/html/1208.2760) establishes a 96-state four-neighbor RNCCA universality result, not the present binary fixed-four-particle clock. The repository's current combined article also identifies already existing binary and globally reversible binary five-particle universality constructions in the five-particle-binary-automata reports (article lines 5897 onward). Nothing in this audit upgrades the four-particle clock into universality or claims precedence over those works.

The source theorem, generic full-shift lemma, and six-row construction are mathematical proofs inspected here, not mechanically formalized theorems. The finite tests corroborate the literal implementation and boundary arithmetic; they are not substitutes for the unrestricted proofs.
