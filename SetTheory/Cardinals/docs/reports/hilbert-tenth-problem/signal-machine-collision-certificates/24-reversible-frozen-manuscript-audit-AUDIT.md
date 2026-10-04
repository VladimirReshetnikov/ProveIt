# Report 49 independent manuscript audit

4 October 2026. **PASS for the exact draft2 manuscript and PDF identified below.** No required scientific correction or rendered-layout correction remains. This is a mathematical and manuscript review, not a proof-assistant formalization, literature-priority certification, or final archive/replay-helper certification.

## Exact reviewed revision

- TeX: `/workspace/shared/reversible-clock-report49-release-20261004/manuscript/report49.tex`
- TeX SHA-256: `c78133175cca8be54cbf230af1423b77b0ee3bcf6d71bd816f6478800ccf9056`
- PDF: `/workspace/shared/report49-draft2-build-20261004/manuscript/report49.pdf`
- PDF SHA-256: `3e9aecc5f93634f0cf5a458e99c944afa1fc21d223505f3d252bdc4d6f2150fa`
- 14 US Letter pages, PDF 1.7
- Prior draft1 was read and rendered in full. The draft1-to-draft2 source diff was inspected; all 14 draft2 pages were then visually inspected.

The scientific source directories were read only. No candidate/upstream executable or saved schedule was imported or run. The only mathematical checker executed in this review was the new, fully inspected `manuscript_checker.py` written in this audit directory from the manuscript's six rows. Poppler was used for PDF extraction and rendering.

## 1. Literal rule and global proof

The six row endpoints and windows in Table 1 agree with the frozen independently audited candidate. Every endpoint lies in its read interval; endpoint cardinalities agree row by row. The actual offsets satisfy `b=7`, `r=8`.

The raw key is correctly `(row, anchor)` without endpoint side. This detail is necessary for the preservation test. The rule explicitly enumerates new as well as old keys after a hypothetical swap; it does not merely check that old candidates survive. There is no unstated legal-state filter.

The prospective-isolation proof is valid on arbitrary bi-infinite configurations:

1. A hypothetical write can affect a key only at anchor distance at most `b+r=15`, making the prospective comparison equivalent to equality of the full raw-key sets.
2. Selected anchors are separated by more than `H=30`. Their writes are disjoint, and a single raw read window cannot meet two selected writes.
3. Each raw predicate therefore receives either no change or exactly the change whose preservation was checked. This proves global raw-key-set invariance without a support restriction.
4. The prospective comparison at a key uses radius `b+2r=23`. Every other selected write misses it because its anchor is more than `H=2b+2r` away, even when the key under consideration is rejected.
5. Selected keys remain selected; isolated prospectively rejected keys remain rejected; nonisolated keys remain nonisolated. No new key appears. Applying the block again performs the same disjoint endpoint involutions.

This includes malformed finite configurations, infinite configurations, rejected-key preservation, and simultaneous accepted/rejected neighborhoods. The compact candidate-birth witness and the example with an additional pair at 70 are correct.

The output-site dependency bound is `b+max(H+r,b+2r)=45` per block, hence 90 for both composite and inverse. Finite number conservation follows from finitely many present keys and disjoint equal-weight swaps; the nonempty endpoints imply quiescence. Infinite-support reversibility does not rely on assigning an infinite particle count. The manuscript claims sufficient radii, not minimal ones.

## 2. Orbit and exact timing

Every displayed half-step is correct. The right flight, right contact, left flight, and left contact cases cover every complete step. The contact endpoint orientations, anchor shifts, and spectators' distances were checked independently.

The close-pair argument is sufficient to exclude alternative raw keys: every endpoint has a pair at distance at most four, and every listed state or half-state has exactly one such pair. The competing three-particle endpoints are precisely excluded by the free-move read windows. Before and after each proposed half-step there is one and the same row-anchor key, so both guards pass.

The phase intervals `0..D-11` and `D-10..2D-23` are consecutive, disjoint, and exhaustive for `L_D=2D-22`. The minimum case `D=13` correctly has no left flight and has one left-phase state. The endpoint is exactly `C_(D+1)`.

For exact word 1000011 at sites 0..6, the right phase matches only at its first state and the left phase never matches. Thus the theorem proves exclusivity at all times, not just the existence of returns. Summing cycle lengths gives

`t_k = k^2 + (2d-23)k`, `k>=0`,

with successive gaps `2k+2d-22`. The unbounded gaps prove failure of eventual periodicity because every infinite eventually periodic subset of the naturals has bounded gaps.

## 3. Quartic scope

For natural external parameters `x,t`, the polynomial `[k^2+(2x+3)k-t]^2` has total degree four and one witness coordinate. The timing polynomial is strictly increasing on natural `k`, so the natural zero fiber is empty or singleton exactly as claimed.

The nonnegative-rational assertion is proved, not extrapolated from testing: every rational root of the monic integer inner polynomial is integral. Nonnegativity then gives the same natural fiber. The second root at a genuine hit is negative and distinct, so the warning about unrestricted rational/integer fibers is correct. Every nonnegative real time parameter has a nonnegative real root; `x=0,t=1` is the given valid false-real-witness example. There is no real-exactness or universal-polynomial record claim.

## 4. Self-contained lower bound and sharpness

The binary fixed-input adaptation in Section 6 is logically sufficient and correctly credited to the stronger inherited weighted uniform theorem. It does not need that stronger theorem as an unproved black box.

- Number conservation and locality force a singleton displacement `delta` with `|delta|<=R`. The translated rule fixes singletons and has radius bounded by `S=max(1,R+|delta|)`.
- Components separated by more than `2S` evolve independently for one step with disjoint successor supports.
- A pair of diameter at most `2S` remains bounded by `2S`. For a gap greater than `S`, both original sites stay occupied and consume the full mass. For a gap at most `S`, any new occupied site sees both particles and lies in the stated interval. The radius-zero padding is harmless.
- The normalized pair state space is finite, giving a finite transient and a translated-periodic tail.
- Outside the diameter-`4S` three-particle core, the configuration consists either of three fixed singleton components or a bounded pair plus one fixed singleton. The first possible interaction is captured by first entry to the core. The union is disjoint through the first-entry time by the preceding one-step independence.
- The first-entry inequality `b-4S <= a+A_r+nD <= b+4S-d_r` is exact and effectively solved in each pair phase.
- First-return edges from normalized core shapes form a finite deterministic graph. A repeated normalized shape yields whole-configuration translated periodicity at all subsequent intermediate times, not merely at section times. A nonreturning branch has the completely described independent-object tail.
- On finitely many time phases, every occupied coordinate is affine in a natural parameter, in both stationary and original frames. Required ones and zeros are both tested. Equality to a fixed site is eventually constant on each phase, making every exact anchored word observation effectively eventually periodic.

The main theorem's formulation without a separate quiescence adjective is consistent: its finite-conservation definition applied to the vacuum implies quiescence. Four is consequently the sharp minimum for this precise non-eventually-periodic anchored timing phenomenon in one-dimensional autonomous binary number-conserving finite-input dynamics, including the full-shift reversible subclass. No extension to multiple unit labels, signed weights, active zero-weight backgrounds, time-dependent rules, infinite inputs, or other dimensions is inferred.

## 5. New dense observation corollary

Corollary 5.2 is correct. For word 100000 at sites 0..5, the origin is always occupied; sites 1..4 are always vacant; site 5 is occupied exactly at the first and last state of each cycle. The hit interval in cycle k is therefore exactly

`[t_k+1, t_(k+1)-2]`.

The complement has two distinct points per cycle and hence `O(sqrt(T))` points through time T, while remaining infinite. This proves density one and noncofiniteness.

The finite-sequence-union obstruction is scoped correctly. Positive-leading-coefficient quadratic sequences, including restrictions of their indices to eventual arithmetic progressions, have density zero. A finite union of eventual arithmetic progressions is eventually periodic; if adding a density-zero set makes its density one, its periodic part already has density one and is cofinite. The resulting union would be cofinite, a contradiction. Arbitrary subsets of quadratic indices are not being silently called unrestricted sequences.

This is an observation of the same orbit, not a new CA construction or an unsupported general band-classification theorem.

## 6. Prior results and further questions

The review used the supplied frontier memo and the inert combined inherited source. The newly added related-work paragraph correctly distinguishes source 17's fixed-input orbit alternatives from source 18's disjoint quadratic timed charts. The latter allow a within-flight parameter and growing time intervals; they are fully compatible with Corollary 5.2.

The revised further question concerns a description uniform in initial particle positions, with a precise syntax and parameter bounds. It no longer advertises the already established fixed-input four-particle classification as open. The source attribution, separate noninjective older shuttle, arithmetic-certificate precedent, and distinction from five-particle universality are appropriately explicit. The report makes no literature-priority claim; this audit does not independently certify external novelty.

## 7. Supplementary new computation

`manuscript_checker.py` was newly written from the literal manuscript table and imports only Python standard-library modules. It was read in full as authored before execution. It discovers possible anchors from nonempty endpoints, evaluates exact read windows, tests complete raw-key-set preservation under a hypothetical swap, and composes the selected endpoint toggles.

The receipt `manuscript-check-results.json` records PASS for:

- Every state and both half-steps in 41 full cycles, `D=13..53`: 1,804 complete steps
- Exact 1000011 and 100000 observation tests at every state in those cycles
- 21 boundary/flight steps at parameters through `10^100`
- 303 arbitrary or malformed finite supports, testing raw-key preservation, selected-key preservation, block involutions, particle number, and both composite inverse identities
- The compact rejected-key and simultaneous accepted/rejected examples

Checker SHA-256: `25c3923600a36d4d15623dc0b7f916d197d3775a665631e51610876292cfbc28`.

These are fresh supplementary finite checks of manuscript transcription and arithmetic. They do not replace the general proofs and are not represented as a rerun of the earlier exhaustive audit. The numerical counts in Section 8 of the manuscript were separately compared against the existing audit's stored JSON receipts; they match.

## 8. Render and packaging boundary

The draft2 PDF was rendered with Poppler at 95 dpi. Every page was opened and visually inspected. Equations, the literal row table, diagram, references, page numbers, and both manifest hashes are legible, with no clipping, overlap, missing glyph, or undefined reference found. The prior draft's stranded hash is resolved. The figure's displayed hits are 0,4,10,18,28,40,54 as required.

The audit does not certify the final archive manifest, the replay helper's implementation, its claimed scratch-only behavior, or the eventual final build output beyond the two hashes above. Those are separate release checks. Any post-review change to the manuscript requires a scoped diff review and a renewed PDF/hash binding.
