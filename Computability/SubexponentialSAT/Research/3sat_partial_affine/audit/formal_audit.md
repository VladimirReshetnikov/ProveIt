# External baseline audit and a crossing-algebra obstruction

Pinned Anthropic source: `anthropics/formal-math`, commit `1a6eee293b9e00cb432eef6018a21f523623a9af`.
PR 31 was merged as `16a5ce41304fcdaea4e0be7c132e1c361dc26da5` at 2026-10-27 03:07:22 UTC (October 26 Pacific).

## Verified source statements

- `eth/MainResults.lean` defines `MainTheorem` to assert the existence of ONE deterministic finite-alphabet Mathlib multi-stack Turing machine and ONE constant C, serving all k >= 1 and valid formulas with n >= 4, m >= 2, each variable occurring, no duplicate clause lists. It counts satisfying assignments in at most floor(2^(C min(k m/sqrt(log_2 m), k^2 n log_2 log_2 n/sqrt(log_2 n)))) machine steps.
- `eth/Solution.lean` states unconditional `MainResults.mainTheorem` and `MainResults.ethIsFalse`, obtained from the imported proof chain. The final statement has no cost-model or oracle hypothesis.
- `eth/README.md` describes the two deliberate `sorry`s in Challenge.lean, the trusted theorem statements; the proof theorem axioms should be propext, Classical.choice, Quot.sound. It explicitly says checking Lean does not machine-check the correspondence between informal English and the statement.
- `eth/proof/PaperIndex.lean`, introductory comments, records deviations in intermediate formal cost accounting: budgets written as blank symbols, operations polynomial in whole state, and conversion to an actual Turing machine. These affect constant factors in the final exponent, not the asserted asymptotic order.
- GitHub check-runs endpoint for the pinned commit reports `verify (eth)` success. Job URL: https://github.com/anthropics/formal-math/actions/runs/40440389861/job/121979112896 . It completed at 2026-10-27 03:22:05 UTC. This is external CI evidence; this session did NOT rebuild the 153k-line proof.
- `.github/scripts/comparator-check.sh` pins Comparator and nanoda, restricts permitted axioms to the three standard ones, forces `enable_nanoda=true`, and accepts only if Comparator exits zero and emits its acceptance string.

The two primary papers were inspected during the review. They are not duplicated in this archive; the pinned source links below identify them.

## Mathematical baseline for 3-SAT

Both source papers give deterministic exact counting, hence decision, in `2^{O(n log log n / sqrt(log n))}` for arbitrary clause density, with input-polynomial overhead as appropriate. For bounded density the OpenAI theorem gives `poly(n,m) 2^{O(n/sqrt(log n))}`. Anthropic's clause bound yields `2^{O(m/sqrt(log m))}`. Deduplication and removing unused variables are needed to compare identical input conventions.

Anthropic Appendix A, Definition 7 / Theorem A: a uniformly effective crossing decomposition with polynomially many pieces and simultaneous row/column factorization bit lengths summing to at most `4 rho lambda + O(log lambda)` yields logarithmic saving power `alpha=log_2(1/rho)`. Appendix D then gives generic 3-SAT time `2^{O(n log log n/(log n)^alpha)}`. Uniformity and the cost/height bounds in Definition 7 are essential. Pointwise existence of favorable ranks is insufficient.

Appendix B obtains `rho=1/sqrt(2)` using Heisenberg Fock spaces `V_h` of dimension `p(h)`, the partition number. The crossing pieces `A_s` use ranks bounded by `(2h+1)p(2h+s)` and `(2h+1)p(2h-s)`, with `p(h)>=2^lambda`. Hardy-Ramanujan asymptotics and concavity give the bit sum `2 sqrt(2) lambda + O(log lambda)`.

## Closing fifth-round qualification

The final ProveIt review pin is `324f3d9b009ab0323f33be65cd6577867c9c4338`.
Its `sat_pairwise_certificates/sections/barriers.tex` gives a full-crossing
rank obstruction: with polynomially many pieces factoring through the
same four-energy window, graded growth exponent beta must be at least
1/2. Consequently the beta < 1/2 specialization of the historical
conditional calculation below cannot satisfy all those same premises.
It is retained to explain the dependency, not offered as an unconstructed
but otherwise consistent algorithm. The main report gives the rank
argument and scopes it to the stated interface.

Pinned barrier source:
https://github.com/VladimirReshetnikov/ProveIt/blob/324f3d9b009ab0323f33be65cd6577867c9c4338/Computability/SubexponentialSAT/Research/sat_pairwise_certificates/sections/barriers.tex

## Conditional graded-growth transfer (rediscovered existing idea, not new)

After checking the complete local corpus, this lever is already present in `Research/3sat_round2_refinement/report/report.tex`, lines approximately 270 onward, which attributes it to Appendix H of an earlier source. Do not present it as a novel contribution.

Suppose a replacement graded algebra satisfies the exact same locality/pairing construction and has nondecreasing dimensions D(h) with

    log_2 D(h) = c h^beta + O(log(h+2)),  0 < beta < 1, c > 0,

with all basis enumeration, coefficients, pairings and integer denominators satisfying Definition 7's uniform bounds. Choose h minimal with D(h)>=2^lambda. Then h is polynomial in lambda and `c h^beta = lambda + O(log lambda)`.

The two intermediate dimensions obey

    log R_row + log R_col
      <= c((2h+s)^beta+(2h-s)^beta)+O(log h)
      <= 2^(1+beta) lambda+O(log lambda),

where the second line is concavity and `-2h<=s<=2h`. Therefore `rho=2^(beta-1)` and `alpha=1-beta`. This converts a genuinely sub-square-root graded growth law (`beta<1/2`) into a genuine improvement of the logarithmic power, IF the other algebraic and effectiveness conditions can be met.

Changing the leading constant in a square-root dimension law, using a fixed number of bosonic/fermionic species, or replacing partitions by another square-root-growth partition class does not improve alpha by this argument. The conclusion only concerns this particular construction and analysis, not all SAT algorithms.

## Rigorous obstruction to simply deleting oscillator modes (existing idea)

The infinite/infinite version and its finite-difference proof already appear in the same round-2 report. The all-proper-nonempty-S formulation below adds the finite/cofinite cases, but this is only an elementary completion and should not be sold as an improvement or breakthrough.

Let S be a subset of positive integers, and take the standard Heisenberg current with only modes in S. Over characteristic zero its commutator is the formal distribution

    [J_S(z),J_S(w)] = sum_{n in Z} a_n z^(-n-1) w^(n-1),
    a_0=0, a_n=n * 1_{|n| in S} for n!=0.

Claim: finite-order locality `(z-w)^N[J_S(z),J_S(w)]=0` for some N holds only for S empty or all positive integers.

Proof: Comparing Laurent coefficients after multiplication by `(z-w)^N` gives the N-th finite-difference equation for the two-sided sequence a_n. Over characteristic zero, every such sequence is the restriction of one polynomial P(n) of degree less than N (Newton interpolation, extended in both directions by the recurrence). If the complement of S in the positive integers is infinite, P has infinitely many roots and hence P=0; thus S is empty. Otherwise S is infinite, so P(n)-n has infinitely many roots and P(n)=n identically; then S has no missing positive integer. Conversely the empty current is local and the full Heisenberg current is local of order 2. QED.

This rules out obtaining a better beta merely by keeping square-index modes or another sparse oscillator set and applying the existing locality identity unchanged. It does not rule out a different algebra, a different cancellation identity, finite-characteristic constructions, or structured 3-SAT-specific rank reductions.

## Source URLs

- https://github.com/anthropics/formal-math/blob/1a6eee293b9e00cb432eef6018a21f523623a9af/eth/MainResults.lean
- https://github.com/anthropics/formal-math/blob/1a6eee293b9e00cb432eef6018a21f523623a9af/eth/Solution.lean
- https://github.com/anthropics/formal-math/blob/1a6eee293b9e00cb432eef6018a21f523623a9af/eth/proof/PaperIndex.lean
- https://github.com/anthropics/formal-math/blob/1a6eee293b9e00cb432eef6018a21f523623a9af/.github/scripts/comparator-check.sh
- https://api.github.com/repos/anthropics/formal-math/commits/1a6eee293b9e00cb432eef6018a21f523623a9af/check-runs
- https://github.com/anthropics/formal-math/blob/1a6eee293b9e00cb432eef6018a21f523623a9af/eth/paper.pdf
- https://github.com/VladimirReshetnikov/ProveIt/blob/324f3d9b009ab0323f33be65cd6577867c9c4338/lib/openai-math/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf
