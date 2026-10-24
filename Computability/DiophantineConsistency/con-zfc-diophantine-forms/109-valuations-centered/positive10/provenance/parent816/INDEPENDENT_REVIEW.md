# Independent review

Two adversarial review rounds were run. The reviewer was an independent
Claude subagent. It received the package files and the cited sources, but
not the author's conclusions, and was asked to break the claim. It worked
read-only on the repository; its scripts stayed in the session
scratchpad. Neither round re-verified package 61's inherited `thm:source`
or the competing arrivals' proofs.

## Round 2: the present version (124 operations, exact degree 816)

| Aspect | Verdict |
|---|---|
| Soundness, relative to `thm:source` | Holds. No FATAL or GAP finding. The order 6.4 → 6.8 → 6.9–6.15 → 6.16 → 6.17 → 6.18 is not circular, and the rational g, s, t are used only as rationals |
| Completeness | Holds. One missing justification was supplied (item 2) |
| Exact degree 816 | Correct. Attacked three ways; see below |
| Operation count | Correct: 124 = 74 × + 30 + + 20 −, eight multiplications by numerals, 28-row norm, every row and input live |
| README numbers | Accurate as of `PROPOSAL_REVIEW_LATEST.md` |

**Findings and their resolution.**

| Item | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | MINOR | §5.2: for F < q the bound is G ≤ (q−1)²+α, not <; (5.2.1) still follows | Fixed |
| 2 | EDITORIAL | §7 did not say why S²⁰ > α | Added: C > 0 gives α < q < q⁴ < Δ′ ≤ S |
| 3 | EDITORIAL | the 28-operation compact norm is already in the radical-residue circuit (rows g094–g130) | Credited in PROOF §0, §9 and the README |
| 4 | EDITORIAL | the inner cancellation ω is the joint-guards centered identity; only the sixteen-fold pairing and weight argument are new | Credited; "new here" narrowed |
| 5 | EDITORIAL | the offset T+F+α and the second center Cf come from the polynomial-shears arrival | Credited; the adaptive candidate inherits it |
| 6 | EDITORIAL | completeness uses the construction inside 61's proof of `lem:auxcomplete`, not only its statement | Stated in §0 |
| 7 | EDITORIAL | `lam` reused in L4 and L7 | L7 now uses phi |
| 8 | EDITORIAL | this file was missing | This file |
| 9 | EDITORIAL, optional | the arrival (19:09, reviewed 19:34) predates the first version's package files | Recorded in the README. The construction was already in scratch; the sixteen-fold norm check dates from 19:05 |

**Round-2 coverage.**

* **Scaling, offset and Archimedean step.**
  - μ² is coprime to q³(q−1)H′, and L3 gives μ² | e.
  - (5.2.1) holds without assuming C > 0.
  - Step 6.16 is correct. The shared-factor case is real: the toy kernel
    at (q, R) = (16, 51) has gcd(H′, q−1) = 15.
* **Transport weight with rational g, s, t.** Steps 6.6–6.8 were re-derived
  by hand and tested on 37,752 inputs with b′ ≥ 1, with no failures.
* **Completeness.**
  - μc² divides ψ_A′(Rcμ).
  - The bound Q_h(x) ≥ (4x−3)^h and the chain V* ≥ (3S²)¹² hold.
  - n is positive, including its new term u.
* **Compact F16.** Equal to the 16-factor product, checked independently in
  SymPy.
* **Exact degree 816.**
  - Lemma 8.1 and the ω identity were checked symbolically.
  - Full expansion of F16(s; a, b, s−ω, d) under the stated weights: the
    maximum weight is 816, reached only by ω⁸, with coefficient 1.
  - Every leading form in §8 is nonzero.
  - With the reviewer's own transcription and the actual ports, on lines
    through the origin modulo 2^61−1, 2^107−1 and 2^127−1, the finite
    differences of order 817–931 vanish and N₈₁₆ = ω₀⁸. ω has exact
    degree 102 with top form ω₀.
* **Section 5.** Exact certified tests on 63,253 toy-port inputs, 1,293 of
  them with b′ = 0. Six adversarial actual-port inputs cover C = 0, C < 0,
  R < 0 with b′ > 0, b′ > 0 with R > 0, b′ < 0, and an exact b′ = 0 with
  c = 3. There were no failures, and a planted false claim was caught.
* **Circuit.** `circuit.py` matches the reviewer's transcription of §1 at
  40 exact toy-port points and 20 actual-port points modulo 2^127−1. The
  JSON's register degrees match §8.
* **Package audits.** `verify.py --quick` passes.

## Round 1: the superseded version (136 operations, degree 1216)

**Verdict.** Soundness and completeness held relative to `thm:source`,
with no FATAL or GAP finding. The degree and operation count were
confirmed independently.

The README's frontier claim was wrong. The radical-residue arrival had a
ten-positive equation at 131 operations and degree 1152, on the same tuple
and domain, and it was already recorded in the repository. It dominated
that version.

The author had found that arrival independently while the review ran, and
rebuilt the construction into the present version.

| Finding | Severity | Resolution in the present version |
|---|---|---|
| F1: README overlooked the 131/1152 form | MINOR (reversed the headline) | The present version beats it in both measures, and the README compares against it |
| F2: other comparison rows stale | MINOR | Rebuilt from `PROPOSAL_REVIEW_LATEST.md` |
| F3: novelty overstated | EDITORIAL/MINOR | PROOF §0, §9 and the README credit the arrivals; see round 2, items 3–5 |
| F4: CHECKS.json predated the final verify.py | MINOR | Regenerated by the final `verify.py` (round 2 confirmed) |
| F5: this file missing | EDITORIAL | This file |
| F6: "genuine sizes" overstated the toy-q kernel audit | EDITORIAL | Reworded |
| F7: symbol clashes | EDITORIAL | q = 2^kappa; the norm difference is omega; L7's index is nu |
| F8: (P8) citation | EDITORIAL | The even-index congruence is attributed to the recurrence |
| F9: trust-boundary wording | EDITORIAL | `thm:source` is the only inherited theorem; package 70 needs more |
| F10: one step-down case implicit | EDITORIAL | Stated |

**Round-1 coverage of machinery the present version keeps.**

* Lemma 2.1 by independent SymPy expansion.
* P1–P8 and L1–L7.
* The Section 5 separation: 46,564 toy-port inputs and 6 adversarial
  actual-port inputs, with no failures.
* First-Pell classification (k must be even).
* The index, rank, parity, ratio and half-binomial steps.
* All six equations of package 61's system, satisfied by the rebuilt
  coordinates, including T_old = f_o·T*.
* The citations to packages 61, 69 and 70 and to the parity and kernel
  notes.
