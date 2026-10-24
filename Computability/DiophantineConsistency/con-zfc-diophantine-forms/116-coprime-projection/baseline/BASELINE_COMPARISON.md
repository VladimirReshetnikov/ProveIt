# Frozen wave-14 comparison

Repository: https://github.com/VladimirReshetnikov/ProveIt

HEAD is frozen at `84e16e43092614bae262ca59651cb9d77e31a255` (2026-10-24 19:17:46 UTC). It was read from remote HEAD and checked against the shallow local clone at 19:27 UTC. No repository scripts were executed and no repository files edited. `ProveIt/` contains a sparse clone of the complete `Computability/DiophantineConsistency` and `docs/incoming` trees. `FRONTIER_SOURCE_AUDIT.json` supplies SHA-256, exact Git blob identities/lengths for every incoming archive, and independently traversed live-operation counts for sixteen selected endpoints. Exact degrees below are pinned proof/certificate claims, not newly re-expanded in this baseline review.

## Compact comparison

All operation counts mean live binary addition, subtraction and multiplication, with squares/scalar multiplication counted and fixed numeral leaves free. Domains must remain explicit.

| Domain | Variables | Exact degree | Operations | Source relative to `ProveIt/Computability/DiophantineConsistency` |
|---|---:|---:|---:|---|
| positive | 9 | 1191570 | 405 | `research/nine-folded-shared-odd-rank/boundary_simple.json` (whole original31) |
| positive | 9 | 1316546 | 413 | `research/nine-folded-shared-odd-rank/compact_simple.json` (whole compact54) |
| positive | 10 | 368 | 99 | `candidates/ten-positive-zero-offset/equation.json` (whole compact44) |
| positive | 10 | 340 | 105 | `candidates/ten-positive-direct-zero-offset/equation.json` (whole compact44) |
| integers | 11 | 2240 | 206 | Prior delivered budget archive, `eleven/budget_intersective11_degree2240.json` |
| integers | 12 | 1000 | 180 | Prior delivered budget archive, `guard/budget12_tau_centered.json` |
| integers | 12 | 1200 | 145 | `candidates/scalar-carrier12/rational.json` |
| integers | 12 | 1456 | 141 | `candidates/scalar-carrier12/integral.json` |
| integers | 13 | 536 | 135 | `candidates/integer13-quadratic-trace/equation.json` |
| integers | 14 | 312 | 117 | `candidates/constructive-integer14-guard-reduced/equation.json` |
| integers | 15 | 172 | 123 | Newly arrived separate Compact Proof Certificates Round13, `radicals/integer15_degree172.json` |
| integers | 15 | 170 | 134 | Same separate Round13, `radicals/integer15c_degree170.json` |
| integers | 16 | 98 | 138 | Same separate Round13, `radicals/integer16_degree98.json` |

The incoming 15-integer172/123 endpoint dominates the user's preceding delivered15-integer176/125 endpoint in both measures. Incoming archives are not automatically accepted repo endpoints: `docs/incoming/README.md` distinguishes arrival, placement and review. New proposals must compare against inspected incoming claims as well as reviewed candidates.

Latest direct-calculus quartics are `research/factorial-radius-output-sign-profile/`: 75 predicates, raw/default support8 or16 yields604 integer variables,372 quadratic rows,9676 quartic monomials,height2445790974704. The lower-height609-variable sibling has377 rows,8823 terms,height964213;608-variable sibling has8739 terms,height45769499. These are not global variable minima because other native encodings have much smaller fixed-variable quartics with different large-coefficient architectures.

The canonical displayed one-page equation remains10 positive variables,368degree,101operations (`CURRENT_EQUATION.json`). Its deliberate delayed rendering update must not be mistaken for the current99-operation research frontier.

## Current source locations

- Prior delivered archive extracted to `budget/ZFC_Diophantine_Budget_Interpolation/`.
- Separate incoming Round13 extracted to `round13/ConZFC_Compact_Proof_Certificates_Round13_2026-10-24/`.
- For each accepted candidate above, `README.md`, `PROOF.md`, `SOURCE_PINS.json`, literal equation and exact `CHECK`/`BUILD` files are present beside it. No stored receipt is represented as a replay performed in this round.
- New changes since9ba3973 are405/413 operation odd-rank sharing,75 predicates via early power-output sign recovery, and complete604-variable quartics. Commite13c7482 adds six incoming archives, including the user's prior Budget Interpolation and separate Compact Proof Certificates Round13 packages.

## Promising cross-compositions identified from actual proofs

1. Scalar-carrier12 removes the main root using `Phi_H(HT+K)` and signed folding, leaving a four-root norm. Combine with the prior centered budget guard, which needs no nearest-square coordinate t, to target11 integers/F16 instead of the prior11 integers/F32. The proof obstacle is ordering: establish nonzero strong scale, guard positivity, main Pell classification, signed rank, whole-product projection, then late positive orientation. Prior budget `eleven/PROOF.md` Section5 already treats the nonodd strong multiplier and centered `|eta/k|<1/2` strip.
2. A lower-risk12-integer companion combines `integer13-quadratic-trace` with `Budget=k^2(q^2-Derr)-4q^2 eta^2` and `Ag=Budget-1-p2^2-p3(p3+1)`. This removes the extra joint-guard t and the main root simultaneously. Signed bootstrap and centered half-binomial recovery must again precede importing the old positive kernel.
3. For direct quartics, raw93's sign now follows from the exact unconditional original-row ideal `N=f*r+(f-1)*s+f`, using only retained f>=2,r,s>=0 before prefix semantics. Further signs should be sought as unconditional original-row consequences rather than assuming factorial/power meanings before their domain is restored. Merely removing three guard witnesses does not establish a projected variable count.

These are research leads, not completed theorems or novelty claims. They were sent to the corresponding mathematical workers.

## Coefficient safety

The ten-positive99/368 and105/340 literal candidates bind whole compact44: K0 has592884bits, rawSHA256 `c6d523bd32af8dd0345db843cdadf6932bfcad186912a6d112314b60657c554e`. The corrected BFS recipe instead has K434054bits, rawSHA256 `562494dbbe6e4651e55697f28596e801e341d50338bb902781c252912f3b2163`. They are different coherent tuples, not interchangeable constants. `INITIALIZATION_CORRECTION.md` records initial head93→1 and complete language conjugacy. Original31, compact54, source34 six-port and BFS44/source44 four-port families stay separate. MF ports are already shifted.
