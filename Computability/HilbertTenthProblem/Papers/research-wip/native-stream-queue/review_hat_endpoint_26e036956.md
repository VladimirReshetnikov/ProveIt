# Independent endpoint proof challenge: hat randomness frontier

**PASS at the bounded scope below.** The private-seed and finite-public-seed exclusions at uniform expected inspection cap1 follow from the stated model and their now-reviewed dependencies. No mathematical correction is requested. In particular, the proof does not assume that the marginal cap remains valid after conditioning on every seed outcome. It excludes almost-sure success, not all positive-probability success.

## Immutable source and additional read scope

Source arrival: `26e036956381b07bb43de0187965f8dcdf9194fb`.

Archive: `docs/incoming/hat_randomness_frontier.zip`, SHA256 `eccc49ac838592997e1c7d8ef0c5ba7c1a95bd76abbb8f12814f552dc34b9e20`.

Member: `hat_randomness_frontier/hat_randomness_frontier.tex` (66,266 bytes; 1,660 lines). Exact member and normalized read-span hashes are in the companion JSON.

This follow-up adds a complete read of lines263–680, 418 lines not included in the earlier proof scope. They contain covariance and query-cost control, zero-inspection projection, the private refinement, owner-indexed Walsh accounting, the self-contained fourth-moment bound, spectral sign control, and the aggregate/variance-overhead theorems. I reexamined the model at193–262 and the endpoint arguments at681–822. Thus the complete dependency interval193–822, 630 lines, is covered.

The earlier review `review_new_actions_26e036956.md` remains immutable, with its original limited scope. This note adds proof coverage rather than retroactively claiming that the earlier read included these arguments. The finite block, scheduling, deterministic upper-bound and entire full-article proof remain outside this follow-up. No supplied verifier, prior collector, archived code, builder or predecessor was run or imported. No external-paper or formalization certification is claimed.

## Query cost, covariance and Fourier accounting

The model gives each player a measurable adaptive algorithm, blind to its own hat, with seeds independent of hats and almost-sure termination. Computation and external randomness are free; Q_i counts individual inspected hats. Coordinate-flip exceptional sets can be removed simultaneously because only countably many players and finite-coordinate flips occur. Repeated inspection can only increase the cost.

Conditioning on every other hat and all seeds leaves the two scored owner hats independent and fair. Expanding the two guesses affinely in those two signs proves the covariance/derivative identity. The event of first inspecting a given coordinate is unchanged by that coordinate's flip: transcripts agree until the first query. This yields the derivative bound and hence the stated variance sandwich even when scored players inspect outside the scored prefix.

For zero-query players, the decision to stop without inspecting depends only on accessible seeds. After conditioning on their hat values, every other scored player's own hat is still independent and fair, so its score has conditional mean zero. The projection identity and both zero-query moment estimates are valid. The independent-private improvement uses independence of the zero-query seed events and of owner hats; it is not asserted for a shared seed.

After freezing seeds, Walsh coefficients of Y_i are supported only on finite sets containing i. Parseval gives total owner energy n, and a singleton Fourier term has exactly one possible owner. The derivative/query bound controls the sum of `(degree−1)` times owner energy. Consequently, if B_n<=n+K with K>=0, then

`sum_(degree>=3) (degree−2)*owner_energy <= V_1+K`,

and `degree<=3(degree−2)` on that range gives

`v_n <= 4 ||P_(<=2)F_n||_2² + 3K`.

This does not assume that all Fourier variables lie in the scored prefix. Countable-coordinate expansions follow by L² approximation and nonnegative influence summation; finite mean cost gives finite relevant sums.

The fourth-moment induction with rho²=1/3 is correct: its mixed term is bounded by2a²b² and its final term by b⁴/9, below `(a²+b²)²`. Applying it to coefficient-rescaled degree-d polynomials and then to finite-coordinate approximation differences proves the countable-coordinate extension. The interpolation and centering argument then gives

`P(F_n<0) >= ||P_(<=d)F_n||_2^4 / (4*3^(2d)*v_n²)`.

The zero-low-mass case is trivial; no division by a vanishing projection is required. With d2 and the energy bound, the aggregate constant is exactly1/5184. The v_n>=6K version is1/20736. These constants were independently checked.

## Deterministic aggregate obstruction

Almost-sure F_n→+infinity implies v_n→infinity by Fatou and P(F_n<0)→0 by bounded convergence. If B_n−n failed to tend to infinity, some fixed finite K would bound it from above along an infinite subsequence. Along that subsequence the preceding negative-sign probability stays bounded away from zero, a contradiction. This proves the necessary divergence of cumulative deterministic expected cost, not a per-player conditional cap.

The argument also handles a deterministic strategy with infinite expected cost at a player: then B_n is infinite thereafter and the conclusion is immediate. In the nontrivial bounded-subsequence argument the needed finite cost hypotheses are present. The influence-only version and the stated variance-scale lower bound follow from the same owner-energy inequalities. In particular, for fixed d the latter discards only nonnegative middle-degree terms before applying the spectral estimate; sending n and then d to infinity is justified in that order.

## Stopped process and conditioning

For the cost lemma, c_i are nonnegative and integrable, with conditional mean at most1 (independence and marginal mean at most1 suffice). Thus S_n=sum(c_i−1) is an integrable supermartingale whose downward increments are bounded by1. No upper bound on jumps and no uniform second moment is assumed or needed.

Stop at the first lower crossing below−K, first upper crossing at least M, or deterministic time N. The stopped value is at least−K−1, and at least M on an upper crossing. Bounded stopping gives expectation at most zero, hence upper-crossing probability at most `(K+1)/(M+K+1)`. Taking N and then M to infinity excludes an unbounded-above path with a fixed global lower bound. Every finite-valued sequence tending to positive infinity has such a lower bound, so a countable union over K proves the lemma. The proof never applies optional stopping directly at an unbounded stopping time.

For private seeds, define c_i(U_i) by averaging Q_i over all hats. This removes the inter-player hat dependence: c_i is now a function of U_i alone. The resulting costs are independent, nonnegative and integrable, and their means satisfy the original marginal cap. Conditional costs can exceed1; the proof permits that. By the finite marginal expectations, the costs are finite for almost every private seed sequence simultaneously for all players. Fubini also provides conditional legality and almost-sure hat success on a common full-measure set if joint success were one. The deterministic aggregate theorem would force S_n→infinity there, contradicting the cost lemma.

The stronger private success-gap corollary is also sound. For almost every seed sequence the cost lemma gives some finite K and infinitely many n with B_n<=n+K. If the conditional success probability p(u) is positive, Fatou still forces v_n→infinity. The aggregate bound gives limsup conditional negative-sign probability at least1/5184, whereas bounded convergence on the success event bounds it above by1−p(u). Integration gives success at most1−1/5184. This is not a probability-zero theorem, and does not settle the open positive-probability private endpoint question.

For a finite public support, conditioning on each positive-mass public outcome and then on private seeds yields simultaneous deterministic almost-sure successes on a common full-measure set. Form the weighted costs `z_i(U_i)=sum_r p_r c_i(t_r,U_i)`. They remain independent across i, with mean at most1, because each depends only on its own private seed and the public averaging is already performed. The finite weighted sum of the divergent deterministic excess-cost sequences diverges, contradicting the same lemma. No cap at each t_r is assumed. Independence of private seeds from the public seed is an explicit hypothesis and is used here.

Finiteness matters at this last limit interchange, not merely in taking a common full-measure set. The proof correctly declines to exchange a limit with an infinite weighted sum.

## A scalar check on the independence boundary

For additional clarity, let an integer T>=0 have `P(T=t)=1/((t+1)(t+2))`, and define correlated nonnegative costs

`c_i(T)=0 if T>=i; c_i(T)=(i+1)/i otherwise`.

Then P(T>=i)=1/(i+1) and E c_i=1. Nevertheless, for every finite T=t,

`sum_(i<=N)(c_i−1) = −min(N,t) + sum_(i=t+1)^N 1/i`,

which tends to infinity. The covariance of c_1 and c_2 is1/2. This is a direct illustration that marginal means alone cannot replace the stopped-process conditional-mean hypothesis or justify a countably infinite public averaging step. It is **not a hat strategy** or a new counterexample to any claim of the manuscript. The manuscript already respects this boundary.

The fresh checker verifies128 exact mean identities and2,145 finite path identities for this scalar model, together with the constants and immutable byte/read-span pins. The all-size endpoint proof is the mathematical argument above; these finite identities are not its certification.

## Status, limits and artifacts

Root separately read lines470–822 in full, plus193–262 and1210–1258, and reported a second mathematical challenge PASS with no finding. That contribution is proof-only; root ran no fresh numerical check for it. It does not enlarge the new read spans recorded by this reviewer.

No false or unproved step was identified within these endpoint arguments, so no source claim needs to be corrected or moved under the incoming retention rule. This result adds an independent mathematical check of the private and finite-public nonattainment arguments and their analytic dependencies. It does not certify all upper constructions, the full article, formal proof-assistant status, or external literature claims.

Expected hat-query caps cannot be compared to the paid arithmetic-gate count of a Diophantine compiler. No arithmetic saving, fixed-arity polynomial, or universal-computation consequence is inferred here.

| Fresh reviewer file | SHA256 |
|---|---|
| `/tmp/review_hat_endpoint_26e036956.py` | `00295c046a5a9fa33dfd77604353bb780f49835efe39ddb08ff90c13abcb4c62` |
| `/tmp/review_hat_endpoint_26e036956.json` | `8c605eda7ea586e40ae7d3855ec0a9892457de08f266e9073181ac2998167129` |

The newly authored metadata/scalar checker passed writer, normal and optimized-Python exact receipt replays from `/` before freeze. There were no repository mutations or supplied-program executions.
