# Integrated mathematical review

Reviewed 1 October 2026.

## Verdict and reviewed artifacts

APPROVED for the mathematical claims and qualifications stated below. The complete integrated source was read as a proof, including the new third coefficient and its explicit remainder. Exact symbolic checks corroborate the finite identities; they are not used as evidence for the analytic estimates or the probabilistic transfer.

This verdict applies to the following exact artifacts:

- `takeuchi-asymptotics.tex`, SHA-256 `40d52eb680316dd97f9c5c39fd208c341bc15c1c4301169da86f22d1d0751ad3`
- `takeuchi-asymptotics.pdf`, SHA-256 `c85426482011fadfe29f33136dc4462e6226b4416d68a5300413c58923b8a9ed`

The source needs no mathematical amendment. This is an independent checking record for a research manuscript, not external peer review or a claim of priority. Historical source interpretation, an exhaustive literature search, and numerical enclosure of the normalizing constant are outside this mathematical verdict.

## 1. Local recurrence and two-correction estimate

The positive recurrence, integer coefficient identity, and leading factor are consistent with the stated indexing. In particular, `n^k exp(-(k+1)w)/k! = exp(-w)w^k/k!` when `n = w exp(w)`, so the finite Poisson-moment calculation arises from the exact recurrence rather than a heuristic saddle replacement. The differentiation rule `D = h d(w) partial_w - h^2 partial_h`, with `d(w)=w/(1+w)`, correctly generates the shifted jets.

For `k <= w^2`, the shifted interval lies in `[n/2,n]` eventually. Each fixed derivative of F beyond its first is the stated inverse power of n times a bounded rational function of w. Positive-order derivatives of g have scaled growth O(1+w); the first two correction functions have scaled derivative growth O(1+w) and O((1+w)^2). Thus the two-correction logarithmic remainder is O(X^5/n^4), where `X=1+w+k`, and the retained coefficients satisfy `|A_r| <= C_r X^(r+1)`. Since X^2/n tends uniformly to zero, exponentiation gives O(X^8/n^4). Finite Poisson moments turn this into O((1+w)^8/n^4).

The intermediate tail bound C(Aw)^k/k! is valid uniformly on `w^2 < k <= n/2-1`; its sum is exp(-w^2 log w + O(w^2)). The far-tail coefficient bound 4^n is dominated by the model ratio exp(-n log n/3), including the finitely many arbitrarily assigned positive model values. The same growth comparison controls the forcing b_n. Both tails and the forcing are smaller than every fixed inverse power of n. These facts justify completing the central finite sums to full Poisson expectations.

## 2. Faithful coupling and quantitative transfer

The Poisson shift estimate is valid with the stated constant. The block length gives variance at least 64 a^2 (log n)^2, and the aligned starting separation is at most 2 a log n. Hence the ideal endpoint total variation distance is at most 1/4. Localization and the parameter variation bound W'(x)<=1/x change the exact killed endpoint laws by o(1), uniformly over admissible starting pairs, yielding a fixed overlap of at least 1/2.

The filtration issue is handled correctly. The endpoints are maximally coupled, then each entire internal path is sampled from its exact conditional bridge law. Both complete killed blocks are finished before any joint stopping, failure, or continuation decision. At each block boundary, the conditional full coordinate path law is consequently the correct killed Markov law. The proof never assumes that a bridge's next transition retains its original kernel when conditioned on the other path's revealed interior information. Alignments use ordinary transitions and ordinary stopping decisions instead.

The first alignment is uniform over every finite m>=n: a good jump crossing n cannot depart from r>=2n for sufficiently large n. All later good trials remain above 3n/4 because their combined descent is O_D((log n)^3). A bad-jump probability is bounded by summing C_B r^(-B) over distinct visited departure states; this is uniform even for arbitrarily large m. The number of trials is O_D(log n), and B>D+3 suffices for the claimed O_D(n^(-D)) failure bound. Conditional on each good boundary history, unsuccessful endpoint coupling has probability at most 1/2. Intersecting with continued goodness cannot increase that probability. The o(1) endpoint comparison only establishes the fixed overlap and is not incorrectly charged as the ultimate failure probability.

On success the paths can be continued together; after an abort fresh correct kernels extend both attained paths. Thus the construction supplies full descending-chain marginals. For a bounded solution of the additive recurrence, iteration over each atomic block or alignment gives the exact endpoint-plus-forcing identity. Each coordinate's departure states are distinct and greater than floor(n/2), so the forcing is bounded by the stated tail sum. There are finitely many transitions for each finite starting pair, avoiding an unbounded optional-stopping assumption.

## 3. Boundedness, positive limit, and all fixed orders

The row sums differ summably from one, and the positive forcing is summable. The running-maximum induction gives a bounded normalized sequence before the additive stability theorem is invoked. The resulting forcing depends on the exact normalized sequence but is deterministic and satisfies the required summable bound; no independence assumption is needed.

The positivity proof correctly removes the transition to index zero. Its weight is in the established superpolynomial far tail. The remaining positive-state row sum is at least 1-d_n for a summable sequence with 0<=d_n<=1/2. All finitely many initial positive-index ratios are positive, and the infinite-product induction gives a uniform strictly positive lower bound. Thus taking logarithms of the limiting ratio is justified.

The fixed-order coefficient construction is triangular. Inserting p_j/n^j first changes the residual at order n^(-j-1) by `-w p_j' + j(w+1)p_j`. The negative tail quadrature in the manuscript has the correct integrating-factor sign. Differentiation under its convergent integral preserves smoothness and polynomial growth of every fixed derivative. The homogeneous freedom is c exp(jw) w^j, excluded by polynomial growth, and it would otherwise change only the global log normalization.

At every fixed J only finitely many Taylor derivatives and Poisson moments are needed. Their remainders are uniformly n^(-J-2) times polynomial envelopes on k<=w^2. The exponential truncation remains uniform there, and the same intermediate and far-tail bounds apply. The normalized kernel has the necessary O(polylog(n)/n) total variation comparison and arbitrarily strong polynomial jump-tail bounds. The argument includes J=0, where the row defect is already summable.

The transfer tail sum loses one inverse power of n, exactly as stated. All p_j/n^j tend to zero for fixed j, so every finite model has the same positive limiting constant C. No historical leading equivalent, convergent infinite asymptotic series, or all-order rationality claim is assumed.

## 4. Literal third coefficient and growth

A fresh independent symbolic construction, importing none of the package's residual-generator code, verifies the displayed polynomial H3 from the finite-product logarithms, the differentiated shifts, and Poisson polynomial moments. It also verifies the first three cancellations, the literal rational p3, and

`-w p3'(w) + 3(w+1)p3(w) + H3(w) = 0`.

Both the displayed H3 and p3 agree exactly with their independent constructions. Their leading limits are

- H3(w)/w^5 tends to -1/24
- p3(w)/w^4 tends to 1/72

The numerator degree is 13 and the denominator degree is 9, with leading coefficient 240/17280=1/72. Thus the warning against assuming p_j=O(w^j) is necessary and correct. The polynomial-growth uniqueness argument identifies this p3 with the canonical quadrature; the third coefficient is not selected merely by a numerical fit or an arbitrary rational ansatz.

## 5. Corollary 8.1 explicit exponent

For the three-correction model, the four retained logarithmic coefficients have joint (w,k) growth degrees at most 2, 3, 4, and 5 respectively. The additional p3 term first contributes at order four as `-(k+1)(d p3'-3p3)`, whose growth is O((k+1)(1+w)^4), still O(X^5).

The first omitted logarithmic terms, all at order n^(-5), have the following numerator bounds:

- Product logarithms: O(k^6)
- F sixth-derivative remainder: O((k+1)^6)
- g fifth-derivative remainder: O((k+1)^5(1+w))
- p1/n fourth-derivative remainder: O((k+1)^4(1+w))
- p2/n^2 third-derivative remainder: O((k+1)^3(1+w)^2)
- p3/n^3 second-derivative remainder: O((k+1)^2(1+w)^4)

Every item is O(X^6). The scaled rational derivative bounds hold uniformly on `[n-k-1,n] subset [n/2,n]`, because the denominators have no poles there and W varies by a bounded amount. The unexpectedly larger growth of p3 has therefore been fully charged in this remainder.

Exponentiating through inverse-power degree four leaves O(X^10/n^5). One way to check the envelope is to use `|A_r| <= C X^(2r)` for X>=1 and X^2/n=o(1); every omitted finite product of inverse-power degree at least five is then bounded by the fifth power of X^2/n, with higher terms absorbed uniformly. The log remainder is smaller than this envelope. Its Poisson expectation is O((1+w)^10/n^5), and the exact fourth-order cancellation removes all lower terms.

The established superpolynomial tails and forcing apply unchanged. Applying the faithful stability theorem to the exact additive defect gives a ratio error O((1+w)^10/n^4). Positivity converts it to the logarithmic error of Corollary 8.1 with the same exact C. No sharper occupation estimate or unproved cancellation is needed.

## 6. Inverse statements and ceilings

The eventual real-model slope is asymptotic to W(x), including the third coefficient because its derivative contribution is polynomial in W divided by x^4. The error first localizes the inverse to `[n/2,2n]`, where the slope is uniformly bounded below by a positive multiple of W(n). The mean-value theorem then gives the stated inverse error. In particular the third-correction logarithmic error O((1+w)^10/n^4) yields O((1+w)^9/n^4) in real index.

For arbitrary large y, strict monotonicity of T_n follows directly from its recurrence. Both log envelopes h_J plus or minus E are eventually increasing. The upper log envelope is inverted for the lower integer bound and the lower log envelope for the upper integer bound, so the manuscript's ceilings have the correct orientation, including equality at an integer endpoint. Their replacement by ceilings of x plus or minus eta is valid by monotonicity of the ceiling function and the inverse localization estimates.

The caution about discrete rounding is mathematically essential: a shrinking interval need not avoid an integer boundary for arbitrary targets. Eventual nearest-integer rounding at values known in advance to equal T_n is valid in principle, but no numerical onset or certified value of C is supplied. Replacing C by historical unenclosed digits introduces a separate log error and cannot certify numerical inversion.


The final source also includes independently checked explicit reversion around the exact leading-model inverse v=F^(-1)(log y). For every fixed J>=1, with w=W(v), q=g+log C and a=d g', the correction B=a q/w^2-d q^2/(2w^3)-p1/w cancels the first inverse-power residual exactly. The remaining log residual is O_J((1+w)^3/v^2), giving an index error O_J((1+w)^2/v^2). Its leading form is v-w/2+log(1+w)/(2w)-log(C)/w+O_J((1+w)/v), with an absolute error tending to zero; B/w tends to 3/8.

The finite Newton hierarchy is also approved. Root and seed are first localized inside an O(1+w) interval with margin. There h_J' is uniformly comparable to w and h_J''=O_J(1/v), so the exact Newton error obeys |e_next|<=C_J e^2/(v w). Starting from error O_J(1+w), each fixed r gives O_(J,r)((1+w)/v^(2^r-1)); the same estimate keeps the iterates in the valid interval. At sequence values, choosing 2^r-1>J+1 makes this error negligible relative to the stated localization scale. Both the exact core inverse and exact C are assumed. This supplies a finite asymptotic inversion algorithm, without a convergence claim for an infinite formal inverse expansion or a certified floating-point algorithm. See `inverse-review.md` and the independent `code/check_inverse.py`.

## 7. Verification limits

The package's independent and generic symbolic checks were replayed separately from the proof reading. Fresh exact recurrence integers support the stated numerical examples. Those examples use a historical decimal constant, explicitly unenclosed, and are consistency diagnostics only.

Approved conclusions are the two- and three-correction logarithmic estimates, a common strictly positive limit, the canonical arbitrary fixed-order hierarchy, the eventual real-inverse errors, and the rigorous asymptotic threshold brackets. This review does not establish convergence of the infinite expansion, optimal truncation, exponential completeness, rationality of every coefficient, a practical effective constant enclosure, or unconditional exact threshold rounding from floating-point data.
