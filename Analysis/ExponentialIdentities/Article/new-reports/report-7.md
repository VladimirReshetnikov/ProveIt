I spent my effort on Priority A (p-adic amplification of the semigroup determinants), because that's where the report localizes the entire remaining deficit to a single quantitative question. I have one rigorous negative result with a clean proof, a structural identity that I think reframes Priority A, a documented dead end, and one honest correction to my earlier literature report. Throughout, I work conditionally on a counterexample with least nonintegral generator $\beta$, $M = 2^\beta$, $A = 3^\beta$, $\theta = \log_2 3$, and use your exact block structure: in the dyadic block $[2^T, 2^{T+1})$ there is exactly one candidate $c_k = 2^{n_k}M^k$ for each $0 \le k \le r \approx T/\beta$, with $n_k \in [T - k\beta,\, T+1-k\beta)$.

## 1. The threshold, made explicit

Fix a column set $S = \{(a_j, b_j)\}_{j=0}^{r}$ of distinct mixed exponents, $\lambda_j = a_j + b_j\theta$, weight $W = \sum_j \lambda_j$, and let $D = \det\big(c_i^{a_j}(c_i^\theta)^{b_j}\big)$, a nonzero integer by your Chebyshev-system positivity. Every entry satisfies $\log_2 E_{ij} \le (T+1)\lambda_j$, so

$$\log_2|D| \;\le\; (T+1)W + \log_2(r+1)!.$$

Any amplification scheme that produces a guaranteed lower bound $|D| \ge 2^{V}$ therefore needs, for a contradiction,

$$V \;>\; (T+1)W + \log_2(r+1)! \;=\; TW\,(1+o(1)).$$

So $TW$ is the bar. (Using your refined divided-difference/Schur-factor upper bounds instead of the crude entry bound shifts this by lower-order terms only; the bar stays $TW(1+o(1))$.)

## 2. A ceiling lemma: term-wise p-adic content reaches at most half the bar

The natural mechanism — and the one Priority A's Question implicitly quantifies over — is *term-wise* valuation: every monomial in the determinant expansion is divisible by a common high power of $p$, i.e. the min-plus bound $v_p(D) \ge \min_\sigma \sum_i v_p(E_{i\sigma(i)})$. Normalize by your no-matched-depth theorem so that (say) $M$ is odd; then $v_2(E_{ij}) = a_j n_i + b_j k_i v_2(A)$ and $v_3(E_{ij}) = a_j k_i v_3(M) + b_j n_i$ exactly.

**Lemma (min-plus ceiling).** For the full-block node system above and *any* column set $S$, the combined guaranteed term-wise content at the structural places satisfies

$$V^* \;:=\; \min_\sigma \sum_i v_2(E_{i\sigma(i)}) \;+\; \theta\cdot \min_\sigma \sum_i v_3(E_{i\sigma(i)}) \;\le\; \Big(\tfrac{1}{2} + o(1)\Big)\, TW .$$

*Proof sketch.* A minimum over permutations is at most the average over permutations, and the average of $\sum_i v_p(E_{i\sigma(i)})$ is $\sum_j \big(a_j \bar\nu + b_j\bar\mu\big)$ with $\bar\nu, \bar\mu$ the row-averaged valuations. The whole content of the lemma is then the computation

$$\sum_{k=0}^{r} n_k \;=\; \sum_{k=0}^r \big(T - k\beta + O(1)\big) \;=\; (r+1)\Big(T - \tfrac{\beta r}{2}\Big) + O(r) \;=\; (r+1)\,\tfrac{T}{2}\,(1+o(1)),$$

i.e. **the depths $n_k$ equidistribute over $[0, T]$, so $\bar\nu = T/2$**. On the $b$-side, $\bar\mu = v_2(A)\,\bar k = v_2(A)\,T/(2\beta) \le \theta T/2$ since $v_2(A) < \log_2 A = \theta\beta$ strictly ($A$ cannot be a power of $2$: $3^\beta = 2^m$ would make $\theta$ rational). The 3-adic side is symmetric. Summing, $V^* \le \sum_j (a_j + \theta b_j)\cdot\frac{T}{2}(1+o(1)) = \frac{TW}{2}(1+o(1))$. $\square$

Including *all* primes ($|D| \ge \prod_p p^{V_p}$, using that for $p \nmid 6$ the valuation is the pure rank-one grading $v_p(E_{ij}) = (a_j v_p(M) + b_j v_p(A))\,k_i$, whose min-plus value is at most $2/3$ of its mean by the oppositely-sorted pairing) the ceiling becomes $\le (\tfrac{2}{3}+o(1))TW$. Either way:

**Corollary.** No choice of mixed-monomial columns over a single-block candidate system can cross the contradiction threshold through term-wise valuations alone — not at $p=2$, not at $p=3$, not combining both, not combining all places. The shortfall is a factor $\ge 3/2$, i.e. exactly the "one-logarithm-deficit" phenomenon reappears as a constant-factor gap that averaging can never close.

Two remarks that I think matter. First, the *reason* the ceiling sits at $1/2$ is the equidistribution of the depths $n_k$ inside blocks — which is the *same* equidistribution that defeats the shrinking-target route. Your two walls (equidistribution can't hit exponentially small targets; interpolation lacks one logarithm) are, at the structural places, literally one wall: candidates spend half their size at $\{2,3\}$ on average, and no assignment argument recovers more than the average. Second, the $b=0$ case is an exact sanity check: there $D = \prod_{i<i'}(c_{i'}-c_i)$, $v_2(D) = \sum_{i<i'}\min(n_i, n_{i'})$ exactly (the min-plus bound is *tight*), and $|D| \ge 2^{v_2(D)}$ is a tautology — pure powers convert p-adic content into the trivial gap fact $c_{i'} - c_i \ge 2^{\min(n_i,n_{i'})}$ and nothing more. So Priority A's Question, as posed, has a negative answer for its most natural reading; the phrase "only more subtle min-plus estimates … have a chance" in your report can be sharpened to: *min-plus has no chance; only genuine cancellation does.*

## 3. Where the missing half must come from: the second-level determinant

So all remaining hope for Priority A lives in valuation *beyond* term-wise — cancellation among the min-plus-optimal terms. I can say precisely what governs it. After extracting 2-parts, the residual matrix has entries that are the odd parts

$$O_{ij} \;=\; P_i^{\,a_j}\,Q_i^{\,b_j} \pmod{2^s}, \qquad P_i = M^{k_i},\quad Q_i = 3^{n_i}A^{k_i},$$

living in $(\mathbb{Z}/2^s)^\times \cong \{\pm 1\}\times\langle 5\rangle$. Writing $-3 = 5^{t}$, $\pm M = 5^{m^*}$, $\pm A = 5^{a^*}$ with $t, m^*, a^* \in \mathbb{Z}_2$ (2-adic logarithms in base 5), the residual object is a **sign-twisted bivariate Vandermonde over $\mathbb{Z}_2$ with exponents bilinear in the row data $(n_i, k_i)$ and the 2-adic parameters $(t, m^*, a^*)$** — the same shape as the original determinant, renormalized to the 2-adic world. Its excess valuation is controlled by quantities of the form $v_2\big(M^{x}3^{y}A^{z} - 1\big)$ with integer exponents bounded by the column weights.

This has two consequences. The pessimistic one: those are exactly the quantities bounded *above* by Yu-type p-adic Baker theory — $v_2(M^x3^yA^z - 1) \ll_{M,A} \log\max(|x|,|y|,|z|)$ — so (heuristically; I flag that the reduction of "excess determinant valuation" to "pairwise/low-rank congruences" is not airtight) the total cancellation available inside one block is $O_\beta(r\log r)$, against a needed excess $\asymp \beta r^3$. If that heuristic survives scrutiny, Priority A is not merely hard within single-block systems — it is *provably capped*, and the node systems must grow in height (multi-block), where the archimedean divided-difference bound can gain from small relative gaps while $\log B$ in Yu's bound grows. The constructive one: the second-level parameters $(t, m^*, a^*)$ are the 2-adic logarithms of $3, M, A$, about which the defining real relation $\log M\log 3 = \log A \log 2$ says *nothing a priori*. So Priority A, pushed to its actual mechanism, demands exactly the real/p-adic logarithm compatibility statement that your Priority D asks about. **Priorities A and D are the same priority.** I'd suggest merging them into one target statement: *find any nontrivial constraint linking the archimedean relation $\log M \log 3 = \log A\log 2$ to the 2-adic (or 3-adic) logarithms of $M, A$* — with the concrete payoff that any such constraint feeds directly into the second-level determinant's valuation.

## 4. A documented dead end, with its exact loss factor

I tried to convert a convergent $p/q$ of $\beta$ into Diophantine pressure on $\theta$, where effective measures exist. Setting $\varepsilon = q\beta - p$, $N_1 = M^q - 2^p = 2^p(2^\varepsilon - 1)$, $N_2 = A^q - 3^p = 3^p(3^\varepsilon-1)$, one gets a rational approximation

$$\Big|\frac{2^p N_2}{3^p N_1} - \theta\Big| \ll |\varepsilon|, \qquad \text{denominator } Q \le 6^p\cdot 2|\varepsilon|\ln 2 .$$

Feeding this into the effective measure $\mu_0$ for $\theta$ gives $|\varepsilon| \gg 6^{-p\,\mu_0/(1+\mu_0)}$. With $\mu_0 \approx 8.62$ (see §5) this is $|\varepsilon| \gg 2^{-2.32 p}$ — strictly *weaker* than the trivial integrality bound $|\varepsilon| \gg 2^{-p}$, and the loss factor $\mu_0/(1+\mu_0)$ can never dip below the trivial bound for any finite $\mu_0$ because the constructed denominator carries the full weight $6^p$. Worth recording so nobody re-walks it: the correlation of the two integer gaps (your failure point 4b) manifests here as denominator inflation, quantitatively.

## 5. A correction, and the true payoff of Wu's measure

In my literature report I suggested Wu's measure $\mu(1,\log 2,\log 3) \le 7.6155$ could yield a *uniform* zero-free criterion replacing your interval certificates. On reflection that was wrong, and I want to flag it plainly: near-integrality of $U^\theta$ is not a rational approximation to $\theta$ — it is the bilinear form $\log 3\log U - \log 2 \log V$, i.e. your wall, and no linear-in-logs measure touches it. The scans stay per-value. What Wu's measure *does* give, immediately and unconditionally: taking $x_0 = 0$, $|q\log 3 - p\log 2| \ge H^{-7.6155}$ yields an effective irrationality measure $\mu_{\mathrm{eff}}(\theta) \le 8.62$, hence

$$q_{n+1} \;\ll\; q_n^{\,7.62}$$

for the convergent denominators of $\theta$ — a polynomial bound replacing your kernel-verified exponential bound $q_{n+1} < 2m^{q_n}$. That is a genuine, citable strengthening of one of your Lean-verified statements (import at the $\textsf{known}$ tier; formalizing Wu's proof itself would be a major computation and I wouldn't attempt it). It also uniformizes anything downstream that consumed the convergent bound. Your finite-difference AP exponent, by contrast, needs nothing: $83/400 = 0.2075 = (2-\theta)/2$ is already at the ideal value.

## 6. Small structural facts, for completeness

Minimality of $\beta$ gives in one line that $2\mid M$ and $3 \mid A$ cannot hold simultaneously ($\beta - 1$ would be a smaller nonintegral solution) — I believe this is your "no matched depth," and note the asymmetric pair ($3\mid M$ and $2\mid A$) is *not* excluded this way, since $\beta - \theta$ leaves the solution monoid. Also $M$ is not a power of $3$ and $A$ not a power of $2$ (either forces $\theta \in \mathbb{Q}$). And Roy's strong six exponentials with rows $(1,\beta)$, columns $(\log 2, \log 3, \log M)$ gives $\beta\log M \notin \mathcal{L}^*$ whenever $M$ is not $3$-smooth, hence $\beta^2 \notin \mathrm{Sol}$ — which I expect your tower/return-kernel modules already contain in stronger form, so treat it as a cross-check.

## 7. What I would do next

The ceiling lemma itself is a good Lean target: it is finite combinatorics (min = mean over $S_{r+1}$, plus the $\sum n_k$ evaluation from your exact block classification) and it *permanently retires* a class of attempts — negative results of that kind are cheap insurance for a formalized program. Mathematically, the fork is now sharp: either (i) prove any real?p-adic logarithm linkage for $(M, A)$ (merged Priority A/D; even a statement conditional on p-adic four-exponentials fragments would clarify the landscape), or (ii) rebuild the determinant over height-growing node systems spanning $\asymp \log X$ blocks, where my ceiling argument no longer applies because the depths no longer equidistribute relative to a common $T$ — the first thing to compute there is the analogue of $\bar\nu/T$.