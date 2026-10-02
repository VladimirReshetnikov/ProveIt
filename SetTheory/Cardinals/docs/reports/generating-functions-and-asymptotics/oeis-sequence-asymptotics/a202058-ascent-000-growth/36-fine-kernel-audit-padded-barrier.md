# Independent audit: padded quadratic-logarithm barriers

2 October 2026. Scope: `../padded-barrier-proof.md`, together with the already-frozen exact operator and infinite-state comparison framework. No frozen source was modified.

## Verdict

**The new proof is valid.** It proves the one-sided coefficient estimate

\[
\log\frac{a_n}{n!\mu^n}\le C(\log(n+2))^2,\qquad \mu=8/(3\pi^2),
\]

and uniformly for every state x at each fixed q,

\[
-2q^2-q\le \log F(t(q),x)-\log\psi(q,x)
 \le H(q)+\lceil q\rceil p(q)+q=O(q^2+q).
\]

The last uniform estimate follows from the padded upper inequality because
\(\log\psi(q,I_Lx)-\log\psi(q,x)=Lp(q)-q(r(I_Lx)-r(x))\le Lp(q)+q\).
The constants are independent of x. Neither statement provides an individual-coefficient lower bound of quadratic-logarithm order, a leading quadratic-logarithm coefficient, or an asymptotic equivalent.

## Analytic checks

1. **Signed Riemann estimate.** The breakpoints s and k are integers. Every summand is the left endpoint of a unit interval on which the frozen g is decreasing, including when a unit interval ends at a breakpoint. Thus S≥λ. The previous absolute error estimate supplies S−λ≤3√2 exp(q/2). There is no unsupported reversal of the signed inequality.

2. **One-sided shifts.** Every child except a duplicate ascent has r_child≥r_frozen. A duplicate ascent has difference r_frozen−r_child=i(R−1)/[D(D+R−1)]≤1/D. This proves the claimed upper factor exp(q/D). The existing absolute shift bound gives the lower factor exp(−4q/D).

3. **Residual normalization.** λ/b=D/R. Using 1−exp(−z)≤z proves the lower residual ≤4q+1. Using exp(z)−1≤z exp(z), R≥1, and exp(q/2)/b≤q+1 proves the upper residual (U). The latter auxiliary bound follows from q/(1−exp(−q))≤q+1, itself equivalent to exp(q)≥1+q; all zero-parameter expressions have continuous limits.

4. **Padding intertwining.** Under I_L(s,u,k)=(s+L,u,k+L), each comparison i<s and i<k is unchanged after replacing i by i+L. Each of the four resulting child triples is exactly I_L applied to the original child. The unused indices 0,…,L−1 contribute nonnegative additional terms. Hence T(f∘I_L)≤(Tf)∘I_L for nonnegative f. This is an inequality, not an operator-commutation claim.

5. **Supersolution and boundary condition.** For fixed Q, choose fixed L=ceil(Q). The differential inequality holds throughout q∈[0,Q], since D(I_Lx)≥L+1>Q. The displayed H′ exceeds the right side of (U) with exp(q/D)≤e. Multiplication by exp(H) and the padding inequality give a global supersolution with initial value 1, including all small original states.

6. **Infinite-state comparison.** The previous killed-chain argument applies to this nonnegative C¹ supersolution. For the lower comparison choose a later time and a single fixed padding size valid through that time. The ratio of the unpadded lower function at v to the padded upper function at v+ε is at most

   C exp(−[p(v+ε)−p(v)]s−[q(v+ε)−q(v)]u),

   uniformly on a compact time interval. Rank terms have absolute size bounded by the maximum q, and L is fixed. Both positive increments have positive compact minima. The required exponentially small exit contribution therefore vanishes exactly as in the frozen comparison proof.

7. **Coefficient extraction.** A(t)≤1+tF(t,x0) and a_n/n!≤A(t)t^(−n) use only coefficient positivity. Q=2log(n+2) has n(T−t(Q))=O(log n); t(Q) stays bounded away from zero for large n. Hence n log(T/t(Q))=O(log n), completing the claimed upper bound.

## Reproduction and caution

`verify_padded_barrier.py` independently checks all four transition cases, padding, signed Riemann errors, and both weighted residual inequalities on a finite grid. Its output is in `verification.json`. These computations corroborate the analytic proof but do not replace it.

The sign of the coefficient statement is important: it excludes a positive stretched exponential exp(c n^σ), c>0, but does not exclude a negative one. Uniform function bounds alone do not justify a coefficientwise transfer or normalized log-concavity.

## Supplement: improved coarse lower bound and inverse

The separate `../improved-coarse-lower.md` was independently checked and is valid. Uniform O(q²) function errors give the stated improved Chernoff estimate. With N=ceil(K n^(2/3)(log n)^(2/3)), ε=2N/n and sufficiently large fixed K, Nε² dominates the quadratic error; solving NM(q)=(1−4ε)n gives the stated q expansion. The central interval leaves a margin of more than N steps, and the factorial-extension loss is O(N log n). This proves the coefficient lower bound −O(n^(2/3)(log n)^(5/3)). Differentiating x log(x/(eT)) shows the two displayed one-sided inverse errors follow from the two coefficient errors, with integer rounding absorbed. Neither lower exponent nor inverse displacement is asserted to be sharp.
