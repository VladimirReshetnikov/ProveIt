# Independent rotation-counting audit

Date: 2026-10-03. Scope: the fixed-parameter canonical family in the supplied `FULL-SIGNED-COUNTEREXAMPLE.md` and `independent/INDEPENDENT-AUDIT.md`. These two sources were read as inert text. No upstream program was run, and no source repository was edited.

## Results

1. There is at most one admissible positive `n = n0 + Lv` for each progression index `p`; the set of selected `p` has relative density `log(1+1/Y)/(L beta)` within its progression.
2. Equidistribution and vanishing endpoint shifts alone prove that density. A standard algebraic-logarithm lower bound additionally proves that the exact selection differs from a fixed rotation interval at only finitely many progression indices.
3. That fixed interval is **not** a bounded-remainder interval. Hence its discrepancy, and the exact-hit discrepancy, are unbounded. This excludes an all-height two-term formula with bounded remainder, but it does not exclude the weaker discrepancy estimate `o(log N)` needed to identify a triple-log second term.
4. Baker-type bounds plus Erdős–Turán give some effective power-saving `O(N^(1-epsilon))`, with fixed-parameter constants. This is still much larger than `log N` and does not identify the second term.

## 1. Exact interval, uniqueness, and limiting rotation

Write

- `dP = P^2-1`, `S = sqrt(dP)`, `lambda = A+sqrt(Delta)`, `nu = P+S`
- `alpha = log(lambda)`, `beta = log(nu)`, `M = L beta`
- `p_r = p_* + Vr`, `delta = log((Y+1)/Y)`, `ell = delta/M`
- `kappa0 = log(S/(2 sqrt(Delta)))`

The strict quotient condition is equivalent to

`a_p < n beta < b_p`,

where

`a_p = asinh(c S/(2(Y+1)))`, `b_p = asinh(c S/(2Y))`, `c=psi_A(p)`.

The function `F(t)=asinh(e^t)` has derivative `e^t/sqrt(1+e^(2t))` strictly between zero and one. Therefore

`0 < b_p-a_p < log((Y+1)/Y) = delta`.

Here `delta <= log 2`, while `L>=1` and `P>=3` give `M>=beta=arcosh(P)>log 2`. Since values of `n beta`, for `n=n0+Lv`, have spacing `M`, at most one is inside this interval. Both endpoints tend to infinity, so the selected `n` is positive for sufficiently large `p`.

For fixed `t` equal to `Y` or `Y+1`, the Pell formula and the elementary asinh expansion give

`asinh(c S/(2t)) = p alpha + log(S/(2t sqrt(Delta))) + O(exp(-2p alpha))`.

In particular,

`a_p = p alpha + kappa0 - log(Y+1) + O(exp(-2p alpha))`,

`b_p = p alpha + kappa0 - log(Y) + O(exp(-2p alpha))`.

Let

`theta = V alpha/M`,

`xi = (p_* alpha + kappa0 - log(Y+1) - n0 beta)/M`.

The limiting interval contains a point of `n0 beta + M Z` exactly when

`{xi+r theta} in I := (1-ell,1)`.

The two quadratic fields are distinct in the audited construction, so `alpha/beta`, and hence `theta`, is irrational. Irrational-rotation equidistribution gives fixed-interval hit count `ell N+o(N)` for `0<=r<N`. For the moving interval, the indicators can disagree only within arbitrarily small fixed neighborhoods of the two limiting endpoints after a finite initial segment. Equidistribution bounds the upper density of these disagreements by the total length of those neighborhoods. Letting that length tend to zero proves

`C(N) = ell N + o(N)`.

Thus the density among progression terms is `ell=delta/(L beta)`, and the density among all positive integers `p` is `ell/V=delta/(V L beta)`. Deleting a finite initial segment for the other positivity requirements changes neither conclusion.

## 2. Optional strengthening: only finitely many endpoint discrepancies

Use the fixed-positive-algebraic-number form of the logarithmic-form theorem: for fixed positive algebraic numbers `zeta_1,...,zeta_s`, there is an effectively computable `C>0` such that every nonzero real form

`Lambda = b_1 log(zeta_1)+...+b_s log(zeta_s)`

with integer coefficients satisfies

`|Lambda| >= B^(-C)`, `B=max(3,|b_1|,...,|b_s|)`.

This is the fixed-number corollary of Baker–Wüstholz, *Logarithmic forms and group varieties*, J. reine angew. Math. 442 (1993), 19–62, DOI [10.1515/crll.1993.442.19](https://doi.org/10.1515/crll.1993.442.19). An explicit verified statement of precisely the bound used here is Theorem 1.1, equation (1.2), in Yann Bugeaud, [*B′*](https://arxiv.org/pdf/2209.00275), pp. 2–3. No explicit numerical value of `C` is needed.

For `t in {Y,Y+1}`, define

`gamma_t = S/(2t sqrt(Delta))`,

`Lambda_t(p,n) = p alpha - n beta + log(gamma_t)`.

Every `gamma_t` is fixed, positive, and algebraic. Moreover `Lambda_t(p,n)` is never zero for integer `p,n`. Indeed, in the biquadratic compositum `K=Q(sqrt(Delta),S)`, the automorphism fixing `S` and sending `sqrt(Delta)` to its negative sends `lambda` to `lambda^(-1)` and `gamma_t` to `-gamma_t`, while fixing `nu`. If `lambda^p nu^(-n) gamma_t=1`, applying this automorphism would give

`-lambda^(-p) nu^(-n) gamma_t=1`,

whose left side is negative in the chosen real embedding. This is impossible.

If an exact and limiting interval indicator differ, a lattice point `n beta` is within `O(exp(-2p alpha))` of a limiting endpoint. Such an `n` satisfies `n=(alpha/beta)p+O(1)` and so `B=O(p)`. The logarithmic-form theorem instead gives `|Lambda_t(p,n)| >= c p^(-C)`, which eventually exceeds the exponential endpoint displacement. Thus mismatches occur only finitely often. In particular, with

`D(N) = sum_{r=0}^{N-1} 1_I({xi+r theta}) - ell N`,

one has

`C(N) = ell N + D(N) + O(1)`.

After a sufficiently large initial threshold, the difference of the two cumulative counts is actually constant. This strengthening is not an inference from equidistribution alone.

## 3. Bounded-remainder obstruction

The Hecke–Ostrowski–Kesten interval theorem states: for an irrational rotation by `theta`, a circle interval of length `ell` has bounded discrepancy if and only if

`ell in Z theta + Z`.

A primary new proof with this exact statement is Theorem 1 in Kelly and Sadun, [*Pattern equivariant cohomology and theorems of Kesten and Oren*](https://arxiv.org/pdf/1404.0455). The original source is Kesten, [*On a conjecture of Erdös and Szüsz related to uniform distribution mod 1*](https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/12/2/96036/on-a-conjecture-of-erdos-and-szusz-related-to-uniform-distribution-mod-1), Acta Arithmetica 12 (1966), 193–212, DOI 10.4064/aa-12-2-193-212. The theorem applies to any fixed starting phase; endpoint conventions change at most finitely many orbit hits.

In the present notation the criterion is equivalent to

`delta in Z V alpha + Z L beta`.

But any such relation would imply

`(Y+1)/Y = lambda^(aV) nu^(bL)`

for integers `a,b`. The right side is an algebraic unit, since `lambda` and `nu` are roots of the monic integer polynomials `z^2-2Az+1` and `z^2-2Pz+1`. A rational algebraic unit is `+1` or `-1`, whereas the left side is rational and greater than one. Contradiction. Equivalently, the norm from the biquadratic field of the right side is one, and the norm of the left side is `((Y+1)/Y)^4>1`.

Therefore `I` is not bounded remainder, `D(N)` is unbounded, and (using Section 2) the exact-hit discrepancy `C(N)-ell N` is unbounded. This conclusion alone does **not** prove that `D(N)` is not `o(log N)`.

## 4. Optional effective power-saving discrepancy

For every positive integer `h`, let `m` be a nearest integer to `h theta`. The nonzero form

`h V alpha - m L beta`

has integer coefficients of size `O(h)`. Applying the two-logarithm version of the same lower-bound theorem gives effectively computable `c>0` and `mu>=1` with

`||h theta|| >= c h^(-mu)`.

The finite geometric-series formula yields, uniformly in the phase `xi`,

`|sum_{r=0}^{N-1} exp(2 pi i h(xi+r theta))| <= min(N,1/(2||h theta||)) << h^mu`.

The unnormalized Erdős–Turán inequality is

`|D(N)| << N/(K+1) + sum_{h=1}^K (1/h) |sum_{r=0}^{N-1} exp(2 pi i h(xi+r theta))|`.

The primary source is Erdős and Turán, *On a problem in the theory of uniform distribution*, [Part I](https://www.renyi.hu/~p_erdos/1948-02.pdf), Proc. Kon. Ned. Akad. Wetensch. 51 (1948), 1146–1154, with proof in [Part II](https://www.renyi.hu/~p_erdos/1948-03.pdf), 1262–1269. The formula also appears as Lemma 2 in Erdős and Koksma, [*On the uniform distribution modulo 1 of sequences (f(n,theta))*](https://users.renyi.hu/~p_erdos/1949-11.pdf), printed p. 300.

Consequently

`|D(N)| << N/K + sum_{h<=K} h^(mu-1) << N/K+K^mu`.

Taking `K` of order `N^(1/(mu+1))` proves

`D(N)=O(N^(1-1/(mu+1)))`.

The exact count has the same bound after the finite endpoint correction. All constants depend on the fixed construction parameters; no parameter-uniform useful numerical exponent is asserted.

## 5. Precisely what the triple-log second term needs

Suppose the independently checked height analysis supplies

`log log H(p) = 2 alpha p + 2 log p + log(alpha/(2 Delta)) + o(1)`

for the canonical maximum witness height. Put `T=log log H`. Its smooth inverse obeys

`p(H) = T/(2 alpha) - (log T)/alpha + O(1)`.

There are `R(H)=p(H)/V+O(1)` eligible progression indices before this cutoff. Thus Section 2 gives the exact useful decomposition

`N_false(H) = [delta/(2 V L alpha beta)] log log H`

`             - [delta/(V L alpha beta)] log log log H`

`             + D(R(H)) + O(1)`.

This is a discrepancy decomposition, not by itself a two-term asymptotic. A genuine all-height second-term assertion with remainder `o(log log log H)` requires

`D(N)=o(log N)`.

It is sufficient, and because the height cutoff runs through all progression indices it is also the relevant necessary condition for that stated coefficient. An `O(log N)` discrepancy is not enough: it produces an error at exactly the scale of the proposed second term. Equidistribution gives only `o(N)`, and the effective power saving in Section 4 remains much larger than `log N`.

An all-height version with an `O(1)` remainder is impossible, because Kesten gives unbounded discrepancy and the finite exact/rotation correction cannot remove it. This does not disprove a second term with `o(log log log H)` remainder; that would require the stronger `o(log N)` estimate, which has not been established here.
