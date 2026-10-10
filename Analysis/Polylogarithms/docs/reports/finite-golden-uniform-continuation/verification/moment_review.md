# Independent review of the joint reflected-moment transition

Reviewer: depth/Gaussian subtask. Source reviewed: `research/moment_notes.md`, against the fixed-m definitions in `sources/manuscript/chapters/07-reflected-moments.tex` at commit `28357e8ca63dd78327db91d9be239d75e4462879`.

## Conclusion

I found no error in the transition constant, the explicit first correction, the mode-centered Gamma moments, or the exact residue-polynomial identities. The weighted-tail localization is sound: the potentially large factor at the left endpoint is dominated by a substantially stronger Gamma large-deviation penalty. The proof needs its existing four-region split; a statement that ordinary Gamma concentration alone handles the whole weighted integral would not suffice.

The all-fixed-orders claim is also justified by the displayed local analytic expansion and exact cumulants. It should remain an asymptotic expansion with a remainder uniform for fixed strip width and fixed order, not a convergent infinite expansion.

## Detailed analytic checks

Write `r=m+1`, `n=rt`, `lambda=m exp(-t)`, and let `p(y)` be the Gamma density with shape `n+1` and rate `r`. Its mode is exactly `t`; its mean is `t+1/r`. The distinction matters at the order claimed.

For `x<=1/2`,

`B(x)/(gamma x) = 1 + sum_(k>=2) zeta(k)x^(k-1)/(k gamma)
 <= 1 + zeta(2)x/[2 gamma(1-x)] <= 1 + C x`,

where `C=zeta(2)/gamma`. Since `ell(x)<=0`, this proves the proposed weight bound `exp(E_m(y)) <= exp(Cm exp(-y))` for `y>=log 2`.

1. **The endpoint `0<y<log 2`.** Substitution back to `x` bounds its unnormalized contribution by `(log 2)^n m!`. The logarithm of its ratio to the leading scale is

   `-n log t + n(1+log log 2) + m log m + O(m+log n+log r)`.

   In the transition strip, `m log m=O(n)`. Hence this is at most `-(n/2)log t` for all sufficiently large `m`, uniformly in the strip. It is far smaller than `exp(-c m/t)`.

2. **The region `log 2 <= y <= t/2`.** The weight is at most `exp(Cm/2)`. The Gamma lower tail at half the mode is `exp(-c0 n)` for an absolute positive `c0` once `n` is large. Because `n/m=t~log m`, the product is bounded by `exp(-c1 m t)`.

3. **The region `t/2 <= y <= t-1`.** Put `u=t-y`. The exact density ratio is

   `p(t-u)/p(t) = exp(n log(1-u/t)+ru) <= exp(-r u^2/(2t))`.

   On `1<=u<=t/2`, the maximum of `exp(u)/u^2` is attained at an endpoint. The two endpoint comparisons are

   `4 C lambda t exp(1)/r -> 0`,

   and

   `16 C lambda exp(t/2)/(r t) -> 0`.

   Thus for all sufficiently large `m`, uniformly in the strip, the weight costs at most half the displayed Gaussian penalty. Since `p(t)=O(sqrt(r/t))`, direct integration gives an upper bound polynomial in `m,t` times `exp(-r/(4t))`, which is `O(exp(-c m/t))` after decreasing the positive constant `c`.

4. **The region `y>=t+1`.** Its weight is bounded by `exp(C lambda/e)`. Gamma Chernoff bounds, for a displacement of one from the mode and `t->infinity`, give probability `O(exp(-c r/t))`. Thus this tail has the same required bound.

The same unweighted arguments with any fixed polynomial factor in `|y-t|` justify replacing truncated signed moments by the full moments. The upper tail with such factors is controlled either by the Gamma density ratio or by a slight reduction of the Chernoff parameter.

## First-correction algebra

I independently recomputed the mode-centered moments from the cumulants of the Gamma law:

- `EV=1/r`;
- `EV^2=t/r+2/r^2`;
- `EV^3=5t/r^2+6/r^3`;
- `EV^4=3t^2/r^2+26t/r^3+24/r^4`.

Writing `a=-gamma`, `a2=zeta(2)/2`, `b=zeta(2)/(2gamma)`, `c=a+b`, and `d=zeta(3)/(3gamma)-zeta(2)^2/(8gamma^2)`, the proposed local expansion is correct:

`A(v)=lambda exp(-v)[b+a t/(t+v)]`,

`B1(v)=a lambda exp(-v)t/(t+v)
       +lambda^2 exp(-2v)[d+a2 t/(t+v)-a^2 t/(2(t+v)^2)]`.

Its contribution at order `1/m` is

`B1(0)+A'(0)+(t/2)(A''(0)+A'(0)^2)`

`=lambda[c(t/2-1)+2a]
  +lambda^2[c^2 t/2+ca+d+a2]`.

The identity `ca+a2=gamma^2` gives exactly the claimed

`C1=lambda[c(t/2-1)-2gamma]
    +lambda^2[c^2 t/2+gamma^2+d]`.

In particular, the inverse powers of `t` cancel; no shift from mode to mean has been lost. The retained cubic Taylor term is `O(t/m^2)` and the fourth-order remainder is `O(t^2/m^2)`. The linear Taylor term for `exp(A)B1/m` is `O(1/m^2)`, while its quadratic remainder is `O(t/m^2)`. These all fit the stated error.

## Higher-order algorithm

At formal order `epsilon^j`, the cumulant operator contains finitely many derivatives: the coefficient of `epsilon^k` in `K_epsilon(z)` has degree at most `k+1`, and `exp(K_epsilon)` has differential order at most `2j` at order `j`. Derivatives of the local analytic amplitudes at fixed orders stay uniformly bounded for `|v|<=1`, because `t/(t+v)` and its fixed derivatives are bounded once `t>=2` and `lambda` stays in a compact positive interval.

The moments satisfy `E|V|^(2J+2)=O_J((t/m)^(J+1))`, as follows by the finite moment-cumulant formula and the exact Gamma cumulants. Taylor expansion through degree `2J+1` therefore supplies the desired error. Evaluating all derivatives at `v=0` makes each coefficient an exponential `exp(c lambda)` times a polynomial in `lambda` with rational functions of `t`; division by the exponential gives the claimed `C_j` class. The largest positive power of `t` is at most `j`.

## Exact residue polynomial checks

The manuscript uses `A_(k,m)=(1/k)[x^(k-1)]Gamma(1+x)^k B(x)^m`. Substitution `k=m+j+1` gives precisely

`(m+j+1)gamma^(-m) A_(m+j+1,m)
 =[x^j]Gamma(1+x)^(j+1) H(x)^m`,

`H(x)=Gamma(1+x)B(x)/(gamma x)`.

The claimed `P1` and `P2` follow from the first two logarithmic coefficients. For the generating identity, Lagrange inversion gives

`g'(w)B(g(w))^m = sum_(k>=1) k A_(k,m) w^(k-1)`.

Division by `gamma^m w^m` proves the displayed `P_j` generating function, including its derivative and index shifts. A fixed residue term has normalized contribution

`P_j(m) ((m+1)/(m+j+1))^(n+1)`.

For fixed `j`, this tends to `(c lambda)^j/j!` along a strip sequence with a limiting `lambda`. More precisely, its difference from that expression is `O_(j,S)(t/m)` times a bounded quantity. This is an explanation of the exponential factor; the proof correctly does not interchange the divergent infinite pole expansion with the joint limit.

## Recommended wording refinements

- Establish `log Gamma(x)>0` on `(0,1)` explicitly using `psi'(x)>0` and `psi(1)=-gamma<0`, or cite this familiar monotonicity fact. Log-convexity between `1` and `2` directly proves the upper bound `log Gamma(x)<=-log x`, while positivity uses the additional monotonicity fact.
- State that the strip hypotheses force `n>0` and `t>=2` for all sufficiently large `m`, even though the family is originally defined for `n>=0`.
- For fixed-residue limits, either assume `lambda` converges or write an asymptotic comparison to `(c lambda)^j/j!` with the moving `lambda`; an unqualified numerical limit should not have a variable on its right side.
- Keep numerical quadrature explicitly diagnostic, as currently stated.
