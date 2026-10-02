# Independent audit: universal-sink last coefficient inequality

## Verdict

**PASS.** The proposed inequality

\[
\gamma_{r-1}^2\geq \frac{2r}{r-1}\gamma_{r-2}\gamma_r
\]

is valid for every loopless directed core on `r >= 4` physical vertices with independent universal sinks and arbitrary nonnegative, independent tail/head activities. The coefficients count each feasible ordered disjoint endpoint pair once, not matching witnesses. There is a strictly stronger sharp inequality, stated and proved below.

The original proposition, support formula, six-term decomposition, normalization, zero-activity limits, and degree qualification were checked independently. The producer's current note is `../weighted-degree-four-boundary/UNIVERSAL_SINK_LAST_GAP.md`. This audit code imports no producer code.

## Setup and direct enumeration

Let `C` be the core; let `W` be independent sinks with all arcs `C -> W` and no arcs out of `W`. Internal core arcs are arbitrary, including opposite arcs, but there are no loops. Write `x_i` for core-tail activities, `y_i` for core-head activities, and `w_a` for sink-head activities. Sink-tail activities have no effect.

For every disjoint ordered pair `(U,V)` of physical vertex subsets of equal size, include the monomial `x_U y_(V cap C) w_(V cap W)` exactly when a directed perfect matching from `U` onto `V` exists. All feasible tails lie in `C`. Set `Gamma(z) = sum gamma_k z^k`.

Write

- `p = product_i x_i`
- `A = e_(r-1)(x)`
- `B = e_(r-2)(x)`
- `E_j = e_j(w)`, with `E_0=1` and `E_j=0` beyond the number of sinks

Let `a_j` indicate that core head `j` has positive *combinatorial* indegree. This indicator does not depend on activity values. For `i != j`, let `a_(j;i)` indicate that `j` has an in-neighbor in `C \ {i,j}`. Let `h_ij` indicate the existence of two distinct tails in `C \ {i,j}` that can match to `{i,j}`. Define

\[
\begin{aligned}
d&=\sum_j a_j y_j x_{C\setminus\{j\}},\\
c&=\sum_{i<j}x_{C\setminus\{i,j\}}
       (a_{i;j}y_i+a_{j;i}y_j),\\
b&=\sum_{i<j}h_{ij}y_iy_jx_{C\setminus\{i,j\}}.
\end{aligned}
\]

Then

\[
\boxed{\begin{aligned}
\gamma_r&=pE_r,\\
\gamma_{r-1}&=AE_{r-1}+dE_{r-2},\\
\gamma_{r-2}&=BE_{r-2}+cE_{r-3}+bE_{r-4}.
\end{aligned}}
\]

A size-`k` support has `k` core tails and at most `r-k` core heads. Cover the zero, one, or two selected core heads first; all remaining selected tails can be matched bijectively to the selected universal sinks. The indicator `h_ij` is Boolean. This prevents overcounting when multiple injections cover a selected pair of core heads.

## Independent verification of the three core inequalities

Newton's inequality in exactly `r` variables gives

\[
A^2\geq \frac{2r}{r-1}pB.
\]

The other inequalities are coefficientwise:

\[
Ad\geq pc,\qquad d^2\geq 2pb.
\]

A division-free proof of the first is especially useful at zero activities. For each summand `y_j x_(C\{i,j})` in `c`, the indicator `a_(j;i)=1` implies `a_j=1`. The product of the `x_(C\{i})` summand of `A` and the `y_j x_(C\{j})` summand of `d` is exactly `p y_j x_(C\{i,j})`. These are distinct ordered choices of omitted core vertex and core head, so every contribution to `pc` is supplied once by `Ad`.

For the second, `h_ij=1` implies `a_i=a_j=1`. The two ordered cross terms of `d^2` supply exactly

\[
2y_iy_jx_{C\setminus\{i\}}x_{C\setminus\{j\}}
 =2py_iy_jx_{C\setminus\{i,j\}}.
\]

All remaining terms are nonnegative. No inverse activity or continuity argument is needed for these two comparisons.

## Sharp finite-sink strengthening

Let `m >= r` be the number of strictly positive sink-head activities. Then

\[
\boxed{\gamma_{r-1}^2\geq K(r,m)\gamma_{r-2}\gamma_r,
\qquad K(r,m)=\frac{2r^2(m-r+2)}{(r-1)^2(m-r+1)}.}
\]

The weaker version obtained by using the total number of sinks instead of the number with positive activity also holds.

If `p=0`, then `gamma_r=0` and the result is immediate. Otherwise all core-tail activities are positive. For `m >= r`, all sink elementary symmetric functions used in denominators below are positive. Newton's binomial-normalized log-concavity gives

\[
\begin{aligned}
\frac{E_{r-1}^2}{E_{r-2}E_r}
 &\geq \frac{r(m-r+2)}{(r-1)(m-r+1)}=:L_0,\\
\frac{E_{r-1}E_{r-2}}{E_{r-3}E_r}
 &\geq \frac{r(m-r+3)}{(r-2)(m-r+1)}=:L_1,\\
\frac{E_{r-2}^2}{E_{r-4}E_r}
 &\geq \frac{r(r-1)(m-r+4)(m-r+3)}
 {(r-2)(r-3)(m-r+2)(m-r+1)}=:L_2.
\end{aligned}
\]

Since `K=(2r/(r-1))L_0`, the pure term satisfies

\[
A^2E_{r-1}^2\geq KpBE_{r-2}E_r.
\]

The mixed and square terms satisfy

\[
2AdE_{r-1}E_{r-2}\geq 2L_1pcE_{r-3}E_r,
\qquad d^2E_{r-2}^2\geq 2L_2pbE_{r-4}E_r.
\]

Both `2L_1` and `2L_2` are strictly greater than `K`. To check the constants without asymptotics, put `t=m-r+1 > 0`. Then

\[
\frac{2L_1}{K}=\frac{(r-1)^2}{r(r-2)}\frac{t+2}{t+1}>1,
\]

because `(r-1)^2-r(r-2)=1`, and

\[
\frac{2L_2}{K}=\frac{(r-1)^3}{r(r-2)(r-3)}
                 \frac{(t+3)(t+2)}{(t+1)^2}>1,
\]

because `(r-1)^3-r(r-2)(r-3)=2r^2-3r-1>0` for `r>=4`. Adding the three termwise comparisons proves the stronger inequality.

### Sharpness and equality

For an edgeless core, equal positive core-tail activities, and `m` equal positive sink-head activities, `d=c=b=0` and

\[
\gamma_k={r\choose k}{m\choose k}(xw)^k.
\]

Consequently `gamma_(r-1)^2/(gamma_(r-2) gamma_r)=K(r,m)` exactly. Thus `K(r,m)` is the best possible class-wide constant for fixed `r,m`.

More generally, when `gamma_r>0`, equality in the sharp bound holds exactly when all core-tail activities are equal, all positive sink-head activities are equal, and `d=0`. Indeed the two mixed/square comparison constants are strictly larger, while Newton equality for positive variables forces the stated uniformity. The condition `d=0` means every core head of positive indegree has zero head activity; all internal arcs then contribute zero support weight. This includes an edgeless core with arbitrary core-head activities.

Uniformly over an arbitrary number of sinks, the sharp constant is

\[
\frac{2r^2}{(r-1)^2}.
\]

The finite-`m` constants decrease to it as `m` tends to infinity; the edgeless equal-activity examples show it cannot be improved uniformly. For finite `m` and `gamma_r>0`, the uniform bound is strict.

## Degree, normalization, and zero weights

There are at most `r` possible tails, so `deg Gamma <= r`. Moreover `gamma_r=pE_r>0` precisely when all `r` core-tail activities are positive and at least `r` sink-head activities are positive. In that case the actual degree is `r`, and the ordinary last degree-`r` ULC/Newton comparison is

\[
\gamma_{r-1}^2\geq \frac{2r}{r-1}\gamma_{r-2}\gamma_r.
\]

The sharper result is therefore stronger than the required last ULC inequality. If `gamma_r=0`, the proposed `r`-indexed inequality is merely trivial. It does **not** by itself prove the last inequality at the smaller actual degree. No middle gap, full ULC assertion, stability assertion, or novelty/priority claim follows from this audit.

Zero core-tail/head activities and zero sink-head activities are allowed. The formulas and core inequalities are polynomial; the only divisions in the sharp proof are made after isolating the strictly positive-top case. If fewer than `r` positive sink-head activities remain, `gamma_r=0` and the original comparison remains immediate.

## Classical input and source

The only classical input is Newton's inequality for elementary symmetric functions, including its binomial normalization. As a modern primary reference, Branden and Huh, *Lorentzian polynomials*, Annals of Mathematics 192 (2020), 821–891, Proposition 2.2 and Example 2.26, supply this normalization via the stable bivariate product of linear factors. The primary paper was independently opened during this audit:

https://annals.math.princeton.edu/wp-content/uploads/annals-v192-n3-p04-s.pdf

The graph-support reduction and coefficientwise comparisons above are proved directly and do not use a matching-witness enumerator.

## Reproducible computational check

Run `python audit.py`. The checker:

1. Enumerates literal disjoint endpoint pairs and tests Hall's condition on every nonempty subset of the tail set
2. Sums each feasible pair once with exact integer activities
3. Independently constructs the proposed three top coefficients, using explicit two-tail injections for the two-core-head indicator
4. Compares the formulas, all three core inequalities, the needed sink-product bounds, the original last-gap bound, and the sharp finite-positive-sink bound
5. Exhausts all 4096 loopless labeled four-core digraphs, uses multiple positive/zero activity assignments, samples ranks through 8, and varies the number of sinks above and below the core size

See `receipt.json` for the final exact scope and counts. These finite checks corroborate the proof; they do not replace it.
