# Independent audit: A202058 EGF radius

Audit date: 2026-10-01 (UTC).

## Verdict and exact scope

**PASS: no substantive mathematical gap found in the audited draft.** The argument establishes

\[
\operatorname{rad}\left(\sum_{n\ge0}a_n\frac{t^n}{n!}\right)=\frac{3\pi^2}{8},
\qquad
\limsup_{n\to\infty}\left(\frac{a_n}{n!}\right)^{1/n}=\frac{8}{3\pi^2}.
\]

This audit does **not** certify a full normalized-root limit, a coefficient-ratio limit, an asymptotic equivalent, a stretched-exponential correction, or novelty against all subsequent literature. The conclusion follows from the analytic argument, not numerical fitting or the author's finite-check script.

The examined proof is `/workspace/shared/oeis-a202058-research/radius-proof.md`, SHA-256:

`51005a5ccb4c7bbfd0fd94139f6fc61e08ceebfbf307f5e98484e7417755c9c4`.

The examined research map is `/workspace/shared/oeis-a202058-research/research-map.md`, SHA-256:

`a1b7530a2e6c95a44960d11e6d58fef9ff3f49221a443346842bfcfdfb249579`.

Read-only copies of both inputs accompany this audit. The primary paper's Sections 2.1, 2.2, and 2.6 were checked using the local full text. Paper PDF SHA-256: `73515090bb5b933f9d488974f9fe772db6f0493807b87e986e19e7b9a7acc7b4`; text SHA-256: `8755aea189c6b51bd0180efdb82434cd085fa3bcf4deb925a787e5bb3e3f0eb7`.

Primary source: A. R. Conway, M. Conway, A. Elvey Price, A. J. Guttmann, *Pattern-Avoiding Ascent Sequences of Length 3*, Electronic Journal of Combinatorics 29(4), P4.25 (2022), DOI [10.37236/11266](https://doi.org/10.37236/11266).

## 1. The exact recurrence, including why compaction is legitimate

An ascent sequence starts at zero and each next label is between zero and one plus the number of prior ascents. Avoiding 000 is exactly the requirement that each label occur at most twice.

### Deleting twice-used labels

After selecting a previously once-used label `i`, that label is forbidden in every continuation. Delete it from the ordered alphabet. Labels greater than `i` shift down by one; other available labels retain their order. The adjusted ascent parameter decreases by one. The last-label comparison threshold becomes `i-1`: a remaining old label `j` satisfies `j>i` precisely when its new label exceeds `i-1`. Thus the duplicate branch changes `(a,l,S)` to

\[
(a+\mathbf1_{i>l}-1,\ i-1,\ r(S\setminus\{i\},i)).
\]

The value `-1` is a comparison threshold, not an actual selected label, and is legitimate. Deletion preserves all future order comparisons and available-label counts.

### Compacting once-used labels without changing the last threshold

The paper does not need, and this audit does not assume, arbitrary cardinality-only invariance of `S`. The narrower below-last exchange is sufficient.

Suppose `j,j+1` are absent from `T`, with `j<l`, and compare the once-used sets `T∪{j}` and `T∪{j+1}`. In any suffix, reverse each maximal block using only the two labels `j,j+1`, then interchange those two labels in that block. This is an involution. It swaps their total counts, so it interchanges their remaining multiplicity budgets (one versus two). The number of ascents inside each block is unchanged, since reversal followed by complementation maps an ascending binary pair to an ascending binary pair at the mirrored position. Comparisons at block boundaries are unchanged because any external label is either below both or above both. At the beginning of the suffix both labels are at most `l`, so neither makes an ascent from `l`.

There is no hidden prefix-legality problem from the reversal. Both labels are already permitted at the start of any such block: `j+1≤l≤a` initially, and the adjusted ascent parameter cannot decrease within a suffix in which no further alphabet deletion has yet been applied. Prefix ascent counts inside a block may differ, but its two labels are already available. At the end of each block the accumulated ascent count is identical, so the legality of every following external label is preserved. Equivalently, one can apply this bijection to the fixed-alphabet suffix interpretation of the deletion recurrence before subsequent dynamic renaming.

Consequently the two suffix counts agree with `a,l` fixed. If the initial set is `{0,...,s-1}` and a new `i≥s` is selected, the child last threshold is `l'=i`; moving its singleton from `i` down to `s` uses only exchanges with `j<i=l'`. Duplicate deletion directly leaves `{0,...,s-2}`. Hence every recursive state reached from the initial state can be compacted exactly, keeping the adjusted last threshold.

The compacted recurrence is therefore

\[
F_n(a,l,s)=\sum_{i=0}^{s-1}F_{n-1}(a+\mathbf1_{i>l}-1,i-1,s-1)
+\sum_{i=s}^{a+1}F_{n-1}(a+\mathbf1_{i>l},i,s+1),
\]

with `F_0=1` and `a_n=F_{n-1}(0,0,1)` for `n≥1`.

### Translation into the draft's state space

Set `m=a+2`, `k=l+1`, `u=m-s`. Then `i>l` is exactly `i≥k`. The four children are precisely those in the draft:

- Duplicate descent: `(s-1,u,i)`
- Duplicate ascent: `(s-1,u+1,i)`
- New ascent: `(s+1,u,i+1)`
- New descent: `(s+1,u-1,i+1)`

The conditions `s≥0,u≥1,0≤k<s+u` are preserved. In particular new descent requires `s≤i<k≤s+u-1`, implying `u≥2`. Each jump changes `m` by `-1,0,+1,0`, respectively. The initial state is `(1,1,1)`, and `T^n1(x_0)=a_{n+1}`. The positive operator may harmlessly be defined on the entire invariant state space, even if some states are not reached from `x_0`.

## 2. Characteristic and frozen integral

For `q≥0`, the definitions imply

\[
e^{2p}=2e^q-1,\quad R=2-e^{-q},\quad 1\le R<2,\quad
\frac q2\le p\le\frac q2+\frac{\log2}{2},\quad B=RA.
\]

Also `dp/dq=1/R`, so `q'=B/q` and `p'=A/q`. The removable limits at zero are `p'=q'=1`; all needed functions and first derivatives extend continuously there. Since `u≥1`, `D=s+Ru≥R≥1`. The profile `h` is increasing from `0` to `D` on `[0,m]`; consequently every state rank satisfies `0≤r<1`.

Here is an explicit verification of the frozen integral, avoiding reliance on an informal eigenfunction analogy. Put

\[
\phi(y)=e^{-qh(y)/D},\quad z=\phi(k),\quad a=\phi(s),\quad c=e^{-q}.
\]

For `k≤s`, multiplying the proposed integral by `φ(k)` gives

\[
\frac Dq\left[e^{-p}\{1-z+e^q(z-a)\}+\frac{e^p}{R}(a-c)\right].
\]

The identity `e^p/R=e^{-p}e^q` cancels the constant and `a` terms, leaving `(D/q)Az`. Dividing by `z` yields `AD/q=λ`.

For `k≥s`, the corresponding expression is

\[
\frac Dq\left[e^{-p}(1-a)+\frac{e^{p-q}}R(a-z)+\frac{e^p}R(z-c)\right].
\]

Now `e^{p-q}/R=e^{-p}` and `e^pc/R=e^{-p}` cancel the constant and `a` terms; the remainder is `(D/q)(B/R)z=(D/q)Az`. At zero the same identity holds by continuity, with both sides equal to `m`.

On each interval cut out by the integer points `s,k`, the frozen integrand is decreasing. Each of its values is at most `M_0=√2 e^{q/2}`: duplicate ascent uses `q-p≤q/2` and nondecreasing frozen rank; duplicate descent uses `r(k)-r(y)≤1`; new ascent uses `p≤q/2+(log2)/2`; and new descent uses `p-q+q(r(k)-r(y))≤p`. The left Riemann-sum error on each integer-bounded interval is between zero and its initial height, hence at most `M_0`. There are at most three such intervals. Thus the stated `3M_0` bound is valid, including coincident or empty intervals.

## 3. Exact child ranks and the uniform residual

Computing `D` and `h` in each child gives, in the order used above,

\[
\frac{i}{D-1},\qquad
\frac{i}{D+R-1},\qquad
\frac{h(i)+1}{D+1},\qquad
\frac{h(i)+1}{D+1-R}.
\]

Every denominator is strictly positive whenever its branch is available. The first three rank differences from `h(i)/D` have absolute value at most `1/D`. The fourth difference is

\[
\frac{D+(R-1)h(i)}{D(D+1-R)}\ge0.
\]

It is at most `4/D`: its numerator is at most `RD`, and `RD≤4(D+1-R)` follows from `D≥R`, `1≤R≤2` (indeed `(4-R)D-4(R-1)≥4-R²≥0`). This is a uniform analytic bound, with no bounded-state assumption.

Only duplicate ascent can decrease the child rank relative to its frozen rank. In that case `k≤i<s`, so

\[
r(k)-r_i\le\frac{k(R-1)}{D(D+R-1)}
\le\frac{D-2}{D^2}\le\frac18.
\]

The middle inequality uses `k≤s-1≤D-2`, `R-1≤1`, and `D+R-1≥D`; this branch necessarily has `D≥2`. The final bound has maximum at `D=4`. Thus every exact transition ratio is at most `M=√2e^{5q/8}`; all frozen ratios satisfy the same bound. The mean-value inequality for the exponential yields, for each branch, an error at most `4qM/D`, and summing at most `m≤D` branches gives `4qM`.

For the time derivative, direct differentiation yields

\[
\partial_t\log\psi=\lambda-q'[r+qe^{-q}\partial_Rr].
\]

The two formulas for `∂_Rr` are `-ku/D²` when `k≤s`, and `-s(m-k)/D²` when `k≥s`. Both lie in `[-1/(4R),0]`, using `su/(s+Ru)²≤1/(4R)`. Therefore the bracket is at most `r≤1` and at least `-qe^{-q}/(4R)≥-1/(4e)`, so its absolute value is at most one. Also `q'≤√2e^{q/2}`.

Combining the derivative, quadrature, and child-shift errors gives

\[
\left|\partial_t\psi/\psi-T\psi/\psi\right|
\le\sqrt2\{4e^{q/2}+4qe^{5q/8}\}
\le8(1+q)e^{5q/8}=C(q).
\]

The continuous extensions at `q=0` are legitimate; no division by zero is being used there. Since `dE(q(t))/dt=C(q(t))`, the two comparison functions have the stated subsolution and supersolution inequalities.

## 4. Infinite-state comparison: explicit justification

This is the most important part of the audit. A bare formal subsolution comparison for an unbounded positive operator would be insufficient. The draft's later-superbarrier argument repairs exactly that issue and is valid.

### Nonexplosion and the positive series

Construct a continuous-time Markov chain giving each of the `m` children rate one. Its generator is `L=T-mI`. At its `j`th jump the total rate is at most `m(x)+j`, because `m` rises by at most one per jump. Coupling holding times with independent unit exponential variables bounds its jump times below by those of a Yule pure-birth chain with rates `m(x)+j`; that chain is nonexplosive. Hence the present chain has almost surely finitely many jumps on every bounded time interval.

For a fixed labelled `n`-step path and ordered jump times `0<t_1<...<t_n<t`, its probability density is the product of rate-one transitions and the holding-survival factor `exp(-∫_0^t m(X_v)dv)`, including survival from the last jump to `t`. Multiplication by the Feynman–Kac weight cancels this factor exactly. Integration over the time simplex gives `t^n/n!`. Summing nonnegative terms over all finite paths and `n`, justified by Tonelli and nonexplosion, proves

\[
F(t,x)=\mathbb E_x\exp\left(\int_0^t m(X_v)\,dv\right)
\]

with infinity permitted. No pre-existing bounded-operator semigroup theorem is required.

### Finite stopping and the upper inequality

Fix `N≥m(x)` and let `τ_N` be the first exit from `m≤N`. Because upward jumps are at most one, every exit has `m(X_{τ_N})=N+1`. Before and at this stopping time only finitely many states can occur. For a horizon `H`, write `W_v=exp(∫_0^v m(X_w)dw)`. The drift of

\[
W_v g_+(H-v,X_v)
\]

before stopping is `W_v(Tg_+-∂_t g_+)≤0`. Up to `τ_N∧H`, the weight is bounded by `e^{NH}`, and the barrier is bounded on the finite pre-exit-plus-boundary state set and compact time interval. Thus ordinary stopped Dynkin/optional-stopping arguments apply with genuine integrable quantities.

For `H=t`, the no-exit terminal value is `W_t`, since `g_+(0,·)=1`. Dropping the nonnegative exit contribution gives

\[
\mathbb E_x[W_t;\tau_N>t]\le g_+(t,x).
\]

Nonexplosion implies `{τ_N>t}` increases to the whole sample space; monotone convergence proves `F(t,x)≤g_+(t,x)<∞` for `t<T_*`.

### Lower inequality and the boundary at infinity

The same stopped argument applied to `g_-` has the reverse drift sign and gives

\[
g_-(t,x)\le\mathbb E_x[W_t;\tau_N>t]
+\mathbb E_x[W_{\tau_N}g_-(t-\tau_N,X_{\tau_N});\tau_N\le t].
\]

Choose `ε>0` with `t+ε<T_*`. Set

\[
\eta=\min_{0\le v\le t}\min\{p(v+\varepsilon)-p(v),q(v+\varepsilon)-q(v)\}>0,
\]

where `p(v),q(v)` here denote their time parametrizations. Positivity follows from strict increase and continuity on the compact interval. Since `E≥0`, `q≥0`, and every rank lies in `[0,1]`, one obtains the explicit, state-uniform ratio bound

\[
\frac{g_-(v,y)}{g_+(v+\varepsilon,y)}
\le e^{q(t+\varepsilon)}e^{-\eta m(y)}.
\]

Apply the later supersolution process with horizon `H=t+ε`, stopped at `τ_N∧t`, not at the later horizon. Its expectation is at most `g_+(t+ε,x)`. Keeping just the nonnegative exit part shows

\[
\mathbb E_x[W_{\tau_N}g_+(t+\varepsilon-\tau_N,X_{\tau_N});\tau_N\le t]
\le g_+(t+\varepsilon,x).
\]

There is no conditioning error here: the barrier argument is exactly the remaining time `t+ε-τ_N`, and the inequality is the stopped supermartingale inequality on the same exit event. Since exit states have mass `N+1`, the unwanted boundary term is bounded above by

\[
e^{q(t+\varepsilon)}e^{-\eta(N+1)}g_+(t+\varepsilon,x)\longrightarrow0.
\]

Taking `N→∞` therefore proves `g_-(t,x)≤F(t,x)`. This explicit exponentially decaying exit estimate is the needed boundary-at-infinity control; no unproved uniform-integrability assertion is being substituted for it.

## 5. The radius upper bound and extended semigroup identity

For large `q`,

\[
C(q)/b(q)=O((q+q^2)e^{q/8}),
\]

so the draft's bound `E(q)=O((1+q)^3e^{q/8})` is valid (and can be sharpened). In particular `E(q)=o(e^{p(q)})` because `p(q)≥q/2`.

All iterates `T^n` have finite branching at a fixed state. Consequently Tonelli permits both distributing `T^n` over the nonnegative defining series and regrouping the nonnegative double sum:

\[
\sum_{n\ge0}\frac{\delta^n}{n!}T^nF(t,\cdot)(x)
=\sum_{n,j\ge0}\frac{\delta^nt^j}{n!j!}T^{n+j}1(x)
=F(t+\delta,x).
\]

This identity is valid even when either side is infinite; it does not assume a bounded generator or prior finiteness at `t+δ`.

From `(s,1,s)`, choosing the available new label `i=s` gives `(s+1,1,s+1)`. Thus there is a specific path from `x_0` to `x_n=(n+1,1,n+1)` for every `n`, with unit coefficient in `T^n`. At this state `u=1` and `r<1`, so the lower comparison gives

\[
F(t,x_n)\ge e^{(n+1)p-E(q)}.
\]

Keeping just that path separately for every `n` in the preceding identity yields

\[
F(t+\delta,x_0)\ge e^{p-E(q)+\delta e^p}.
\]

For every fixed `δ>0`, the right side diverges as `t↑T_*`, since `E=o(e^p)`. Nonnegative coefficients give monotonicity, hence `F(T_*+δ,x_0)=∞`. Combined with finiteness at every `t<T_*`, this proves radius exactly `T_*`. No assertion about finiteness at `T_*` is needed. Finally `F(t,x_0)=A'(t)` as formal series, and differentiation preserves radius of convergence.

## 6. Exact evaluation of the characteristic time

The substitution `y=√(2e^q-1)` gives exactly

\[
T_*=\int_1^\infty\frac{2\log((y^2+1)/2)}{y^2-1}\,dy.
\]

It is integrable at both endpoints. Integration by parts using `log((y-1)/(y+1))` has vanishing boundary terms: near one the product is `O((y-1)log(y-1))`, and at infinity it is `O(log(y)/y)`. The further substitution `z=(y-1)/(y+1)` gives

\[
T_*=-2\int_0^1\log z\left(\frac1{1-z}+\frac z{1+z^2}\right)dz.
\]

The first term is `2ζ(2)=π²/3`. The second is

\[
2\sum_{j\ge0}\frac{(-1)^j}{(2j+2)^2}
=\frac12\eta(2)=\frac{\pi^2}{24}.
\]

The series interchange for the alternating term is justified by the finite sum of absolute integrals `∑_{j≥0}1/(2j+2)²`; the first term is also absolutely integrable. The sum is `3π²/8`.

## Suggested exposition improvements, not blockers

1. Include the short compaction-bijection justification or explicitly stress that only below-last adjacent exchanges are used, rather than arbitrary cardinality invariance.
2. In the infinite-state section, write the stopped process `W_v g_±(H-v,X_v)` and specify the finite boundary set `m≤N+1`. This makes signs and integrability transparent.
3. Give the explicit constant `C_{t,ε}=exp(q(t+ε))` and display the later-horizon stopping inequality. The existing text is correct but compressed at the most delicate point.
4. Spell out the `q=0` continuous extensions and the nonnegative double-series derivation of the semigroup identity.
5. Preserve the draft's precise radius/limsup limitation in any abstract, announcement, or downstream use. This audit supplies no full-root-limit upgrade.

## Audit method and limitations

The audit independently derived the recurrence translation, source compaction mechanism, frozen integral, child-rank and residual estimates, stopped Feynman–Kac comparisons, deterministic-prefix bound, and exact integral. The author's verification script was inspected but was not run or used as proof. No author file was modified. The companion manifest records the SHA-256 hashes at the start and end of the audit and the exact certified scope.
