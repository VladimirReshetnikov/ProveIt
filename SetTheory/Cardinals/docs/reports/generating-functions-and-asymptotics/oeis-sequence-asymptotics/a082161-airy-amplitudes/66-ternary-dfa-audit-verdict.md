# Independent audit of the ternary DFA amplitude transfer

Date: 2 October 2026. Scope: the transfer in `dfa-ratio-transfer.md`, taking the independently audited relaxed tracking estimates as a premise. I did not edit the proof documents or publish anything.

## Verdict

**The transfer is valid.** It proves existence of

\[
\rho_\infty=\lim_{n\to\infty}\frac{B_n}{2^{n-1}R_n}\in[P_3,1],
\qquad P_3=\frac{2\sqrt2}{\pi}\sin\frac{\pi}{\sqrt2}>0,
\]

and hence the claimed finite positive ternary DFA amplitude, conditional only on the already approved relaxed tracking theorem and the stated completed-run model. There is no remaining gap in replacing finitely many level defects by a fixed-time prefix perturbation. The repaired high-path bound is sufficient and does not rely on the false assertion that every up weight is at most 2.

The main clarifications worth retaining in a final proof are: define the altered vector explicitly at the cutoff time; restrict bridge terminal times to `T=3n`; and write the denominator comparison in the direction `d_T(0) >= d_(3x)(0) p(3x,0;T)`. These are explanatory additions, not corrections to the conclusion.

This audit does **not** independently recertify the analytic singular-form and quasimode estimates behind relaxed tracking, establish an all-orders DFA expansion, evaluate the amplitude numerically, or establish novelty relative to later literature.

## 1. Inputs and exact normalization

The audited snapshots have SHA-256 hashes:

- `dfa-ratio-transfer.md`: `d70d4a0dadbe323234b027434d094b5021a2a5d40b1141f3140091bdcb9c22d7`
- `repaired-high-path-tail.md`: `53a664a2fa87b3ce0f6f86e561e0d11d082af4fae57ffc816925563781ef0c64`
- `amplitude-proof-candidate.md`: `18cdbc4ef9215673871f6196a18c5886ada435c0a995f6a808b44c82a28d783b`
- `independent-gap-audit/leading-amplitude-verdict.md`: `6aed66c2816f1576e3e410db54d224d835d78865b8d40447fe3b0990af42075e`
- `../larger-alphabet-automata-research/proof.md`: `64f44bda63ce949994a259216002a51bce4190132c5a21eec69666509055f90a`

I also opened the [primary arXiv version](https://arxiv.org/html/2404.08415v1). Its equations (3)–(5) confirm the transformed recurrence and endpoint conversion, and Section 3.4 contains the bridge comparison and the erroneous critical domination in its Lemma 14 proof. The argument below proves the needed replacement directly; it does not infer an amplitude theorem from the published statement.

Write original path coordinates as `(h,m)`, with `h>=2m`, and transformed coordinates as

\[
i=h+m,\qquad j=h-2m,\qquad
h=(2i+j)/3,\quad m=(i-j)/3.
\]

The gauge is

\[
d_i(j)=\frac{4^h}{h!}r_{h,m}.
\]

A horizontal step has original weight `m+1`; after this gauge its weight is `4(m+1)/h=U(i,j)`. A vertical step preserves `h` and has weight 1 in both models. The gauge therefore multiplies **each individual path** to a fixed endpoint by the same endpoint factor, rather than merely relating the sums. Thus the original relaxed bridge law and the transformed weighted bridge law are identical on path shapes. At `(2n,n)`, the factor is `16^n/(2n)!`, giving the stated conversion.

## 2. Completed-run factors and the factor 2^(n−1)

At vertical level `m>=1`, a completed horizontal run of length `ell` has relaxed weight `(m+1)^ell` and DFA weight

\[
W_m(\ell)=2(m+1)^\ell
\left(1-\frac{\mathbf1_{\{\ell\ge3\}}}{2(m+1)^2}\right).
\]

There are precisely `n−1` such completed runs before the rises `m -> m+1`, for `m=1,...,n−1`. The initial arrival at level 1 has weight 1 in the completed-run model, so it supplies no additional factor 2. The terminal point lies on `h=2m`; consequently the final step is a rise and there is no trailing horizontal run at level `n`. The last of the `n−1` factors includes the rise from `n−1` to `n`.

The first-row convention in the supplied comparison proof is material: `A(h,1)=1` for `h>=2` corresponds to `b_(−1,0)=1` in the signed recurrence and gives `B_1=1`. With this convention the expectation identity and the factor `2^(n−1)` are exact.

Retaining factors only for `m<M` omits indices `j=m+1>=M+1`. Every factor lies in `[0,1]`, so pointwise

\[
0\le F^{[M]}-F\le\frac12\sum_{j>M}j^{-2}\le\frac1{2M}.
\]

This remains true when `n<=M`, in which case no factor is omitted. The same bound therefore holds for the normalized expectations, uniformly in `n`.

## 3. Fixed-time prefix reweighting really is covered by tracking

For fixed integers `M,L`, define `H_(M,L)` on a prefix through time `L` as the product of the factors whose run-terminating rise both has source level `m<M` and occurs at time at most `L`. A run unfinished at time `L` contributes nothing, even if its current length is already at least 3. This is exactly the truncation in the transfer note.

For large enough `n` that `3n>L`, put

\[
v_L(j)=\sum_{P:(0,0)\to(L,j)}w_d(P)H_{M,L}(P),
\qquad j\in J_L.
\]

This is a fixed finite vector, independent of `n`, and `0<=v_L(j)<=d_L(j)`. All weights after `L` are unaltered, so the reweighted endpoint count is exactly

\[
(T_{3n}\cdots T_{L+1}v_L)(0).
\]

The histories that enter `v_L(j)` can be aggregated: no factor will be applied after `L`, so neither a current run length nor a vertical-level memory variable has to be carried into the later evolution. The usual physical coordinate already determines the level at time `L`.

Section 5 of the candidate starts from an arbitrary finite vector at a fixed sufficiently large time and uses linear estimates; positivity of the vector is not required. If `L` is too small to start those estimates, evolve it to one fixed larger starting time. Thus the reweighted endpoint, divided by

\[
S_n=27^n\exp(3\,3^{1/3}a_1n^{1/3})n^{13/6},
\]

has a finite limit. The reference endpoint has a strictly positive limit on this scale by the approved relaxed theorem. Dividing proves convergence of `rho_n^[M,L]`.

The altered-prefix amplitude may be zero; this does not impair this argument. Uniformity of the tracking constants over a family with growing `L` is also unnecessary, because convergence is used separately for each fixed `L`. The uniform approximation needed to pass to the limit is supplied by the path tail, not by tracking.

## 4. Repair of critical domination

For every active up destination `j>=1`,

\[
U(i,j)\le U(i,1)
=2\left(1+\frac3{2i+1}\right)
\le2\left(1+\frac3{2i}\right).
\]

The first up weight is actually `U(1,1)=4`, so the printed domination by 2 cannot be used. For a path of length `t`, however,

\[
w_d(P)\le 2^{N_+(P)}\prod_{i=1}^t\left(1+\frac3{2i}\right)
\le C t^{3/2}2^{N_+(P)}.
\]

Extending the product from the actual up times to every time is allowed because each added factor exceeds 1. A path to `(3x,3y)` has `2x+y` up steps and `x−y` down steps. Ignoring the nonnegativity restriction gives exactly

\[
d_{3x}(3y)\le Cx^{3/2}2^{2x+y}\binom{3x}{x-y},
\qquad 0\le y\le x.
\]

Thus (T1), including its exponent `3/2`, is correct.

## 5. Backward normalized bridge monotonicity

Fix a legitimate terminal time `T=3n`. On the physical spaces `J_r={s:0<=s<=r, s=r mod 3}`, let `p_r(s)` be the total continuation weight to `(T,0)` and set `u_r(s)=p_r(s)/(s+1)`. The backward recurrence is

\[
u_r(s)=A_r(s)u_{r+1}(s+1)+B_r(s)u_{r+1}(s-2),
\]

with negative-height terms omitted and

\[
A_r(s)=\frac{4(r-s+3)(s+2)}{(2r+s+3)(s+1)},
\qquad B_r(s)=\frac{(s-1)_+}{s+1}.
\]

Both coefficients are nonnegative on the physical interval. For `s>=1`, their sum equals

\[
V_r(s)=3-6\frac{s-1}{s+1}\frac{s+2}{2r+s+3}.
\]

The two displayed fractions are nonnegative and increasing in `s` at fixed `r`; their derivatives are respectively `2/(s+1)^2` and `(2r+1)/(2r+s+3)^2`. Therefore `V_r` is nonincreasing. At the remaining bottom point,

\[
V_r(0)=A_r(0)=\frac{8(r+3)}{2r+3}>4>3=V_r(1).
\]

Suppose `u_(r+1)` is nonnegative and nonincreasing along its physical residue. Adjacent starts `s,s+3` have respective supports `{s−2,s+1}` and `{s+1,s+4}`, with negative terms absent. If `c=u_(r+1)(s+1)`, then

\[
u_r(s)\ge V_r(s)c\ge V_r(s+3)c\ge u_r(s+3).
\]

This also handles the bottom cases `s=0,1`: their only nonzero coefficient is the one at the common point. There is no missing upper-boundary issue: if both starts `s,s+3` belong to `J_r`, then `s+4<=r+1`, so both upper destinations are physical. The terminal sequence is 1 at 0 and 0 at all larger physical coordinates, establishing the induction.

In particular,

\[
p_{3x}(3y)\le(3y+1)p_{3x}(0).
\]

For `x<=n`, bridge mass factors as `d_(3x)(3y)p_(3x)(3y)/d_T(0)`. Nonnegativity and the paths passing through height 0 give

\[
d_T(0)\ge d_{3x}(0)p_{3x}(0),
\]

and hence

\[
\mathbb P_T(H_{3x}=3y)
\le(3y+1)\frac{d_{3x}(3y)}{d_{3x}(0)}.
\]

This proves (T2) without any questionable division by a visiting probability. If a continuation factor vanished, the same nonnegative inequality would still be valid.

## 6. Uniform tail and endpoint-time indices

The relaxed lower bound has the form

\[
d_{3x}(0)\ge c27^x e^{-D x^{1/3}}x^{13/6}
\]

for all sufficiently large `x`, with constants independent of `n`. This is not circular: the lower bound does not require the high-path truncation used for the published upper bound.

For `X~Binomial(3x,1/3)`,

\[
\frac{2^{2x+y}\binom{3x}{x-y}}{27^x}
=\mathbb P(X=x-y)
\le\mathbb P(X\le x-y)
\le e^{-2y^2/(3x)}.
\]

Combining the estimates gives the particularly concrete bound

\[
\sum_{y>x^{3/4}}\mathbb P_T(H_{3x}=3y)
\le Cx^{4/3}\exp\left(-\frac23x^{1/2}+D x^{1/3}\right).
\]

Here the power is `3/2−13/6+1+1=4/3`: one power bounds `3y+1`, and one bounds the number of heights. Summing over all integer `x>I` gives a quantity `F(I)->0`; allowing `x>n` only enlarges the upper bound. Thus the estimate is uniform over every terminal size.

Now consider a retained run at source level `m<M` whose terminating rise occurs at time `i>L`. Its endpoint in the original coordinates is `(h,m+1)`, so its transformed height is **exactly**

\[
j=i-3(m+1)\ge i-3M.
\]

Let `p=3 floor(i/3)` and write `p=3x`. Each forward jump is at most `+1`; hence

\[
H_p\ge H_i-(i-p)\ge p-3M,
\qquad H_p/3\ge x-M.
\]

This direction of the comparison is correct even when the last jump is a down step. Also `p>=i−2>L−2`, so `x>(L−2)/3`. For fixed `M`, choose `X_M` such that `x−M>x^(3/4)` whenever `x>=X_M`. Once `L` is large enough, every delayed retained rise therefore forces a forbidden block point with `x>(L−2)/3`.

Two products in `[0,1]` have difference at most the indicator that some retained factor is treated differently. Taking a union over possible delayed rises is already included in the event of visiting **some** forbidden block point. Consequently

\[
\sup_n |\rho_n^{[M]}-\rho_n^{[M,L]}|
\le F\!\left(\left\lfloor(L-2)/3\right\rfloor\right)\longrightarrow0
\]

for sufficiently large `L` depending on `M`. If `3n<=L`, the two products agree identically. This covers all endpoint-time and small-terminal exceptions.

## 7. Passing to the ratio and amplitude limits

For fixed `M`, the sequence `rho_n^[M]` is uniformly approximated by sequences `rho_n^[M,L]` that have limits. The ordinary Cauchy criterion therefore proves its convergence; no interchange theorem or unproved uniform tracking estimate is needed. The independent uniform `1/(2M)` bound then proves convergence of `rho_n` as `M->infinity`.

For every `n>=1`, the completed-run lower bound gives `rho_n>=P_(3,n)>=P_3`, where Euler's sine product gives the displayed expression for `P_3`. Thus the limit is strictly positive.

Finally,

\[
B_n=2^{n-1}\rho_nR_n
\sim \frac{\rho_\infty C_R}{2}(n!)^2
\left(\frac{27}{2}\right)^n
\exp(3\,3^{1/3}a_1 n^{1/3})n^{5/3}.
\]

The `1/2` in the amplitude, the base `27/2`, and the power `5/3` are all correct.

## 8. Independent finite consistency checks

`check_transfer.py` uses exact rational arithmetic. Its output is saved in `exact-checks.json`.

- The path-product identity agrees with the signed DFA recurrence, including its auxiliary first-row value, for `n=1,...,9`
- The first values include `(R_2,B_2)=(7,14)` and `(R_3,B_3)=(139,532)`, with the latter ratio `133/139`
- Finite-level and finite-time product ordering, the `1/(2M)` bound, and equality once `L>=3n` pass the tested ranges
- Backward normalized monotonicity passes 858 exact adjacent-height comparisons for terminal times `3,6,...,36`
- Every tested bridge visiting-probability inequality (T2) passes

These checks guard against normalization and boundary slips. The infinite-time conclusions rest on the analytic arguments above, not on the finite tests.
