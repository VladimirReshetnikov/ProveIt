# One certified Pell bound and one sum of squared index errors

## Exact theorem

Write

\[
X_0(A)=1,\quad Y_0(A)=0,\qquad
X_{n+1}=AX_n+(A^2-1)Y_n,\quad Y_{n+1}=X_n+AY_n.
\]

Let `W >= 3`, `A - 1 > W^3`, and let the positive requested indices
`k_1,...,k_m` satisfy `k_i < W` and `m <= W-2`. Let
`V = Y_W(A)` be certified once. The following natural-number system has
exactly the canonical principal pairs `x_i=X_{k_i}(A), y_i=Y_{k_i}(A)`:

\[
x_i^2-(A^2-1)y_i^2=1\quad(1\le i\le m),
\]
\[
V=W+1+s+\sum_i y_i,\qquad
\sum_i(y_i-k_i)^2=(A-1)q,
\]

where `s,q` are nonnegative. More precisely: every solution gives those
canonical pairs; conversely canonical pairs extend to a solution whenever
`A>W+1`, which follows from the stated stronger size hypothesis.

### Soundness

Every nonnegative solution of `x^2-(A^2-1)y^2=1` has the form
`(X_j(A),Y_j(A))` for a unique `j>=0`. This is elementary Pell descent:
for `y>1`, the inverse transformation
`(x,y) -> (Ax-(A^2-1)y, Ay-x)` preserves the norm, is nonnegative, and
strictly decreases `y`; the endpoint is `(1,0)`. The fundamental positive
solution is `(A,1)`.

The aggregate bound gives `y_i<V`. Strict monotonicity of `Y_j(A)` gives
`0<=j_i<W`. Reduction of the recurrence modulo `A-1` gives
`X_j(A)=1 mod(A-1)` and `Y_j(A)=j mod(A-1)`. Consequently the pooled row
implies

\[
A-1\mid E:=\sum_i(j_i-k_i)^2.
\]

The two indices in each difference belong to `[0,W-1]`, so

\[
0\le E\le m(W-1)^2\le(W-2)(W-1)^2<W^3<A-1.
\]

Thus `E=0`, and each `j_i=k_i`. The case `j_i=0` is allowed during this
argument; positivity of the requested `k_i` rules it out only at the end.
No individual lower bound `y_i>=k_i` is needed as a premise.

### Constructive completeness

Set `x_i=X_{k_i}(A)` and `y_i=Y_{k_i}(A)`. Each difference `y_i-k_i`
is a nonnegative multiple of `A-1`, so

\[
q=\frac{\sum_i(y_i-k_i)^2}{A-1}
\]

is a nonnegative integer. Also `y_i<=Y_{W-1}(A)`. The Pell recurrence gives

\[
Y_W(A)>(2A-1)Y_{W-1}(A).
\]

Therefore

\[
Y_W(A)-\sum_i y_i>(2A-1-m)Y_{W-1}(A)>W.
\]

The final inequality follows from `m<=W-2`, `A>W+1`, and
`Y_{W-1}(A)>=1`. Hence
`s=Y_W(A)-W-1-sum_i y_i` is nonnegative. These are explicit witness
restorations, not a counting argument or a finite experiment.

## The cap has an ordinary polynomial certificate

The compiler retains one complete copy of the inherited positive
indexed-Pell certificate, now at requested index `W`:

\[
\begin{aligned}
U^2-(A^2-1)V^2&=1,\\
H^2-(A^2-1)J^2&=1,\\
S^2-(B^2-1)R^2&=1,\\
B&=1+4V(d+1),\\
J&=V^2(e+1),\\
B&=A+Hf,\\
S&=U+Hg,\\
R&=W+4Vh.
\end{aligned}
\]

All letters are nonnegative. Its usual hypothesis `W<=V` follows from
the new aggregate row `V=W+1+s+sum y_i`; a separate witness for that
hypothesis has been removed. The inherited indexed-Pell lemma gives
`U=X_W(A), V=Y_W(A)`. Its constructive completeness supplies all six
comparison/congruence witnesses. No unsupported new Pell-index lemma is
substituted for that dependency.

## Why all size hypotheses hold before interpreting any power

The shared frame is the literal row

\[
W=2+\sum_{a\in\mathcal A}a,
\]

where `Acal` is the set of distinct actual base, exponent, and output
atoms of the finite power-request list. Every atom is nonnegative.
Every independent requested index `k_i` is an actual, distinct, positive
exponent atom, so `k_i<W` and `m<=W-2`. Positivity of those exponents is
proved from the raw source expressions and endpoint rows, before the
power graphs have been interpreted. In the selected source there are
16 independent indices and one derived index; the horizon is at least
12. The cap index and private cap witnesses are not inserted into the
semantic atom set.

The retained scale certificate is

\[
A^2-\big((W+1)^2-1\big)\big(W(z+1)\big)^2=1.
\]

Pell classification gives `A=X_l(W+1)` and
`W(z+1)=Y_l(W+1)` for a positive index `l`. Since
`Y_l(W+1)=l mod W`, one has `W|l` and `l>=W`. Thus
`A>=X_W(W+1)>=(W+1)^W`. For `W>=3`,
`(W+1)^W-1>W^3`; hence `A-1>W^3`. This recovers the large-modulus
property from polynomial rows without assuming any power request is
already correct.

## Power outputs and derived indices

For a requested base `n`, the retained modulus and power row are

\[
T_n=2An-n^2-1,\qquad
X_k(A)+(n-A)Y_k(A)=m+T_n q_n.
\]

The existing shared-frame proof gives `T_n>W^W+W`; the requested
base, exponent, and output are all less than `W`. Since the Pell pair has
now been proved to have exactly the requested index, the standard
congruence gives `m=n^k` by the strict interval bound. The original
positive-power completeness supplies a nonnegative quotient `q_n`.

The one additive index in the selected graph is derived by the exact
Pell addition formulas from an already certified independent index.
It is not an unverified extra seed. The standalone metadata lists this
derivation and all its quadratic gates.

## Composition and logical status

The new frame preserves all semantic bases, exponents, and outputs. It
therefore composes with the self-sized binomial radix and the `K=R`
amplification change without altering their CRT semantics. It is an
alternative polynomial representation of the same finite family of
positive-power requests.

The selected arithmetic source still has the literal C222-calculus
constructor formulas, factorial carrier, ten binomial range conditions,
two exact-binomial graphs, and nineteen power requests. Its inherited
ordinary arithmetic and calculus-calibration proof identifies zeros
with C222 refutations and hence with syntactic ZFC refutations. The
present index argument uses only finite algebra, induction, elementary
Pell theory, and integer divisibility, all formalizable internally in
ZFC. It assumes neither consistency nor inconsistency.

Exact JSON row checking and polynomial expansion are finite checks of
the emitted arithmetic syntax. They do not constitute a newly completed
Lean, Rocq, or object-language ZFC proof. No global minimality or
literature-wide priority claim is made.

## Selected finite output

`capped_pooled_h12/natural/equation.json` describes a sum of squares of
194 integer quadratic residuals in 261 nonnegative unknowns. Its fully
collected quartic has 31,679 nonzero monomials and coefficient height
85,566,955. The normalized raw source has 406 variables and 339 rows;
145 certified natural-domain eliminations give the selected equation.

The sparse companion `capped_cantor/natural/equation.json` instead keeps
the individual cap and residue rows. It has 292 natural variables, 225
quadratic rows, 6,140 quartic monomials and height 83,933,334. Both are
strict variable-count improvements over the delivered 349-variable
direct source; the sparse companion also improves its monomial count
and coefficient height. The pooled endpoint trades density for a lower
variable count.
