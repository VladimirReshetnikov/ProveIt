# A consecutive-product CRT modulus with a signed factorial output

## Scope, inherited interfaces, and the exact source change

This is an ordinary mathematical proof of the arithmetic source used by
the final consecutive-modulus refinement. The older 512-variable
specialization and `COFINAL_PROOF.md` remain a complete separate
checkpoint. The earlier source with `y=V^2+3F^2-1` is not the principal
source proved here. Literal coordinate maps, polynomial metrics, and
coefficient certificates are supplied separately by the emitting tools.

The parent is the derived-label, square-shell, factorial-carrier direct
construction at repository commit
`45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6`. The following inherited
interfaces are used with their original hypotheses:

1. The numerical C222 calculus and its finite syntax transfer to the
   square-shell encoding; its calibration to finite ZF and ZFC
   refutations is recorded by
   `KEndpoint.c222_iff_zf_refutation` and
   `ConstructibleChoice.zf_refutation_iff_zfc_refutation`.
2. The literal signed simultaneous Pell-power theorem, its square-frame
   budget, seed inequalities, and output-orientation lemma. These are
   the same interfaces used by the parent signed compiler.
3. The exact and residue-only binomial digit graphs, including their
   stated carry bounds.
4. `FACTORIAL_CARRIER_PROOF.md`, for bounded local proof certificates,
   multiplicative Horn flow, and the first beta-CRT encoding;
   `HYBRID_PROOF.md`, for reciprocal prime-power CRT and simultaneous
   completeness at precision `2K`; and
   `DERIVED_LABEL_RANGE_PROOF.md`, for the derived label range and the
   horizon-16 growth floor.

The final source keeps `F` and `V` as initially unrestricted integers.
Let `f2` be the already existing coordinate with defining row
`f2=F^2`. The arithmetic definitions changed from the original parent
are exactly

```
t = 16 + h^2,
rho = f2*t^2,
R = 2+t+x+y+f2,       K = 2R,
y = V(V-1).
```

The original power request with output `V` is retained; its intended
meaning is `V=(rho+1)^t`. The source also retains the proposed
factorial binomial `D`, reciprocal-product binomial `B`, and common
radix requests with intended meanings

```
D = binom(rho+t,t),       B = binom(F^2+t,t),
N = B^K,                 q = N(N+V+1)^K.
```

Those meanings will be proved in the order below. Variable powers,
binomials, and factorials are explanatory notation for retained
polynomial graphs, not operations in the final polynomial.

The natural guard on `t-16` is replaced by one square witness. The
three private sign witnesses for `F` are deleted. The three private
sign witnesses for the endpoint slack `r0` are also deleted, but the
endpoint equation `r0=y-F-1` remains. No other sign guard is deleted.
The modulus row is the quadratic polynomial

```
y - V^2 + V = 0.
```

There is no new square coordinate. Before subsequent projection, the
inherited source bindings are `t0` at index 0, `x` at 1, `y` at 2,
`F` at 3, `t^2` at 4, `rho` at 5, `D` at 6, `V` at 7,
`r0` at 12, `R` at 26, and `f2` at 27, with `t=t0+16`.
The separate source transformation certificate identifies the actual
retained and removed coordinates and verifies the literal rows.

## 1. Positivity before any indexed-Pell interpretation

For every integer `v`, the product `v(v-1)` is nonnegative. Indeed,
either `v<=0`, in which case both factors are nonpositive, or `v>=1`,
in which case both are nonnegative. Therefore the new raw modulus row
gives

```
y>=0,                y+1>=1
```

for every signed proposed output `V`, including `V=0` and `V=1`.
No norm obstruction, parity restriction, or interpretation of `V`
is required for this initial conclusion.

The other unchanged raw rows and guards give `t>=16`, `x>=0`,
`f2=F^2>=0`, and `rho=f2*t^2>=0`. In particular

```
R=2+t+x+y+F^2>=18,           K=2R>0.
```

Every seed index is now positive before power recovery. The complete
types of seed indices are:

- `t` and the derived `t+1`;
- `K`;
- `rho+t` and `F^2+t`;
- `y+1` and `x+1`;
- the positively shifted independent CRT representatives;
- the derived label sum `J`, whose positive-constructor circuit depends
  on the guarded encoded parameters and contains a positive constant.

Neither `F>=0` nor `r0>=0` is needed to establish this list. The original
automatic positivity certificate is consequently replaced by these
arguments rather than cited with a deleted premise.

The unchanged frame budget is two plus the squares of all actual
power bases, exponents, and outputs. Hence `W>=2` and it bounds the
absolute values of those atoms. Its retained bootstrap rows imply

```
A^2-W^3(W+2)(z+1)^2=1,        A,z>=0,
```

so `A>=6`. Every retained seed inequality `Y_i>=k_i` now gives
`Y_i>=1`. The unchanged shared auxiliary-product equation therefore
gives a nonzero auxiliary ordinate, and its norm gives `|U|>=2`.
The retained comparison-base construction then supplies a base at
least two. These are precisely the hypotheses of the inherited
signed indexed-Pell theorem. This uses only raw rows and retained
guards, before factorial or binomial semantics.

## 2. Orienting the shared index recovers the factorial output's sign

The two unchanged raw factorial-ceiling rows have the form

```
V+D = DF+u+1,              D=u+v+1,
```

with `u,v>=0`. Thus `D>=1`. The retained digit output-bound row gives
`q=D+o+1` with `o>=0`, so `q>=2`, before the binomial meaning of `D`
is assumed.

The genuine request with base `q` and exponent `t` orients the shared
`t`-indexed pair by the parent's signed-output lemma at a base at
least two. The original `V` request uses that same pair and has base
`rho+1>=1`. Consequently

```
V=(rho+1)^t>=1.
```

Subtracting the raw ceiling rows gives `DF=V+v>0`. Since `D>0`,
this forces `F>=1`. This is a recovered sign, not an assumed
factorial interpretation.

There is now a stronger lower bound. Since `t>=16` and `F>=1`,

```
V >= rho+1 = F^2*t^2+1 >= F+2.
```

Therefore

```
y=V(V-1) >= (F+2)(F+1) >= F+1,
r0=y-F-1>=0.
```

The endpoint slack is restored before using endpoint, beta-CRT, or
local Horn semantics. Its deleted private sign witnesses can be
supplied whenever needed by the standard three-variable representation
of a nonnegative integer.

## 3. Recovering the remaining powers without a circular radix argument

The unchanged reciprocal-index row is

```
C+F^2+1 = B*i_q,
```

where `C>=1` and the original `B>=0` guard remain. Its positive left
side forces `B>0`. In the signed request `N=B^K`, the only possible
inverse-output case is `B=1, N=-1`. In that case the other base at
the shared exponent `K` is `N+V+1=V>=3`. Its request orients the
`K` pair and rules out that inverse case. Thus

```
N=B^K>=1,           q=N(N+V+1)^K>V^K>=V^2.
```

Every remaining seed is oriented by an actual request at base `q`
or `q+1`, both at least two. All seed indices were proved positive
in Section 1. Hence all original power requests have their intended
meanings before any digit under validation is interpreted as a
binomial, and before `F=t!` is used.

## 4. The self-bounding factorial lemma at a squared radius

**Lemma.** Let `n,f` be positive integers and put

```
rho=f^2*n^2,       V=(rho+1)^n,       D=binom(rho+n,n).
```

There are natural `u,v` satisfying

```
V+D=Df+u+1,        D=u+v+1
```

if and only if `f=n!`.

**Proof.** The rows are equivalent to `f-1<V/D<=f`. Write `G=n!`.
The exact product identity is

```
V/D = G product_(i=1)^n (1-(i-1)/(rho+i)).
```

All factors lie in `(0,1]`. The sum of their deficits is at most

```
n(n-1)/(2rho) = (n-1)/(2f^2*n) < 1/(2f^2).
```

The elementary finite-product inequality therefore gives

```
G(1-1/(2f^2)) < V/D <= G.
```

If `f-1<V/D<=f`, then `G>f-1`, so integrality gives `G>=f`.
Conversely the strict lower estimate and `V/D<=f` imply

```
G < f/(1-1/(2f^2))
  = f+f/(2f^2-1)
 <= f+1.
```

Thus `G<=f` and `G=f`. For completeness, set `f=G`. The same
estimate gives `G-1/2<V/D<=G`, so the ceiling is `G`. The explicit
natural witnesses are

```
u=V+D-DG-1,            v=DG-V.
```

Both defining rows hold. The cases `f=1` and `n=1` are included.
This proves the lemma.

## 5. Validating exact digits before factorial semantics

By Sections 2–3, `F>=1`, `rho=F^2*t^2>=t`, and `q>V^2`.
For `0<=j<=t`,

```
binom(rho+t,j) <= binom(rho+t,t) <= (rho+1)^t=V<q.
```

The first inequality is the usual increasing low-index binomial
bound because `rho+t>=2t`; the second follows by multiplying
`(rho+i)/i<=rho+1` for `1<=i<=t`. Thus the exact digit graph really
gives `D=binom(rho+t,t)`. Applying Section 4 to the retained ceiling
rows now proves `F=t!`.

The reciprocal binomial is also within its digit bound. For every
`F,t>=1`,

```
F^2+t <= F^2*t^2+1=rho+1,
```

since the difference is `F^2(t^2-1)-t+1>=t(t-1)>=0`.
Every coefficient through index `t` is therefore at most
`(F^2+t)^t<=V<q`. Its exact digit gives
`B=binom(F^2+t,t)`, and the inherited reciprocal-modulus identity
and bound `B>=2` apply. Only at this stage use `N>=2^K`.

## 6. Later majorants and soundness are preserved

Once `F>=1`, the modified majorant satisfies

```
R=2+t+x+y+F^2 >= 2+t+x+y+F = R_old.
```

The bounded local Horn polynomial `L` and the derived label polynomial
`J` have not changed. Their literal certificates bounding them by
`R_old^E`, with `E=8388608`, consequently bound them by `R^E`.
The original exponential-majorant induction applies because
`R>=F^2>=F=t!>=16!`, giving `R^E<2^R<2^K` with its retained finite
base certificate.

Every ordinary range lower index is still at most `R-1`, and `K=2R`.
The aggregate representative bound and digit estimate are unchanged.
The separate derived-label estimate retains its inequality
`3*ell*(t+1)<=2F<2R`. Thus the amplified CRT and derived-range
decoding apply in their original order, after the bootstrap above.

The first beta encoding uses only natural local states bounded by `y`
and the endpoint relations

```
x=F+1+(y+1)u0,        y=F+1+r0,
x=1+[1+(t+1)y]ut.
```

Its remainder moduli exceed `y`; this proves overlap and the stated
endpoints. Every weight `1+jF` is positive, so the multiplicative
flow propagates positivity of all states from `S_0=F+1`.
For `1<=j<=t`, the weights are pairwise coprime because `F=t!`.
Prime valuations therefore give the parent's exact multiplicity
balance. The finite closure argument in the inherited Horn-flow
theorem extracts a finite C222 derivation even if the supplied
multiset of rule instances has cycles. Calibration then gives a
finite syntactic ZFC refutation.

In particular, neither an assumption of consistency nor any assumed
truth of the source rules in the universe is used for this extraction.

## 7. A strict pending-product bound

**Lemma.** Let `F>=1`, `t>=2`, and `a=Ft>=3`. Consider a backward
proof-tree expansion with at most `t` steps, each replacing one
pending conclusion by at most two premises, and labels in `[0,t]`.
With `V=(1+F^2*t^2)^t`, every pending accumulator satisfies `S<V`.

**Proof.** The initial pending multiset has one member, so after
at most `t` steps it has at most `t+1` members. Each weight is at
most `L=1+Ft=a+1`. Thus `S<=L^(t+1)`. Put `A0=a^2+1`. Then

```
A0>(a-1)L,
(a-1)^t >= (a-1)^2 >= L,
```

where the second inequality uses
`(a-1)^2-(a+1)=a(a-3)>=0`. Consequently

```
V=A0^t > L^t(a-1)^t >= L^(t+1) >= S.
```

The empty product is one. Truth factors have weight one, and truth
padding leaves the accumulator unchanged, so these cases are
included. This proves the lemma. Its assumptions hold throughout
the canonical construction because `t>=16`.

## 8. Complete reconstruction from a finite refutation

Translate a finite ZFC refutation to a finite C222 derivation using
the inherited calibration. Expand its finite proof DAG into a proof
tree. Collect its step count, all local parameters, all complete
constructor-label bounds (including unused branches at the chosen
tuples), and the fixed truth-padding tuple.

The parent completeness theorem permits every sufficiently large
integer horizon, with all later witnesses chosen afterwards. Choose
`h` such that `t=16+h^2` exceeds all the collected finite bounds.
There is no horizon congruence requirement. This cofinal restriction
is justified by eventual freedom of the horizon, not by the false
claim that an arbitrary unbounded admissible set contains squares.

Now set

```
F=t!,      rho=F^2*t^2,      V=(rho+1)^t,      y=V(V-1).
```

Construct the positive pending-multiset accumulators and enough
truth padding to give exactly `t` rows. Section 7 proves `S_i<V`
for every accumulator. Since `V>=F+2>=3`,

```
y=V(V-1)>=V>S_i,             y>=F+1.
```

Also `rho+1` and `V` are congruent to one modulo `F`, so `F|(V-1)`
and hence `F|y`.

These are exactly the inherited first-CRT requirements:

```
S_i,S'_i <= y,        y>=F+1,        F|y.
```

There is no inherited requirement `y>V^2`. That inequality was only
a sufficient convenience in the previous modulus proof and is
deliberately replaced by the strict bound of Section 7.

For completeness of the first CRT step, the moduli
`m_i=1+(i+1)y`, `0<=i<=t`, are pairwise coprime. A common prime
divisor of `m_i,m_j` cannot divide `y`; it would divide `j-i`,
so it is at most `t`, hence divides `F=t!` and thus `y`, a
contradiction. Choose a common nonnegative CRT code `x` for all
states. Because `0<S_i<=y<m_i`, its Euclidean quotients are
nonnegative and at most `x`. Supply the two endpoint quotients
and `r0=y-F-1`.

Only after `x,y` are fixed choose `R,K`, the reciprocal product and
common radix, and all amplified CRT representatives at the original
precision `2K`. The old fixed canonical index is not substituted
for those representatives. The new factorial lemma supplies its
ceiling witnesses, and the unchanged exact/fused digit arguments
supply the other natural quotients and slacks. Rebuild the common
square frame and private Pell witnesses for this entire finite
family of true powers. Supply every retained ternary sign guard.
The full changed source therefore has an integer zero.

The dependence order is acyclic:

```
finite refutation -> h,t -> F,rho,V,y -> x -> R,K,
reciprocal/amplified data -> digit witnesses -> common Pell frame.
```

The completeness proof reconstructs witnesses from a refutation.
It does not assert that an arbitrary old source zero can be reused
pointwise with its old horizon and modulus.

## 9. From the arithmetic source to the fixed polynomial

Sections 1–6 prove source soundness, and Sections 7–8 prove
constructive completeness. The separately recorded factoring,
monic integral projection, and integer translation maps preserve
zero existence in both directions. Their quadratic residuals are
combined into one ordinary polynomial by summing their squares.
An integer sum of squares vanishes exactly when every residual
vanishes.

All quantified arguments here use finite syntax and induction,
integer arithmetic, factorial identities, CRT, the three-square
representation of nonnegative integers, and the inherited uniform
Pell/calculus theorems. They are formalizable in ZFC without its
consistency as a premise. Composing them with the exact emitted
gate binding proves, in ZFC, that existence of a zero of the fixed
polynomial is equivalent to existence of a finite ZFC refutation.
Negation gives the requested equivalence with `Con(ZFC)`.

This is an ordinary mathematical proof composed with identified
inherited theorems. It is not a new end-to-end Lean/Rocq derivation,
a proof of unsolvability, or a claim of global minimality. Finite
regression tests check selected arithmetic cases and transcription
controls; they do not replace any unbounded argument above.
