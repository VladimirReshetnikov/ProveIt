# Coupled indices save three additions in the complete GPCP compiler

The [literal compiler](gpcp_coupled_index_units754.py) changes three private
linear targets in the [fixed-target757 parent](gpcp_index_linear_units757.md)
and removes their three unused successor additions. The default complete
polynomial costs **754=352M+402A**, with 728 certificate operations,
9 comparisons, 125 positive witnesses, three fixed positive program
parameters and ordinary positive input. Its exact formal degree is 205777.
The supplied-initial interface costs **757=353M+404A**, with 10 comparisons,
126 witnesses and exact degree 8892.

The mathematical transfer is a **surjective positive projection with exactly
four preimages over each positive parent zero**, including an identity
section. It changes two private coordinates in each AND core. It applies
for every positive choice of the program parameters and preserves every
external parameter and input coordinate. It does not assert that every
parameter/input choice has a zero, and it does not transfer the parent's
same-coordinate equality theorem unchanged. The independent 75-certificate/
87-polynomial universal bound is unchanged.

The [receipt](gpcp_coupled_index_units754.json) contains all eight complete
polynomial schedules, costs, exact-degree certificates and replay evidence.
Only parents with ancestor stage 763 and both fixed-target index and linear
conversions enabled are admitted. The eight forms toggle the initial
interface and the AND/geometry bound conversions. No 765 ancestor or
partially converted parent is admitted.

## 1. Literal source, privacy and operation accounting

The three core prefixes are `geo__`, `and__`, and `hist__and__`. In one
core write `r=J` for geometry or `r=bs_packed` for an AND, `E=XY`,
`K=k−hE`, and `V=of−c`. The selected 757 parent computes

```text
r1 = r+1
R11 = k−hE = K
tr1 = r1+r1
index_unit = K−r
linear_unit = V−jc+tr1
H2 = V*V
```

Replace `tr1` by `R11+R11=2K` and delete `r1`. The new factors are

\[
 N_k=K-r,\qquad N_l=V-jc+2K.
\]

Everything else in the actual source remains present, including the genuine
`V²` auxiliary norm. There are no new witnesses, factors or comparisons.
Each deleted row is one paid addition. The complete polynomial finalizer
and its multiplication count are unchanged.

The compiler pins the complete parent Python file SHA-256 to
`a8b213386863857dae8c98f06a2ab41b297e05e6742b91217f538efaf7087774`
and compares the complete imported parent against its exact-type canonical
packet. It checks every changed row and its consumers. In each parent,
`r1` feeds only `tr1`, `tr1` feeds only the linear factor, and `K` feeds only
the index factor. The new schedule adds `tr1` as a consumer of `K`.
Every emitted gate is checked to reach the final polynomial output.

For each AND, supplied `F0` occurs only in `shared_sum02` and `bs_packed`;
supplied `bound_beta` occurs only in `bs_X_bound`. The packed index feeds
only its private successor, native bound and index factor. Neither mapped
coordinate occurs in the active external/program/history exports, after
excluding the explicit list of supplied auxiliaries. These literal checks
are what permit the coordinate projection below without changing a history
word, mask, input, output or program parameter.

|Initial interface|AND bound units|Geometry bound units|Polynomial operations|Comparisons|Witnesses|Exact formal degree|
|---|---|---|---:|---:|---:|---:|
|Computed|No|No|758=352M+406A|13|125|214694|
|Computed|No|Yes|756=352M+404A|11|125|214760|
|Computed|Yes|No|756=352M+404A|11|125|205711|
|Computed|Yes|Yes|754=352M+402A|9|125|205777|
|Supplied|No|No|761=353M+408A|14|126|8904|
|Supplied|No|Yes|759=353M+406A|12|126|8970|
|Supplied|Yes|No|759=353M+406A|12|126|8826|
|Supplied|Yes|Yes|757=353M+404A|10|126|8892|

All counts charge additions, subtractions and multiplications, including
multiplication by numerical constants, in the literal straight-line model.
The exact degrees are formal degrees before specializing program parameters;
a specialization is not asserted to preserve them.

## 2. Recover shifted local indices before using either AND theorem

The complete finalizer is `W*(1+S)−1`, where `W` is the product of every
unit factor and `S` is the sum of squares of every remaining ordinary
residual. At an integer zero, `W=1`, `S=0`, and each integer factor is
`±1`. We now restrict all supplied coordinates and parameters to positive
integers. The following deductions use unchanged scalar definitions and
norms, not the completed parent equivalence theorem.

The [fixed-target proof, Sections 2–5](gpcp_index_linear_units757.md#2-establish-the-weak-scalar-cone-before-recovering-any-new-sign)
establishes the weak scalar cone, positive Pell norms, normalized strong
rank, positivity of `V`, and strict auxiliary stepdown from the actual
source. Its starting bounds remain available here:

\[
 r\ge9,\quad X\ge r,\quad Y\ge6,\quad
 E>2r+3,\quad Y(r-1)>2(2r+3).
\]

For AND cores the bound is strict: `X>r`. Positivity and the literal padding
residues prove this even when either checksum or first-padding unit is
negative. Geometry needs only `X>=r=J>=B>=2^127`. The four local norm
factors are still `+1` by their modulo-four obstructions. In particular,
the normalized strong equation is the unchanged full equation
`f²−Delta*(ic²)²=1`; it implies `pc|m`, not merely `c|m`.

Write `epsilon=Nk` and `lambda=Nl`, both signs. The new target is

\[
 J_* =2K-\lambda=2r+2\epsilon-\lambda,
 \qquad 2r-3\le J_*\le2r+3.
\]

This target is positive and below `c/2` in the same weak cone. The first
Pell index satisfies `n>=r−1`, the main index satisfies `p>=r`, and the
normalized rank gives `V>0` before a sign is selected. The same strict
stepdown and no-wrap windows therefore give

\[
 p=2K-\lambda,\qquad n=K=r+\epsilon.
\]

With Pell parameters `A=Y(X+1)+2`, `P0=2XY²+1`, duplication gives

\[
 \psi_A(2n)=2A\psi_{2A^2-1}(n)>(Y+1)\psi_{P0}(n)=(Y+1)k.
\]

The unchanged ratio has `c=psi_A(p)<(Y+1)k`. Thus `lambda=−1`, which
would give `p=2n+1`, is impossible. It follows that all three new linear
signs are `+1`, but this argument does **not** force `epsilon=+1`. Set

\[
 \rho=r+\epsilon-1,\qquad n=\rho+1,\qquad p=2\rho+1.
\]

The raw power/population argument now applies at `rho`, before native AND
or history typing. In an AND, the actual positive fields give
`r>=8q³+q²+q+1`, hence `rho>q` and `rho>=9`, with `X>rho`.
In geometry, `rho>=J−2>B−3>q` and `X>=rho`; when `epsilon=+1` this is
exactly the previously justified weak geometry boundary. The unchanged
ratio, exponent comparison and odd scaling consequently give

\[
 X=2^{2\rho+1},\qquad q=2^{\operatorname{popcount}(\rho)}.       \tag{1}
\]

Only this raw scalar conclusion is used next. Invoking the completed AND,
recoder or history theorem here would skip the sign obligations.

## 3. AND signs, including subtraction across a base-q boundary

In either AND write `C=q−sum Fi` for the checksum sign and `sigma` for the
first-padding sign. The retained second padding and actual computed `F3`
give the table below. By (1), write `q=2^t=16Q`, with `t>=4`. Positivity
and `sum Fi=q−C` imply `0<Fi<q`; the four base-q blocks in the packed index
are therefore disjoint. The high parts below are nonnegative integers.

|C|sigma|`(F0,F1,F2,F3) mod16`|Sum of high parts|Low-bit population|
|---:|---:|---|---|---:|
|+1|+1|(1,4,2,8)|Q−1|4|
|−1|+1|(3,4,2,8)|Q−1|5|
|+1|−1|(15,6,2,8)|Q−2|8|
|−1|−1|(1,6,2,8)|Q−1|5|

The sum of the high-part populations is at least the population of their
sum. For `epsilon=+1`, `rho=r`, so the last three rows have population at
least `t+1,t+3,t+1`, respectively. The `Q−2` case with `Q=1` is impossible.
Only `C=sigma=+1` can satisfy (1).

For `epsilon=−1`, use `rho=r−2`:

- `C=−1,sigma=+1`: the first low nibble changes from 3 to 1, giving low
  population 4 and high sum `Q−1`. This is the surviving sign case.
- `C=+1,sigma=−1`: the first low nibble changes from 15 to 13, giving low
  population 7 and high sum `Q−2`, hence total at least `t+2`.
- `C=+1,sigma=+1`: if `F0>=17`, the first low nibble changes from 1 to 15
  and its high part decreases by one. Low population 7 and high sum `Q−2`
  again give at least `t+2`.
- `C=−1,sigma=−1`: the same within-field subtraction, when `F0>=17`, gives
  low population 8 and high sum `Q−2`, hence at least `t+3`.

In either of the final two cases, `F0=1` needs separate treatment. The
subtraction borrows into the next base-q block: the new first block is
`q−1`, the second is `F1−1`, and `F2,F3` are unchanged and positive.
The second block's low nibble is 3 or 5, so total population is at least
`t+2+1+1=t+4`. This excludes the cross-block corner as well.

Therefore the necessary classification in both ANDs is

\[
 \boxed{\sigma=1,\qquad C=\epsilon.}                         \tag{2}
\]

For a negative surviving sign, `F0=3 mod16`, so `F0−2` is positive.
No assertion is made that a field tuple surviving the population test
alone extends to all compiled Pell equations. The receipt's example
`q=64`, fields `(3,20,34,8)`, `r=2237699`, has
`popcount(r−2)=6`; it is only a component example.

## 4. Geometry's index sign is positive without full recoder typing

The literal outer rows, guarded by the wrapper, are

\[
 q_g=\texttt{input_bound},\quad B=2^{63}q_g^{64},\quad
 P=(B-1)J+1,\quad \texttt{scale}=q_gP,\quad q_{\rm rec}=16q_gP.
\]

Equation (1) makes both `q_g` and the recoder's native `q_rec` dyadic.
Hence the positive integer `P` is dyadic. Write
`q_g=2^a`, `B=2^b` with `b=63+64a`, and `P=2^e`.
The relation `B−1 | P−1` implies `b|e`: writing `e=ub+v`, `0<=v<b`,
a nonzero remainder would require `2^b−1` to divide the smaller positive
integer `2^v−1`. Thus

\[
 P=B^s,\qquad J=1+B+\cdots+B^{s-1}.
\]

The supplied bound `J>=B` implies `s>=2`. If geometry had `epsilon=−1`,
(1) would require

\[
 a=\operatorname{popcount}(J-2)=b+s-2\ge b=63+64a>a,
\]

a contradiction. The population identity follows by borrowing from the
second base-B digit: the first becomes `B−1`, the second becomes zero,
and `s−2` further one digits remain. Therefore geometry's index sign is
`+1`. This argument uses only raw populations and positive literal scale
relations; no full recoder AND relation or history interpretation is needed.

## 5. Positive projection, section, and exactly four preimages

For each AND core define the map to its selected 757 parent by

\[
 F0_{\rm old}=F0+\epsilon-1,\qquad
 \beta_{\rm old}=\beta+1-\epsilon.                         \tag{3}
\]

Retain every other supplied coordinate. Formula (2) makes the first
coordinate positive: it is unchanged for the positive sign and subtracts
two from a positive integer congruent to 3 modulo16 for the negative sign.
The second coordinate is unchanged or increased by two.

The parent's packed index is `r_old=r+epsilon−1=rho`, so its successor
is `rho+1=K`. Its fixed target `2r_old+2` equals the child's `2K`.
Its checksum is `C−epsilon+1=1` and its index unit is `K−rho=1`.
Its linear factor stays `+1`. Both native bounds preserve their exact
values, because

\[
 \rho+\beta_{\rm old}=r+\beta.
\]

The actual padded inputs, all genuine `V²` norms and all remaining ordinary
residuals are unchanged. The coordinate privacy checks in Section 1 justify
these assertions for the full source. In geometry no coordinate changes;
its index and linear signs have both been proved `+1`. In each AND the two
child factors removed by sign normalization have product
`C*Nk=epsilon²=1`. Consequently the complete parent factor product is one
and all parent residuals vanish. This proves a positive map from every
child zero to a parent zero for every positive program-parameter choice.

Conversely, on a positive 757 parent zero, all index, linear, checksum and
first-padding signs are `+1`. Thus `K=r+1`, and the child's `2K` equals the
parent's target. The identical supplied tuple is already a child zero,
and (3) returns it unchanged. This is the identity section and proves
surjectivity onto the entire parent positive zero set.

There are exactly four positive preimages, not just this one. At a positive
parent zero, (1) gives `X=2^(2r+1)`, `r>=9`. The parent's positive native
slack is `beta=X−r` for an ordinary bound or `beta=X−r−H` for a bound unit
`H=±1`. In either case `beta>2`. Independently in each of the two ANDs,
choose `delta` in `{0,2}` and set

\[
 F0_{\rm child}=F0_{\rm parent}+\delta,\qquad
 \beta_{\rm child}=\beta_{\rm parent}-\delta.               \tag{4}
\]

Every coordinate stays positive. The child index and checksum become
`1−delta`, their product stays one, and every linear sign, other factor
and ordinary residual retains its parent value. Thus the four independent
choices all give child zeros, and (3) sends each back to the original
parent zero. Conversely, (2) permits only `epsilon=±1`; a preimage of a
fixed parent tuple must have exactly `delta=1−epsilon` in each AND, with
all other supplied coordinates fixed. Hence these four distinct lifts
exhaust every positive fiber. This statement is conditional on a parent
zero; it does not create one for a nonmember input.

## 6. Complete off-zero correction after the formal coordinate map

Extend (3) to every integer assignment using the actual integer value
`epsilon=Nk`, without assuming it is a sign. Positivity is not asserted
for this formal extension. Write `C_r,C_h` for the two child checksums,
`epsilon_g,epsilon_r,epsilon_h` for its index factors and
`lambda_g,lambda_r,lambda_h` for its linear factors.

Under the formal map, both parent AND index factors are identically one;
their checksums are `C_j−epsilon_j+1`; their linear factors are unchanged.
The parent's geometry index remains `epsilon_g`, and its linear factor is
`lambda_g−2(epsilon_g−1)`. Every other unit factor, every actual auxiliary
`P17` factor and every retained ordinary residual is unchanged.

Let `B0` be the product of all common factors excluding the two checksums
and the six index/linear factors, and put `T=B0*epsilon_g*lambda_r*lambda_h`.
If `S` is the common retained residual sum of squares, the complete products
satisfy

\[
\begin{aligned}
 W_{754}&=T C_r C_h\epsilon_r\epsilon_h\lambda_g,\\
 W_{757}(\pi v)&=T(C_r-\epsilon_r+1)(C_h-\epsilon_h+1)
                   (\lambda_g-2(\epsilon_g-1)).
\end{aligned}
\]

Therefore, for every integer supplied tuple, including signed off-zero
assignments,

\[
 F_{757}(\pi v)-F_{754}(v)=
 [W_{757}(\pi v)-W_{754}(v)](1+S).                         \tag{5}
\]

This is a division-free correction, not an assertion of polynomial identity.
The public `offzero_correction` checks it by executing both complete actual
polynomial schedules and comparing every unit factor and retained residual.
The formal lifts (4) are also checked directly: their AND index/checksum
factors subtract `delta`, their three linear factors change by
`2*(parent_index_unit−1)`, and all other factors/residuals agree.

## 7. Exact degree, guarded APIs and replay evidence

Degree propagation uses the full emitted polynomial source and the three
fully guarded expanded main-norm identities inherited from the
[shared-selector degree checker](gpcp_shared_selectors774.py). At each `R15`,
the highest term is `2*cam2*gam`, strictly above every other term of its
expanded identity. Every supporting literal row and strict degree inequality
is checked. The remaining gates use ordinary degree propagation.

To certify actual degree rather than just an upper bound, the receipt stores
explicit assignments at which the complete top homogeneous output is
nonzero modulo both `1000000007` and `1000000009`. Every factor's top value
is also recorded and nonzero. For the default form the output values are
`554805445` and `706438710`, at formal degree 205777; for supplied initial
with both bounds they are `76468308` and `336173198`, at degree 8892.
The complete output degree equals the unit-product degree plus twice the
largest remaining outer degree: `196667+2*4555` by default and
`8622+2*135` for supplied initial. The explicit nonzero evaluations exclude
cancellation at those degrees.

Public APIs are `build`, `canonical_parent`, `rewrite`, `checked`,
`polynomial_source`, `degree_audit`, `ledger`, `evaluate`,
`project_assignment`, `lift_assignment`, and `offzero_correction`.
The assignment APIs require exactly all supplied parameter/auxiliary names
with exact integer values; Booleans and floats are rejected. Signed integers
are accepted for formal off-zero algebra, while the equivalence theorem is
strictly over positive coordinates. Lift deltas must be exact integers 0
or 2. Public parent/build accessors return defensive copies; exact-type
canonical comparison and cache-poisoning regressions protect the guarded
reference packets. Inherited same-coordinate equality metadata is removed.

The author receipt checks all eight forms and records:

- 96 complete projected factor/output corrections, including 48 signed
  cases and 24 zero-decoded-selector contexts;
- 64 complete formal lift factor/residual maps;
- 54,132 field/sign cases, including 1,428 cross-radix borrow cases,
  with 1,365 population survivors in each permitted sign pattern;
- 8,190 positive bound-map identities, 480 literal geometry negative-sign
  exclusions, 1,287 dyadic order cases and 144 positive-slack lift cases;
- 524 rejected malformed callers, including float/Boolean coefficients,
  bad lift deltas, metadata tampering and public cache-poisoning attempts.

These component checks supplement the positive-domain proof. They do not
materialize a complete enormous Pell witness or replace the universal
program/ordinary-input contract inherited through the selected parent.
Run from the repository root:

```sh
/tmp/diophantine-research-venv/bin/python Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/gpcp_coupled_index_units754.py
```

The default mode recomputes and compares the saved receipt without writing
it. `--write` regenerates the author receipt.

Two independent reviews passed on Python SHA-256
`80c5f06ef5ec43975369ed2f9737fdf0d75b44e5abba4c24e19a2bc4fba1f9e3`.
The separate source oracle checked all eight ledgers, 16 leading
certificates, 128 complete projected output corrections (64 signed),
512 complete formal lift corrections, 32 zero-selector maps, and public
copy/type/metadata guards. Its temporary evidence is
`/tmp/review_gpcp754_source.py` and `/tmp/review_gpcp754_source.json`.
A separate API/metadata review rejected 376 malformed calls and checked
eight cold canonical copies, 192 active fields, 32 current interfaces,
24 native-interface/privacy conditions, eight nested public build copies
and 32 formal lift domain cases. That evidence is
`/tmp/review_gpcp754_final_api.py` and `/tmp/review_gpcp754_final_api.json`.
Both reviewers also read the positive-domain proof; the final proof/API
review is saved at `/tmp/review_gpcp754_final.md`. Fresh author and
independent default receipt replays passed. The finite algebraic tests
remain distinct from the proof of positivity and exact fiber cardinality.
