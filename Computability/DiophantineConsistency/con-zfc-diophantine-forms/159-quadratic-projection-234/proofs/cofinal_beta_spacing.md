# A cofinal quadratic beta spacing with one fewer residual

## Scope

This is a new arithmetic change to the factorial-free direct construction in
`ConZFC_Factorial_Free_Binomial_CRT_2026-10-25`, not a zero-set-preserving
coordinate change. It replaces its two equations

\[
 m=(2w+1)^2,\qquad y=Fm
\]

by the single equation

\[
 \boxed{y=F^2+u^2+v^2.}
\]

The variables `u,v` are unrestricted integers. The same two witness slots
are used, but there is one fewer residual. The existing graph `R=F^2`
allows the displayed equation to be written `y-R-u^2-v^2=0`.

All other semantic data are unchanged, especially

\[
 t=16+h^2,\quad F=[2(t+1)]^t,\quad
 B=\binom{F^2+t}{t},\quad q=(BH)^x,
 \quad q=(2z+1)^2,\quad H=2+\sum A_i.
\]

These exponentials and binomials are explanations of the unchanged
ordinary-polynomial Pell and digit certificates; they are not operations
in the final polynomial.

## 1. Cofinal divisibility lemma

**Lemma.** Let `t>=1` be an integer, and let `F>=2` be an integer such that
`2^{v_2(t!)} | F^2`. For every integer bound `C`, there exist integers
`u,v` such that

\[
 y=F^2+u^2+v^2>C,\qquad t!\mid y.
\]

One may choose both `u` and `v` to be multiples of `F`. If `F` is even,
then the constructed `y` is even.

**Proof.** Write `t!=2^a m` with `m` odd. For every odd prime power
`p^e || m`, the congruence

\[
 a_p^2+b_p^2\equiv -1\pmod {p^e}
\]

has a solution. First, the set of squares in the field `F_p` and the
set `-1` minus those squares each have `(p+1)/2` elements, so they
intersect. A solution modulo `p` cannot have both coordinates zero,
since `-1` is nonzero. At least one derivative `2a_p` or `2b_p`
is therefore nonzero modulo `p`. Holding the other coordinate fixed
and changing this coordinate by a multiple of `p^j` lifts a solution
modulo `p^j` to one modulo `p^{j+1}`. Explicitly, if the first coordinate
is a unit, set

\[
 a'_p=a_p+\delta p^j,\qquad
 \delta\equiv-\frac{1+a_p^2+b_p^2}{p^j}(2a_p)^{-1}\pmod p.
\]

The identical formula with `b_p` applies otherwise. This proves
solvability at all exponents without invoking any analytic result.

Apply the Chinese remainder theorem separately to the first and second
coordinates to obtain integers `a,b` with `m | 1+a^2+b^2`. Put

\[
 u_k=F(a+km),\quad v_k=Fb,\quad
 y_k=F^2\bigl(1+(a+km)^2+b^2\bigr).
\]

Then `m | y_k`, while the assumed power of two divides `F^2`, hence
divides `y_k`. Thus `t! | y_k`. As `k` tends to positive infinity,
`y_k` tends to infinity, proving cofinality. The parity conclusion
is immediate. This also covers `m=1`, when the congruence is vacuous.
QED.

For the actual front, `F=[2(t+1)]^t`, so `v_2(F)>=t` and
`v_2(t!)<t`. The lemma therefore applies with a large margin.

## 2. Soundness bootstrap

The inherited signed Pell-frame theorem is unchanged: the known
positive horizon and the power request at base `2(t+1)` first imply
the genuine equality `F=[2(t+1)]^t`. Thus `F>=7` at every complete
zero, before any interpretation of the CRT digit.

The new row now gives

\[
 y\ge F^2>F+1>0.
\]

The parent proof's other initial steps still apply. The odd-square
radix gives `q>=1`; the power requests at base `q+1` make the nine
actual CRT representatives nonnegative; hence `H>=2`. The retained
index row `B*iota=C_0+F^2+1` makes `B` nonzero. The signed power lemma
at base `BH`, whose absolute value is at least two, therefore gives
`x>=0` and `q=(BH)^x`.

The last endpoint

\[
 x=1+\bigl(1+(t+1)y\bigr)u_t
\]

excludes `x=0`, because the positive coefficient `1+(t+1)y` is
greater than one and cannot divide `-1`. Thus `x>=1`. In the first
endpoint

\[
 x=F+1+(y+1)u_0,
\]

an integer `u_0<=-1` would imply `x<=F-y<0`. Hence `u_0>=0` and
`x>=F+1`. The last endpoint then has `u_t>=1`, yielding

\[
 x\ge2+(t+1)y\ge2+(t+1)F^2.
\]

All these estimates are at least as strong as the corresponding
parent estimates, which required only `y>=F`. Consequently the
same independent centered-remainder argument recovers the true
positive binomial digit `B=binom(F^2+t,t)`. The generalized binomial
CRT lemma recovers every local row, with its inherited strict
majorant and range bounds.

The initial beta remainder `F+1` is already strictly less than
`y+1`. It therefore represents the actual first state, and the last
state is one. In particular, the parent's separate `y=F` zero-path
contradiction is no longer needed. The positive-accumulator product,
large-evaluation multiplicity recovery, and finite Horn-closure
argument apply exactly as before.

The proof does not need to show that a new zero extends to the
old two-equation beta block. Such an extension generally does not
exist, because `y/F` need not be an odd square. What is preserved is
the equivalence between solvability and a finite C222 refutation.

## 3. Constructive completeness

Start from a finite C222 refutation. Choose a permitted padded horizon
`t=16+h^2`, define the same `F`, and compute the finite positive
pending-multiset accumulator path. Its weights and all its states
are determined before choosing `y`.

Apply the lemma with a bound exceeding every state and `F+1`.
The resulting `y` is a positive even multiple of `t!`. The beta
moduli `1+(i+1)y`, for `0<=i<=t`, are pairwise coprime: a prime
common to two distinct moduli divides their index difference,
is at most `t`, and consequently divides `y`, contrary to its
dividing `1+(i+1)y`. Each desired state is a proper remainder.
The beta CRT therefore supplies an integer code `x`, which can
be chosen arbitrarily large and even, since the product of these
odd moduli is odd. All old lower bounds and strict quotient
requirements are obtained by taking a sufficiently large such code.

Now define `N=B^x` and perform the parent's generalized binomial
CRT at every prime power of `B`. Its parity argument is unchanged:
`B` is odd because `v_2(F^2)>floor(log_2 t)`; adding the odd
precision modulus changes the parity of a representative while
preserving its arithmetic data. Choose the same even dominant
semantic anchor and odd `H` as in the parent. Then `q=(BH)^x`
is an odd square and supplies the retained radix row. All
remaining Pell witnesses, normalized remainders, and norm slacks
exist by the unchanged constructive arguments.

This proves completeness. Both directions use only finite
arithmetic arguments formalizable in ZFC. Composing with the
retained C222/ZF and ZF/ZFC refutation calibrations gives the
desired equivalence with `Con(ZFC)` for the new ordinary polynomial.

## 4. Exact finite interface and metrics

The supplied generator takes the parent's *principal* equation,
with 242 integer variables and 178 residuals. In that final chart,
the semantic `y` is stored coordinate 2 minus one, `F` is
coordinate 3, and `R=F^2` is coordinate 4. The two private beta
witnesses are coordinates 240 and 241. The exact changes are:

* replace residual 173,
  `-1+x_2-x_3*x_240`, with
  `-1+x_2-x_4-x_240^2-x_241^2`;
* delete residual 177,
  `-1+x_240-4*x_241-4*x_241^2`;
* rename the two private witness slots to `beta.square_u` and
  `beta.square_v`.

All remaining residuals and coordinates are unchanged. The
generator verifies that the two witnesses occur nowhere else,
and verifies the retained residual `x_4-x_3^2` literally. The
parent's final shear/projection/row certificate leaves these
two residuals untouched; its earlier projector retains both
beta rows and uses no beta witness as a projection target.

The resulting sum of squares has 242 integer variables, 177
quadratic residuals, exact degree four, 5,017 collected monomials,
coefficient height 7,968, and residual coefficient height 64.
Against the matching parent, it saves one residual and one
collected monomial without changing dimension or height.

The code constructs and checks 195 exact CRT witnesses across
the horizons 16 through 80. These checks illustrate the
construction; the proof above is unbounded and does not rely
on their finite scope. No new Lean/Rocq formalization, globally
minimal equation, or literature-wide priority claim is made.
