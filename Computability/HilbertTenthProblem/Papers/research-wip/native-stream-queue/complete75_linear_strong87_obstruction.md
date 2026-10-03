# A local obstruction to replacing the strong parameter by `ic`

This note rejects an inherited **auxiliary rank and index lemma**, not a
complete polynomial candidate. Replacing `t=ic^2` by `t=ic` in
[normalized strong87](complete75_normalized_strong87.md) admits positive
local auxiliary solutions with the wrong main index. No full polynomial
zero, false accepted input, or failure of universality is established.
The proved 75-operation certificate and 87-operation polynomial remain
unchanged.

## 1. The proposed local change

Write `A=a+2`, `Delta=A^2-1`, and use the Pell conventions

\[
 (A+\sqrt\Delta)^n=\chi_A(n)+\psi_A(n)\sqrt\Delta.
\]

The parent computes

\[
 t=ic^2,\quad Q=\Delta t^2,\quad K=\Delta^2t^2,
 \quad N_s=f^2-Q,\quad N_3=K(V^2-y^2)+y^2,
 \quad V=of-c.
\]

The candidate changes only `t=ic^2` to `t=ic`. In the literal Python
source this is the single row `ic2 = i * R10a`, where `R10a` is `c`.
The main `c^2` register remains live elsewhere. Thus this substitution
alone retains **87 operations = 48 multiplications + 39 additions** and
19 positive witnesses; it does not save an operation. Its candidate
degree is 183, with factor degrees
`(14,22,42,54,9,5,28,9)`. These are circuit facts, not a new universal
degree bound.

## 2. A positive local family

Choose any integer `A>=3` and `p>=7` with `p=3 mod4`. Set

\[
 \begin{aligned}
 f&=\chi_A(p),&c&=\psi_A(p),&i&=1,\\
 R&=5p,&T&=\Delta c,&\ell&=5p,\\
 y&=\psi_T(\ell),&V&=\chi_T(\ell)/T,\\
 o&=(V+c)/f,&j&=(V+R)/c.
 \end{aligned}                                                     \tag{1}
\]

All these quantities are positive integers. They satisfy exactly

\[
 \begin{aligned}
 f^2-\Delta c^2&=1,\\
 T^2(V^2-y^2)+y^2&=1,\\
 V&=of-c=jc-R,
 \end{aligned}                                                     \tag{2}
\]

while **the main Pell index is `p`, not `R=5p`**. The family also retains
the substantial local size margins

\[
 c>A\Delta^2,\qquad c>2R>2p,\qquad f>2c.             \tag{3}
\]

For the integrality assertion, write `ell=2v+1`; here `v` is odd. The
odd Chebyshev quotient is an integer polynomial

\[
 \chi_T(\ell)/T=Q_v(T^2),\qquad
 Q_v(0)=(-1)^v\ell,\qquad
 Q_v(1-A^2)=(-1)^v\psi_A(\ell).
\]

Since `c|T`, the first identity gives `V=-R mod c`, proving that `j`
is integral. Also

\[
 T^2=\Delta^2c^2\equiv-\Delta=1-A^2\pmod f.
\]

Expanding the fifth power of `f+c sqrt(Delta)` gives

\[
 \psi_A(5p)=5f^4c+10f^2c^3\Delta+c^5\Delta^2
            \equiv c\pmod f,
\]

because `Delta*c^2=f^2-1`. The second quotient identity therefore gives
`V=-c mod f`, proving integrality of `o`. Positivity follows directly
from (1). The ordinary Pell identities give (2).

Finally, `psi_A(p)>(2A-1)^(p-1)`: the positive Pell recurrence increases
by a factor greater than `2A-1` at each step after its initial value.
Consequently

\[
 c>(2A-1)^6>A^6>A\Delta^2,
 \qquad c>5^{p-1}>10p=2R.
\]

The identity `f^2=1+Delta*c^2`, with `Delta>=8`, gives `f>2c`.

## 3. What the family obstructs

The new strong equation allows its positive auxiliary Pell index to be
`m=p`. Since `c>p`, the inherited conclusions `c|m`, `m>=c`, and
`m>2p` are false for this local system. The simultaneous auxiliary
congruences and the size margins (3) do not repair the problem: (2)
explicitly realizes the incorrect recovered index `R=5p`.

Nor does the parent's coordinate embedding survive. Keeping the same
`A,c,f` in normalized strong87 would require `i_old=1/c`. Keeping the
same tuple in its coupled88 parent would require
`i_88=Delta/c`. Neither is a positive integer; indeed `c>Delta`.
This rules out those particular restoration maps, not every possible
replacement proof or reconstruction.

The construction imposes neither the full first norm and index factor
nor the two ratio slacks, packed compiler fields, input norm, or input
transport. It also does not identify independent `A,c` in (1) with all
their computed main-source definitions. In particular it supplies no
full zero of the modified eight-factor polynomial. A proof using the
remaining equations might still exclude these local configurations.

This obstruction is distinct from the unresolved
[weakened-bound86 candidate](complete75_weakened_bound86_candidate.md),
which changes an outer positivity bound, and the
[independent-gamma87 period analysis](complete75_independent_gamma87_period.md),
which concerns a different input-modulus parameterization.

## 4. Bounded checks

Exact integer Pell evaluation checked all **21** cases
`A=3,...,9`, `p in {7,11,15}`. Each case passed integrality and strict
positivity of every quantity in (1), both norms and both expressions
for `V` in (2), all margins (3), and `p!=R`. The general argument above
does not depend on this finite sample.

Separately, 128 positive/signed literal-source assignments checked the
changed factors and complete output against their direct scalar
formulas. A weighted univariate source evaluation attained the eight
factor degrees recorded in Section 1 and total degree 183; the
corresponding formal degree bounds agree. These are arithmetic circuit
checks and local Pell solutions only. No full positive candidate zero
was tested or claimed. No new universal operation or degree bound
follows from this note.
