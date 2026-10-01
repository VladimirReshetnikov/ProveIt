# Arbitrary local targets for the linear-strength87 candidate

The first-norm lower bound on the main Pell index does not, by itself,
repair the [linear strong auxiliary lemma](complete75_linear_strong87_obstruction.md).
After replacing `t=ic^2` by `t=ic`, the auxiliary system can encode
**every positive target** in the family below. In particular it admits
the wrong target R=p+4 while retaining the preliminary inequalities
`n<p<2n` and the exact representative `2n=R+1`.

This is a local theorem. It does **not** give a full positive zero of
the modified87 polynomial, disprove its universality, or establish its
soundness. The retained first Pell norm, common ratio definitions and
complete outer/input system remain essential unresolved conditions.
The established [normalized strong87](complete75_normalized_strong87.md)
with `t=ic^2` is unchanged.

## 1. An exact arbitrary-target auxiliary construction

Use

\[
 (A+\sqrt\Delta)^r=\chi_A(r)+\psi_A(r)\sqrt\Delta,
 \qquad \Delta=A^2-1.
\]

Fix integers p>=3, p=3 modulo4, and A>=3 divisible by p. Put

\[
 c=\psi_A(p),\qquad f=\chi_A(p),\qquad i=1,
 \qquad T=\Delta c.                                  \tag{1}
\]

For **any positive integer target J**, there are positive integers
y,V,o,j satisfying

\[
\begin{aligned}
 f^2-\Delta(ic)^2&=1,\\
 T^2(V^2-y^2)+y^2&=1,\\
 V&=of-c=jc-J.                                       \tag{2}
\end{aligned}
\]

The first factor in (2) is exactly the proposed linear-strength norm,
and its auxiliary coefficient is `T^2=Delta^2*(ic)^2`.

Here is a construction without any search over Pell solutions. The
recurrence `psi_A(r+1)=2A*psi_A(r)-psi_A(r-1)` gives

\[
 c\text{ odd},\qquad c\equiv-1\pmod p,
 \qquad \gcd(4p,c)=1.                               \tag{3}
\]

For the second congruence, reduce A modulo p: the recurrence alternates
between zero and signed one, and p=3 modulo4 selects minus one. Thus
there is a unique u in `[0,c-1]` satisfying

\[
 4pu\equiv J-p\pmod c.
\]

Define

\[
 \ell=(4u+1)p,\quad y=\psi_T(\ell),\quad
 V=\chi_T(\ell)/T,\quad
 j=(V+J)/c,\quad o=(V+c)/f.                          \tag{4}
\]

We prove that all divisions in (4) are integral. The first is integral
because ell is odd. Write ell=2v+1. The odd Chebyshev quotient is an
integer polynomial Q_v in T^2, with

\[
 Q_0(S)=1,\quad Q_1(S)=4S-3,\quad
 Q_{v+1}(S)=(4S-2)Q_v(S)-Q_{v-1}(S).
\]

Its two relevant evaluations are

\[
 Q_v(0)=(-1)^v(2v+1),\qquad
 Q_v(1-A^2)=(-1)^v\psi_A(2v+1).                    \tag{5}
\]

Both follow by the displayed recurrence and its first two values; for
the second, the odd-index Pell subsequence has recurrence coefficient
`4A^2-2`, and multiplying its v-th term by `(-1)^v` changes that
coefficient to `2-4A^2`.

Our ell is3 modulo4, so v is odd. Since c divides T and ell=J modulo c,
the first identity in (5) gives

\[
 V\equiv-\ell\equiv-J\pmod c.                      \tag{6}
\]

Also `Delta*c^2=f^2-1`, so

\[
 T^2=\Delta^2c^2\equiv-\Delta=1-A^2\pmod f.
\]

In the quadratic integer ring reduced modulo f, the element
`f+c*sqrt(Delta)` squares to minus one. Its `(4u+1)`-st power therefore
has the same square-root coefficient c. By Pell composition,

\[
 \psi_A(\ell)=\psi_A((4u+1)p)\equiv c\pmod f.
\]

The second identity in (5) now gives

\[
 V\equiv-\psi_A(\ell)\equiv-c\pmod f.              \tag{7}
\]

Equations (6)–(7) prove the remaining two integrality claims. All
quantities are strictly positive. In fact ell>=p>=3 and T>=8c, so
`V>=chi_T(3)/T=4T^2-3>c`. Also `f^2=1+Delta*c^2` gives f>2c.
The ordinary Pell identities at A and T establish both norms in (2).
No inverse of T modulo c or f is assumed anywhere.

## 2. Nearby wrong targets survive the preliminary index bounds

Take p>=7 in the same residue class and set

\[
 R=J=p+4,\qquad n=(p+5)/2.                          \tag{8}
\]

Then

\[
 2n=R+1,\qquad n<p<2n,\qquad
 p\ge(R-1)/2,\qquad p\ne R,\qquad R\equiv3\pmod4.  \tag{9}
\]

The construction in Section1 realizes this J with auxiliary Pell
index m=p and i=1. The usual local growth margins are also retained:

\[
 c>A\Delta^2,\qquad c>2(R+2),\qquad c>2p,
 \qquad f>2c.                                      \tag{10}
\]

Indeed `psi_A(p)>(2A-1)^(p-1)`. With p>=7 and A>=3, this exceeds
`A^6>A*Delta^2`; it also exceeds `5^(p-1)>2p+12=2(R+2)`.

The full first norm in the complete source gives
`k=2*psi_(2XY^2+1)(n)`, and its index equation implies the preliminary
bound `n>=(R-1)/2`. Thus it does exclude the earlier particular
local family R=5p. But the index consequences (9), including the
positive-sign exact representative `2n=R+1`, do not exclude (8).
The same applies to a proof that additionally establishes p<2n from
the upper ratio.

This is a failure of that proposed local repair, not a counterexample
to the first norm itself. We have not made the n in (8) its actual
index at common X,Y, or shown that the two strict ratio slacks can
coexist with that norm and the computed main definitions.

## 3. What is still required for a full-system answer

The literal87 candidate changes one row from `ic2=i*c2` to `ic2=i*c`.
Its48 multiplications,39 additions/subtractions and19 positive witnesses
are unchanged. The previously checked degree183 is a circuit fact,
not an established universal degree bound.

In the full source, A and c are not independent inputs: with
`X=wq^3`, `Y=sq^3`, `E=XY`, one has `A=Y(X+1)+2` and
`c=kY+eta`, `k=eta+zeta`, with eta,zeta>0. The main Pell root is also
the computed expression `X+(A-2)c+(rho+sigma)(4A-5)`.
Section1 does not impose these simultaneous requirements. It likewise
does not impose the first norm, packed compiler R, weak transport,
ordinary-input norm, or the input-modulus restrictions.

Consequently a proof of full candidate soundness could still use those
additional equations. Conversely a full obstruction must satisfy them,
rather than promote the auxiliary CRT family to a false accepted input.
The exact remaining issue is whether they exclude the nearby target
freedom exhibited here. This packet does not resolve it.

## 4. Bounded exact checks

The [checker](complete75_linear_strong87_target_crt.py) and
[receipt](complete75_linear_strong87_target_crt.json) verify288 parameter
and target choices, with p=3,7,...,47 and four positive multiples of p
as A. They check both divisibilities in (3), the exact CRT solution,
and (6)–(7) by independent modular Pell powering. Forty-four nearby
target cases also check every inequality in (9)–(10).

The large auxiliary words are not expanded. To compute
`chi_T(ell)/T modulo M`, the checker computes `chi_T(ell) modulo T*M`,
verifies the residue is divisible by T, and divides that bounded
residue. Since the exact quotient is integral, this gives precisely
its residue modulo M, without requiring T to be invertible modulo M.

Twelve small p=3 families are fully materialized, checking positivity,
both norms and both equalities for V. They test the auxiliary theorem;
they are not instances of the p>=7 nearby-target inequalities or full
compiler zeros. A literal source guard confirms that the proposed
candidate still has87 operations and changes only the stated operand.
The existing parent files and established universal87 theorem are not
modified.

Author writer and fresh default replay passed; all local links resolve.
Root's independent full proof/source/fresh-default review passed without
findings. The packet is frozen with the local/full-system distinction
above unchanged.

```sh
python3 complete75_linear_strong87_target_crt.py
```
