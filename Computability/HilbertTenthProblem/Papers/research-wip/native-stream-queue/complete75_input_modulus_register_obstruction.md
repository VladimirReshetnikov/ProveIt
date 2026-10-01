# Reusing the projection modulus empties the 87-operation compiler

Replacing the input-index modulus Delta by the already paid H=4a+3 in
[normalized87](complete75_normalized_strong87.md) leaves the literal cost
at **87=48M+39A**, with nineteen positive witnesses, and lowers the
formal polynomial degree from203 to187. Nevertheless, the resulting
polynomial has **no positive zeros on a valid compiler slice**. The
smaller degree is therefore not a new universal bound.

The [source](complete75_input_modulus_register_obstruction.py) and
[receipt](complete75_input_modulus_register_obstruction.json) preserve this
specific rejected substitution. They also audit eight other already paid
moduli and a necessary modulo-eight restriction for those variants.
The original75/87 sources and all fixed compiler numerals are unchanged.
This packet does not rule out other input bridges or variable-modulus
counting constructions.

## 1. Exact modification and inherited sign recovery

Use the full normalized87 compiler contract, including both ratio slacks,
the fixed masks and retained raw bound. Write

    q=(B−1)J+1, X=wq^3, Y=sq^3, a=Y(X+1),
    A=a+2, Delta=A^2−1=a^2+H, H=4a+3,
    C=q−F−Z−alpha−2dx, W=C−Z, u=2dx+b,
    D=X+ac+(rho+sigma)H.

Here c is the main Pell ordinate. The source register named `A` contains
Delta; mathematical A denotes its Pell parameter. The fixed inner offset
b is positive and odd, b<B, and d>=4. All supplied coordinates and the
ordinary input x are strictly positive integers.

For a chosen already paid positive register M replace just

    kappa=u+delta*Delta       by       kappa=u+delta*M.     (1)

Keep mu=W+a*kappa+rho*H and the input factor

    N_input=mu^2−Delta*kappa^2.

No other factor or gate definition changes. The complete source still
has eight integer factors whose product is1 at a zero. The input factor
cannot equal−1 modulo4 because Delta is0 or3 modulo4. The same is true
of the normalized strong factor. Its positive change i_old=Delta*i
restores the full old strong block, as in normalized87.

The inherited coupled proof up through main-kernel restoration uses the
input norm only to recover its positive unit sign; it does not use the
old definition of kappa. The detailed dependency argument is also given
in [the linear-modulus proof, Sections2–3](complete75_linear_input_modulus89.md).
All listed M are positive expressions on the original positive grid.
Thus the complete sign, rank, ratio and packing arguments give

    q=2^t>=16, R>=q^2, X=2^R,
    c=psi_A(R), D=chi_A(R),
    0<C<q, -q<W<q, 3<=u<2q<R, a>q^6.                    (2)

Both the raw bound and the actual masks are retained. No input index or
End-marker interpretation is assumed in obtaining these conclusions.

## 2. The projection already forces W to be a genuine power

The new kappa is positive. Since W>−q and a>q, its computed root satisfies
mu>−q+a>0. The input norm therefore gives an integer v>=1 with

    kappa=psi_A(v), mu=chi_A(v).

Set E_A(j)=chi_A(j)−(A−2)psi_A(j). Its initial values1,2 and recurrence
E_A(j+1)=2A E_A(j)−E_A(j−1) make it strictly increasing. The two retained
projection identities and W<q<X give

    E_A(v)=W+rho*H < X+(rho+sigma)H=E_A(R).

Hence v<R, independently of(1)'s modulus. The projection recurrence gives

    E_A(v)=2^v modulo H.                                (3)

For completeness, multiply the E recurrence by4 and reduce modulo
H=4A−5: if the two preceding terms are2^j and2^(j−1), then
4E_A(j+1)=10*2^j−4*2^(j−1)=4*2^(j+1) modulo H.
H is odd, so4 is invertible; the initial terms establish(3).

Since0<2^v<X<a and−q<W<q, the congruence W=2^v modulo H lifts uniquely:
a positive added multiple of H gives W>q, while a negative one gives
W<a−H<−q. Consequently

    W=2^v,        2<=W<q.                              (4)

This conclusion does not use kappa=u modulo Delta, does not require v
to be odd, and does not assume that a decoded history already has its
intended input. It is an arithmetic consequence of the retained norms,
projections, dominance and bounds.

## 3. The H-modulus variant has no positive zero

Take M=H in(1), so kappa=u modulo H. Modulo H the norm becomes

    W^2+2aW*kappa=1,

because mu=W+a*kappa modulo H and Delta=a^2 modulo H. Multiplying by4
and using4a=−3 modulo H gives the exact divisibility

    H divides T=4W^2−6Wu−4.                            (5)

Do not infer T=0 from divisibility alone. By (2),(4),

    |T| < 16q^2+4 < 4q^6 < H.                         (6)

The middle strict inequality holds for q>=16. Therefore T=0. Dividing
this integer equality by2 and rearranging yields

    W(2W−3u)=2.

The positive power W>=2 must be2. Then4−3u=1, so u=1, contrary to
u>=3. This contradiction proves the empty-slice assertion. There is no
missing parity branch or large congruence multiple. In particular it is
not merely a failed attempt to reproduce canonical witnesses.

## 4. Eight dyadic-divisible moduli have a separate necessary restriction

The checker also substitutes each of

    M=q, q^2, q^3, X, Y, XY, a, 4a.                    (7)

At a positive zero the inherited typing makes every listed M divisible
by8, because q is a power of two at least16. A=a+2 is even. Equation(1)
therefore gives kappa=u modulo8, with u odd. For even A, Pell recurrence
modulo2 shows psi_A(v) is odd exactly when v is odd. The odd subsequence
modulo8 satisfies

    psi_A(2j+1)=(-1)^j modulo8.                        (8)

Indeed its first two values are1 and4A^2−1=−1 modulo8, and its recurrence
has coefficient4A^2−2=−2 modulo8. Thus every positive zero of a variant
in(7) necessarily has

    u=2dx+b in {1,7} modulo8.                          (9)

Inputs with u=3 or5 modulo8 are excluded. This conclusion is stated in
terms of d,b: it does not assume an arbitrary compiler width is odd.
If d and b are both odd, precisely two input classes modulo4 violate(9).
The standard reviewed [modified compiler recipe](complete75_half_binomial_compiler.md)
chooses b,L,d as powers of five, so this extra hypothesis holds for that
recipe. Those slices cannot represent all positive integers. An alternative
even-width recipe can avoid these particular input residues; this packet
does not claim a general nonuniversality theorem for every such recipe.
The unconditional H-modulus empty-slice result is separate.

## 5. Exact source corrections and formal degrees

Let kappa_0,mu_0 be the original normalized87 expressions and put

    e=delta*(M−Delta).

On every integer assignment, including signed assignments,

    kappa_M=kappa_0+e,    mu_M=mu_0+a*e,
    N_M−N_0=2e*(a*mu_0−Delta*kappa_0)−H*e^2.             (10)

Every other factor is identical. Multiplying(10) by their product gives
the exact complete-polynomial correction without division by a factor.
This is an algebraic audit, not a map between positive zero sets.

All nine sources change only the already paid `index_product` gate,
from delta*Delta to delta*M. Each retains86 certificate gates, one
comparison and the same final subtraction:87=48M+39A. Complete dependency
closure is checked; no old gate becomes dead. The following are degrees
of these rejected or restricted polynomials, not universal bounds:

| Input modulus | Input factor degree | Complete polynomial degree |
|---|---:|---:|
|H|26|187|
|q|19|180|
|q^2|20|181|
|q^3|21|182|
|X or Y|22|183|
|XY, a or4a|26|187|

To verify the changed degree, put r=W+rho*H. The exact cancellation is

    N_input=r^2+2a*kappa*r−H*kappa^2.

The highest forms of a,H,r have degrees8,8,9. For M=H, the highest form
of kappa is4*delta*a_top, so the input factor has nonzero degree26 form

    32*delta*(rho−2delta)*a_top^3.

For M=XY or a the corresponding form is
4*delta*(2rho−delta)*a_top^3; for M=4a it is the H form. For the remaining
choices, kappa has degree2,3,4 or5 and the term2a*kappa*r uniquely has
highest degree19,20,21 or22. The seven unchanged factors have total
exact degree161 by the parent proof, so the table follows for every
admissible fixed B. Weighted polynomial fixtures corroborate these
highest-form calculations, without substituting zero-set equalities.

## 6. Reproduction and scope

Run `python3 complete75_input_modulus_register_obstruction.py`; `--write`
regenerates the receipt. The source checker tests576 complete factor and
polynomial correction identities, including288 signed assignments, over
all nine substitutions. Eighteen weighted/offset univariate evaluations
check every factor degree and the total degrees. Exact symbolic checks
prove the norm congruence and correction identities.

Finite Pell recurrence checks verify the projection congruence and norm
congruence at3108 parameter/index pairs, with1554 even-parameter
parity/modulo-eight cases. Necessary-domain boxes check the strict
no-wrap estimate, and sixteen odd-width/offset fixtures record the two
excluded input classes. These are algebraic and necessary-condition
fixtures, not complete positive Pell/compiler zeros.

The established75 comparison bound and87-operation universal polynomial
are unchanged. This obstruction is separate from both the refuted
weakened-bound86 proposal and the multiplicative-gamma shortcut.
The author writer and separate fresh replay pass. Root independently read
the full proof and source, checked the inherited dependencies and exact
leading forms, and passed a fresh default replay. Gibbs independently
reviewed the full proof/source/dependencies and passed a fresh replay,
with no findings. His separate executor checked432 complete source,
factor and output corrections, including216 signed assignments. A
matrix-power oracle checked3296 projection/norm pairs through index
10^12+1, including1792 even-parameter parity cases; separate checks
covered300 no-wrap endpoints,160 odd-width residue slices and12865 lift
candidates. All five local links resolve. These independent checks have
the same algebraic and necessary-condition scope as the author fixtures;
they do not assert full positive compiler zeros.
