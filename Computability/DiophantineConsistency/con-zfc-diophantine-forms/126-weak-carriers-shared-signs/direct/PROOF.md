# Deferred signs in the direct factorial-carrier certificate

This note proves the new arithmetic transformation. Its fixed input is the
round-14 derived-label, square-shell source in the archive
`ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24.zip`, inspected
at ProveIt commit `45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6`.
The input is its full `direct/derived16_factored_shell/factored_source.json`.
Its known projected, centered endpoint has 517 integer variables and 310 rows.
The transformation below gives a quartic in 478 unrestricted integer variables,
305 rows, 5,484 collected monomials and coefficient height 511,326.
The inherited calculus and the factorial/CRT theorem remain explicit
dependencies; no end-to-end proof-assistant certification is asserted.

## 1. The exact interface and the domain changes

Use the source's semantic notation, whose meanings will be recovered in the
order proved below:

* `t=t0+16`, with `t0>=0`; `x>=0`; `F=fact0.output`.
* `y=F+endpoint.r0+1`, with `endpoint.r0>=0`.
* `rho=F*t^2`, the proposed `V=(rho+1)^t`.
* `D=choose0.output`, `B=choose1.output`, `N=B^K`, and
  `q=N(N+V+1)^K`, with `K=2(2+t+x+y+F)`.
* The exact ceiling rows are `D=r+s+1` and `D*F=V+s`, where
  `(r,s)=(fact0.remainder,fact0.slack)`.
* The exact output bounds are `q=D+o0+1` and `q=B+o1+1`, with
  `o0=choose0.oslack`, `o1=choose1.oslack`.
* The reciprocal index row is `B*i=C+F^2+1`, where
  `C=crt.encoded_index_minus_one+1>=1`.

The changes are literal:

1. Strengthen the existing guard `F>=0` to `F>=1`. It still costs three
   integer witnesses. Genuine source certificates have `F=t!>=1`.
2. Replace each of fourteen pairs of nonnegative scalar guards by the
   nonnegativity of their product. The pairs are the factorial `(r,s)`,
   `(B,o1)`, both binomial remainder/slack pairs, and all ten range
   remainder/slack pairs. The separate guard `o0>=0` remains.
3. Replace `A>=0`, `Zminus1>=0` and `v>=0` for the common ordinate
   quotient `v=shared_index.Vquotient_minus1` by one quadratic gate
   `u=(v+1)^2` and one guard `(A-1)u-1>=0`. This couples the frame
   orientation with nonvanishing of the shared auxiliary ordinate.
4. Remove the sign guard on the comparison-base multiplier
   `shared_index.q4minus1`. The comparison base may have either sign.
   All seed guards `Y_i>=k_i` remain. The common auxiliary ordinate may
   have either sign and is forced nonzero by item 3.
5. Use a mixed linear/square common frame. If an affine power atom `a`
   is already proved nonnegative using retained scalar guards and exact
   monotone polynomial rows, its contribution to `W` is `a`. Every other
   atom contributes `a^2`. The frame is `W=2+sum(contributions)`.

No proposed power is used in the sign inference for item 5. The original
frame row is excluded from that inference, so it cannot justify itself.
All proof steps and the precise atom list are included in the budget
certificate. The list is inherited, byte for byte, from the source's
power interface.

The universal guard used throughout is

    Q(a,b,c)=a^2+b^2+c(c+1).

For integer arguments Q is nonnegative. Conversely every nonnegative
integer n is Q(a,b,c): the three-square theorem applies to 4n+1, and
exactly one of its three squares is odd. The substitution of that odd
square `(2c+1)^2` proves the formula. Thus the single quadratic row
`r*s-Q(a,b,c)=0` expresses exactly `r*s>=0`, with no hidden domain.

## 2. The common frame before any powers are interpreted

For every integer a, `a^2>=|a|`. A proved nonnegative atom contributes
`a=|a|`. Every contribution is nonnegative, so

    W>=2 and |a|<W for every listed power base, exponent and output.

The coupled guard has the exact quadratic presentation

    u=(v+1)^2,
    (A-1)u-1 = alpha^2+beta^2+gamma(gamma+1).

Its right side is nonnegative. Therefore `(A-1)u>=1`, which forces
`u>=1`, `v+1!=0` and A>=2. Conversely any integers A>=2 and v!=-1
make the left side nonnegative and hence admit the three-square witnesses.
The actual first power base `F*t^2+1` is independently at least two,
because F>=1 and t>=16.

Write `Z=Zminus1+1`, now an arbitrary integer. The unchanged frame norm is

    A^2-W^3(W+2)Z^2=1.

As A>=2, Z is nonzero. This is the Pell equation with base W+1 and
ordinate WZ. For `chi_b(h)+psi_b(h)*sqrt(b^2-1)=(b+sqrt(b^2-1))^h`,
classification of the integer Pell solutions gives

    A=chi_(W+1)(h), |WZ|=psi_(W+1)(h), h>=1.

Reduction of the recurrence modulo W gives `psi_(W+1)(h)=h (mod W)`,
so W divides h and h>=W. Consequently `A>W^W` and in fact
`A>=(W+1)^W`. For every positive base n<W the modulus

    T_n=2*A*n-n^2-1

is positive and exceeds `W^W+W`. One elementary bound is
`T_n>=2A-2`; the quadratic is increasing on `[1,W-1]`, since A>W.
The binomial expansion gives `(W+1)^W>=2W^W`, which proves the claimed
strict margin for all W>=2. Thus all usual forward and inverse power
residue estimates remain valid. No sign of a power output was used.

## 3. Removing the comparison-base sign

Write Vaux for the shared auxiliary Pell ordinate, to distinguish it from
the factorial power V. Every prescribed seed exponent k_i is positive
before power interpretation: this is the inherited compositional index
certificate, whose inputs `t0,x,F,endpoint.r0` and the encoded representatives
retain their nonnegative guards. Strengthening F is harmless. The retained
seed rows and guards give `Y_i>=k_i>=1`. The literal product row

    Vaux=(product_i Y_i^2)*(v+1)

therefore gives Vaux!=0, since the coupled guard proves v+1!=0. The norm
`U^2-(A^2-1)*Vaux^2=1` yields
`|U|=chi_A(h)`, `|Vaux|=psi_A(h)` for an index h>=1.

The comparison base b satisfies the unchanged exact equations

    b=1+4*Vaux*(q4+1),    b=A (mod U).

Although q4 and Vaux may now have either sign, b is 1 modulo four.
It cannot be 1, because `|U|>=A>A-1`. The congruence modulo four already
excludes b=-1, b=0 and b=2; hence |b|>=3. The squared divisibility
arguments below apply to |Vaux| without changing their conclusions.

The signed comparison-base indexed-Pell theorem is already proved in the
incoming quadratic-frames package, in
`direct/source/signed_comparison_base_proof.md` and
`signed_comparison_index_proof.md`. This sign lemma is credited to that
source. Its application to the new stronger carrier is part of the present
composition. For clarity, its essential argument is repeated here.

Every signed solution at b has form
`S=epsilon*chi_b(j), R=delta*psi_b(j)`, with independent signs. Polynomial
dependence on b transfers the abscissa congruence to base A. The main norm,
Y_i>0, squared divisibility `Y_i^2 | Vaux`, and the abscissa congruence give
`j=+/-i (mod 2h)` and `Y_i | h`. The base-one congruence
`b=1 (mod 4Y_i)` and the ordinate congruence give
`j=+/-k_i (mod 4Y_i)`. Thus `i=+/-k_i (mod 2Y_i)`. Both i and k_i lie
in `[1,Y_i]`; the positive alternative gives i=k_i, and the negative
alternative can only attain the common endpoint i=k_i=Y_i. Therefore

    |X_i|=chi_A(k_i), Y_i=psi_A(k_i).

Independent signs of b,S,R,U introduce no extra arithmetic solutions.

## 4. The earlier factorial bootstrap

For a request `m=n^k` at a positive base, the unchanged power row is

    X+(n-A)Y=m+T_n*u.

At its indexed pair, positive X gives `m=n^k (mod T_n)`. Negative X
gives `m*n^k=-1 (mod T_n)` by multiplication by the conjugate and the
Pell norm. The frame bounds give both `|m-n^k|<T_n` and
`|m*n^k+1|<T_n`. Thus negative X is impossible when n>=2, and positive X
gives the exact equality. This remains true when m has no sign guard.

Apply this first to `n=F*t^2+1`, `k=t`. The base is at least two before
q is interpreted. It follows that

    V=(F*t^2+1)^t > F.

The strict inequality also holds at the edge F=t=1, although the actual
derived-label horizon is at least 16. This is the change that unlocks the
factorial guard fusion.

The product guard gives rs>=0. If either r or s were negative, both would
be nonpositive. Eliminating D from the two ceiling rows gives

    V=F*r+(F-1)*s+F <= F,

since F>=1. This contradicts V>F. Therefore r,s>=0, D=r+s+1>=1, and the
retained guard o0>=0 yields q=D+o0+1>=2. This argument uses neither the
factorial meaning of F nor the binomial meaning of D.

Now `(B,o1)` has nonnegative product and positive sum `q-1`. For any
real/integer a,b, `ab>=0` and `a+b>0` imply a,b>=0. The reciprocal index
row `B*i=C+F^2+1>0` excludes B=0. Thus B>=1 and o1>=0 before K-indexed
power recovery.

For the request `N=B^K`, positive X gives N=B^K. The only remaining
negative-X alternative has B=1 and N=-1. In either case the second base
`N+V+1` is at least two, since V>=2. Its request therefore orients the
shared K pair and excludes that alternative. All K requests are now true.
Every other seed has a request at q or q+1, both at least two; these orient
the remaining pairs. The derived t+1 pair is recovered from the unchanged
Pell addition identity after the t pair. All nineteen original powers are
therefore true at the original front coordinates.

## 5. Recovering the delayed signs

Each remaining product guard has an unchanged sum equation

    r_j+s_j=q^(ell_j)-1.

For the two binomial extractions ell_j=t; for the ten range extractions
it is t, t+1, x+1, or y+1, as literally recorded by the source. All these
exponents are positive. Since q>=2, the sum is strictly positive. The
elementary product/sum implication therefore restores r_j,s_j>=0 for all
twelve pairs. No digit, binomial, factorial, or CRT theorem was used to
restore these signs; only the already recovered powers were used.

All original semantic front signs have now been restored. The inherited
ordered self-bounding factorial, digit, reciprocal prime-power CRT,
derived-label bound and pairwise-coprime Horn-flow proofs apply unchanged.
They recover a finite C222 refutation and hence a finite ZFC refutation.
The unchanged signed Horn factorization is an exact polynomial identity,
so this step does not require signs for its internal product coordinates.

## 6. Completeness and the exact equivalence asserted

Given a finite C222 refutation, use the inherited source completeness
construction to choose its front arithmetic certificate. In particular
F=t!>=1, all fourteen pairs consist of nonnegative integers, and all
nineteen true powers hold. Construct the new mixed frame from these
front coordinates, then set `A=chi_(W+1)(W)` and
`Z=psi_(W+1)(W)/W`. The division is integral by the recurrence modulo W.
The new coupled predicate is true when the common positive auxiliary
Pell witnesses are chosen below.

For each seed choose the positive pair at its actual index. Choose a common
Pell iterate whose ordinate is divisible by the product of all Y_i^2,
using the order of a unit in the corresponding finite quadratic ring.
This canonical choice gives v>=0, so `(A-1)(v+1)^2-1>=0`.
Ordinary CRT then chooses a positive comparison base satisfying both
shared congruences. Such a positive choice is still permitted when its
sign guard is omitted. Fill the comparison pairs, power congruence
quotients, derived pair and all polynomial gates. Supply three-square
witnesses for every remaining scalar and product predicate. This gives
a zero of the new full quadratic system.

Alternatively, to compare directly with a zero of the old guarded source,
first invoke its inherited arithmetic soundness to identify its semantic
front, and rebuild fresh auxiliary Pell coordinates as above. In the
other direction rebuild fresh old positive witnesses after recovering the
front arithmetic. The result is equivalence of existential zero assertions,
not a pointwise assertion that every old auxiliary coordinate survives.
For example an arbitrary negative new comparison multiplier need not be
an admissible old witness.

Finally every monic projection step is `z=Q(other coordinates)` with an
integral quadratic Q and preserves residual degree at most two. Reversing
the recorded steps restores every deleted defined coordinate uniquely;
the two explicitly unconstrained coordinates are restored as zero.
The final integral translations are bijections. Thus the emitted 478-variable
equation is equivalent to the full new quadratic system over all integers.

## 7. Logical scope, measurements and attribution

The equation is exactly the sum of the squares of its 305 literal quadratic
rows. Over integers this vanishes exactly when every row does. Its complete
5,484-term expansion is supplied, with exact degree four and coefficient
height 511,326. The parent has 517 variables, 310 rows, 6,774 terms and
height 3,904,267. All four displayed size metrics improve, but no global
minimum or smallest known variable count across the repository is claimed.

The signed comparison lemma, integral projection, three-square guards,
signed Horn factorization and original carrier/calculus calibration are
inherited and credited. The contribution is the F>=1 early bootstrap,
dependency-ordered product-sign compression, the coupled frame/nonvanishing
guard, its typed-frame composition,
and the exact emitted lower-cost endpoint. The unbounded implications are
ordinary mathematical proofs formalizable in ZFC. Finite checkers verify
only the indicated equations, certificates, arithmetic regressions and
coefficient data; they do not decide consistency or prove that a solution
exists or does not exist.

Using the inherited unconditional endpoints
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`, the conclusion is

    ZFC proves: [no integer zero of P478] iff Con(ZFC).

The complete new theorem remains conditional only in the ordinary sense
that it invokes those explicitly identified previously proved mathematical
theorems; no consistency or soundness assumption is used in either direction.
