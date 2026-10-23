# Independent review of the nine-variable source adaptation

Reviewed 23 October 2026. Review scope: new raw-parent source, overlapping
target placement, raw-witness shift, bounds, and degree-certificate interface.
The historical Jones ratio proof and the native compiler are imported
dependencies, not re-proved or newly kernel-checked by this review.

**Conclusion: the new source adaptation and its local composition are sound.**
The new positive-domain circuit has 682 operations and exact degree
33,332,620. The natural-domain bijection gives 685 operations and the same
degree. These statements do not extend the domain to unrestricted integers.

## 1. Parent and witness shift

`data/coefficient_recipes.json` now describes the unshifted quadratic
residuals of the 31-positive-variable parent. One row (original row 8) has
been negated, and the rows reordered; both preserve the common zero set.
The new source uses `Jcode = 2*(1+g+ell)^2*Dcode + B*geom`, with

    ell = sum_i B^w_i,
    g   = sum_i z_i B^w_i,
    0 <= z_i < b.

Thus the formal square being multiplied by Dcode is

    (1 + sum_i (z_i+1)*t^w_i)^2.

The factorial-normalized target coefficient is exactly twice the raw
parent residual evaluated at the positive tuple x_i=z_i+1. This directly
recovers the original positive parent without expanding every residual
after substitution. The low digit mask is unchanged and constrains the
z_i, rather than the x_i.

For completeness, a positive parent solution cannot be x_i=1 for every i:
the fifth parent comparison E=X*(a-E) would read 1=0. Consequently its
translated digit code g is positive, as required by the nine-variable
ratio bridge.

## 2. Finite target isolation replaces disjoint block intervals

The inherited package-45 proof used targets separated by 2W+1. That
spacing argument is no longer applicable and is not needed. Here the
finite certificate checks all quadratic monomials beta of degree at most
two against every supported coefficient alpha in every source row:

    h_j - alpha.w + beta.w = h_k

holds only for k=j and beta=alpha. An independent enumeration checks all
528 quadratic monomials, all source reversal terms, and all targets. The
reversal exponents are nonnegative and mutually distinct. Their largest
exponent is the largest target, 7,243, with coefficient +2 from the
constant term of the negated original row 8. The total product span is
7,243+2*799=8,841.

Thus overlapping interval enclosures do not create cross-target
contributions, and every coefficient of Dcode has magnitude below the
same bound M used for individual source coefficients. The leading +2
term proves Dcode>0 for every allowed b, independently of g.

## 3. Bounded-source estimates after the new shift

The source uses b>=4096M, B=b^3, W=799, cap=32bB^W, and
Kcode=Hmax+2W. Since all weights are distinct and lie in {1,...,W},

    ell < B^(W+1)/(B-1) < b*B^W.

On the soundness branch g<4bB^W, integrality gives 1+g<=4bB^W, hence

    1+g+ell < 5bB^W.

The positive leading term and the coefficient bound give

    0 < Dcode < M*B^(Hmax+1)/(B-1).

Therefore

    2*(1+g+ell)^2*Dcode
      < 50*M*b^2*B^(Kcode+1)/(B-1).

The old constant 32 must be replaced by 50 at this point. This does not
require enlarging the base floor: b>=4096M implies
50Mb^2 <= B/64. Adding B*sum_{k=0}^{Kcode}B^k yields

    Jcode < (65/64)*(B/(B-1))*B^(Kcode+1)
          < 4*B^(Kcode+1) = N1.

The other source bounds g<N0 and Tcode<N remain unchanged. Hence
0<=Scode,Tcode<N still holds on the bounded-g branch before imposing any
carry condition.

## 4. Balanced digits and completeness

After the low mask has recovered 0<=z_i<b, put x_i=z_i+1. Then x_i<=b
and the coefficient bound for the formal product is

    M*(1+sum_i x_i)^2 <= M*(32b)^2 <= B/4.

This is exactly the balanced-digit bound needed by the inherited binary
carry argument. The target coefficients vanish if and only if all raw
parent residuals at x vanish.

Conversely, for any fixed positive parent solution choose an arbitrarily
large power of two b>=b_floor with b>max_i x_i. Let z_i=x_i-1 and form g
from these digits. Then g>0 and

    g <= (b-1)*ell < bB^W,

so 32g<cap. This gives the stronger completeness inequality required by
the inherited ratio_complete theorem. The ratio_sound output 8g<cap
gives g<4bB^W, exactly the soundness branch verified above. There is no
circular bound assumption.

## 5. Degree certificate and evaluator

The compact equation and its certificate equation are polynomially
identical. Write V1=(AC)(AE)(GH) and a1=DFI. The certificate uses

    delta = (C^2-1)*(AE)^2*(GH)^2
          + D*(E^2-1)*(GH)^2 + D*F*(H^2-1).

The three identities (AC)^2-D=C^2-1, (AE)^2-F=E^2-1, and
(GH)^2-I=H^2-1 give delta=V1^2-a1 by telescoping. Expanding
Theta=E0-Omega*V0*V1 then shows

    Theta^2-Omega^2*(a0+V0^2*a1)
      = E0^2-2*E0*Omega*V0*V1
          +Omega^2*V0^2*delta-Omega^2*a0.

This proves equality of the compact and certificate expressions without
relying on sampled evaluations. The certificate avoids the cancellation
which would inflate a naive degree bound on the compact evaluator.

An independent integer calculation propagates total-degree bounds and
the coefficient at that bound after every input is set to T. It obtains
degree 33,332,620 and the exact nonzero leading coefficient 2^2050. Thus
the upper bound is attained, proving exact degree. As a secondary modular
check, the coefficient is 638,575,513 modulo 1,000,000,007. The compact
positive evaluator has 189 additions, 24 subtractions, and 469
multiplications, totaling 682. The positive certificate has 700 gates;
it is a proof artifact, not the claimed compact evaluator. The natural
forms have respectively 685 and 703 gates.

The independent script `audit_nine_interface.py` checks the target
isolation, positive top coefficient, literal operation counts, and exact
degree arithmetic. It uses the shipped fixed coefficient payloads and
does not import the new generator.
