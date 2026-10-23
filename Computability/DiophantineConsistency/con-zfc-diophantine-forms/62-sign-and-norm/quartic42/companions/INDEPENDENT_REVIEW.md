# Independent review of the 35-integer sextic and 30-integer octic

**Verdict: no local mathematical defect found.** The relocated square
guard preserves the Q42 integer zero set bijectively, and the two
elimination sequences give the claimed unrestricted-integer equations
with exact degrees 6 and 8. This review adds no new native compiler or
consistency calibration theorem; those remain the Q42 dependencies.

## The square-guard relocation

The only changed parent residual is row 24:

    beta*J+1-2*q_half_root^2  ->  X-8*rho^2.

The preliminary proof that u is nonzero is valid even before proving
q positive. The retained positive product guards make F,alpha and
C=q-F-alpha have one common nonzero sign, so |q|>=3. If u=0, the scale
and defining rows force w=X=E=0 and a=(2*v_scale+1)*q^3, giving |a|>=27.
The main norm reduces modulo H=4a+3 to 0=1, whereas |H|>=105. This is
impossible, and uses neither version of the square guard.

At a relocated-guard zero, X=wq, w=4u^2 and X=8rho^2 give
q*u^2=2rho^2. In the reduced fraction rho/u=A/B, B>0, coprimality
implies B^2|2, so B=1. Thus u divides rho and q=2(rho/u)^2, restoring
exactly the old guard with an integer coordinate. Conversely
rho=u*q_half_root satisfies the new guard. Because u is nonzero, these
maps are inverse. No additional sign assumption or hidden denominator
condition is introduced.

## Exact elimination verification

The independent checker parses the literal residual strings as restricted
polynomial syntax and uses fresh sparse polynomial arithmetic. It imports
neither `build_companions.py` nor any other project builder or checker.
It verifies the initial sextic coordinate change

    tau_old=tau_tail+P-eta-zeta

and then checks each defining row at each of the 19 elimination steps
against exactly plus or minus the monic polynomial v-f. Each restoration
is an integer polynomial in the then-remaining variables and fixed ports.
It substitutes that expression into every surviving residual and checks
the entire resulting child list, in order.

The independently composed restoration agrees with every archived
`full_parent_restorations` entry. Substituting those complete restorations
into all 27 Q42X residuals yields exactly zero or the declared child
residual; every child residual occurs once. Thus both directions of the
claimed zero-set bijections are certified. The retained-variable sets
have exactly 35 and 30 members respectively, every member occurs, and
the four bound coefficient ports and their entire manifests are unchanged.

## Degrees and actual fixed-instance coefficients

The sextic has 20 residuals with maximal degree 3 in its 35 integer
witnesses. Its fully expanded sum of squares has 349 terms with the
four fixed ports symbolic. Its coefficient of r^2*c^4 is exactly the
constant 4, independent of the ports. Its degree on the authentic
coefficient slice is therefore exactly 6.

The octic has 15 residuals with maximal degree 4 in its 30 integer
witnesses. Its fully expanded sum of squares has 470 terms with the
ports symbolic. Its coefficient of a^4*f^4 is exactly the constant 1.
Its degree on the authentic coefficient slice is therefore exactly 8.

Both supplied expanded-polynomial artifacts were compared term by term
with the independent sums of squares. The checker also confirms that
the relocation altered exactly one residual and that its parent digest
matches the actual Q42 file. Normal and optimized Python execution pass.

Reviewed packet SHA-256 values:

* `sextic35.json`:
  `6e485fcefb5460f74d4ec97093a87fdb087376a46851ae8b328437a2a0b8269f`.
* `octic30.json`:
  `91ee2d3d9a97d386fa2e8b939884d6cd846e866bb45b1efe945f11873e27b72c`.

The independent code is `check_low_degree_companions.py`; its receipt is
`COMPANIONS_INDEPENDENT_CHECK.json` in the review work area or
`INDEPENDENT_CHECK.json` in the portable component. These finite checks
establish the new polynomial identities and exact metric claims. The
unbounded Pell, native compiler and K215/refutation theorems are expressly
inherited from Q42, whose new common-sign argument was separately reviewed
in `P13_REVIEW.md`.
