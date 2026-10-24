# Exact degree 1000, with an authentic-coefficient certificate

This note covers the unscaled centered budget and the unit main-root multiplier in `build.py` and `PROOF.md`. Earlier exploratory degrees do not describe the delivered equations.

The preferred polynomial has 12 unrestricted integer variables, exact total degree 1000, and 180 live binary arithmetic operations. Its companion omits the first-Pell shear and has degree 1024 in 179 operations. All fixed coefficient ports have degree zero.

## A complete cancellation-sensitive cut

Write D=delta, let d=M^2 Dmain, A=U^2 Df, e=U^2 Ag, and write L=XY^2k. Then

    B=U^2(L^2+Lk+1),
    Cn=U^2((D+1)V^2−1),
    Z=UV+UL+s,
    s=Un+M b0+H(v−q^2).

For the degree-1024 companion replace Z by UV+s. These are exact polynomial identities. The weights of (U,s,V,d,A,L,k,e,D) are bounded by

    (6,7,19,14,26,11,5,28,22).

The weights of 1,sqrt(d),sqrt(e),sqrt(de) are (0,7,14,21). Expand the three-root cleared norm in this free biquadratic algebra, then take its two quadratic norms. `check_degree.py` performs exact sparse arithmetic at this cut and obtains the following weighted component degrees:

    Degree-1000 construction:
      first cleared square expression: (64,54,61,43)
      after its square and scalar subtraction: (122,118,125,115)
      after final three-root subtraction: (250,240,247,243).

    Degree-1024 companion:
      first cleared square expression: (56,54,61,43)
      after its square and scalar subtraction: (128,110,117,115)
      after final three-root subtraction: (256,238,245,243).

In each case the scalar component is strictly largest at the final stage. The final two quadratic norms therefore square that scalar leading form twice; their other terms have strictly lower weight. For degree1000 the scalar leading form is

    64 D^4 U^6 V^4 L^2 e,

and hence the complete leading form is

    2^24 Q0^16 U0^24 V0^16 L0^8 e0^4.

For degree1024 the scalar leading form is 16 D^4 U^8 V^4 L^4, and the complete leading form is 2^16 Q0^16 U0^32 V0^16 L0^16.

These computations prove universal upper bounds, but a coefficient after actual specialization is needed to establish exact degree. That certificate follows.

## A nonzero coefficient for the actual fixed tuple

Let leading forms carry a subscript zero. Put

    q0=6 beta j; X0=12w q0; Y0=q0 v; a0=X0Y0; i0=2r;
    R0=q0^4 z−12q0^3 w C;
    k0=R0+h a0; eta0=−Y0 k0;
    Q0=a0^4 i0^2 c^4;
    U0=8q0^2 a0;
    V0=−a0^2 i0^2 c^4 R0;
    L0=X0Y0^2 k0;
    e0=−4U0^2 q0^2 eta0^2.

The last formula follows from Ag=budget−1−p2^2−p3(p3+1): its unique degree-16 contribution is −4q0^2 eta0^2. The determinant-error term has smaller degree, so no coefficient tuple relation can cancel this top part.

Substitution into the complete leading form gives

    [j^456 w^152 v^168 h^16 r^64 c^128 z^16] P1000
       = 2^952 3^608 beta^456 > 0.

The exponents sum to 1000. The h^16 coefficient chooses ha0 in every factor of k0^16, and z^16 then chooses q0^4z in every factor of R0^16. No other fixed compiler coefficient enters this coefficient. Thus it is nonzero for the actual beta, independent of any relation among K0,MC,MF,cone_A,cone_B.

Likewise

    [j^464 w^160 v^176 h^16 r^64 c^128 z^16] P1024
       = 2^960 3^624 beta^464 > 0.

`check_degree.py` verifies both coefficient statements by exact sparse integer arithmetic, in normal and optimized Python. The checker uses explicit errors rather than removable assertions.

## Why the extra first-root shear helps

The map n→n+L is an integral polynomial coordinate bijection, since L is independent of n. It therefore preserves existence and requires no parity assumption. Centering the dominant first-Pell square removes degree24 from the final norm. Further additions to s of degree at most7 cannot remove the displayed leading term: the cut certificate's leading scalar does not involve s and the guard root remains the next dominant term. No global degree optimality is asserted.
