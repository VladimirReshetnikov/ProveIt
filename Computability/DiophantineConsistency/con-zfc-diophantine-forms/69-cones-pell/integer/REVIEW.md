# Independent review of the native weighted-cone reduction

Review date: 2026-10-23. Reviewed by a separate reasoning process in the same assisted research session. This is internal review, not external peer review or a proof-assistant certificate.

## Verdict

The proposed replacement of two ternary positivity guards by one weighted
Lorentz-cone guard is valid for the coherent source34 native coefficient
tuple. It reduces the literal quartic41 system to 38 unrestricted integer
coordinates and 25 quadratic residuals. It preserves **existence of a zero**;
it does not claim that every witness of the old system satisfies the new
guard. Completeness uses the canonical occupied-cell witnesses of the native
compiler. Soundness uses no canonicality assumption.

The review assumes the named inherited native compiler and signed Pell
theorems used by quartic41. It is not a new end-to-end proof-assistant check
of those inherited theorems or of the object-language ZFC equivalence.

## Exact sources inspected

- `upstream/quartic41.json`, including the literal transport residual and
  both native positivity guards.
- `upstream/coefficients/COEFFICIENT_PROOF.md`, the source34 mixed-parity,
  unrounded tuple with rho = 2^121, B = rho^8801, and beta = B - 1.
- `upstream/coefficients/sources/WANG943_LANGUAGE_AND_COMPILER.md`, especially
  occupied-cell decoding, occupancy propagation, and canonical padding.
- Source64 `upstream/Q41_PROOF.md`, especially its restoration of the earlier signed
  system and the divisible-by-four canonical scale.

The old language document also describes larger historical geometries. This
review uses only its language/occupancy proof; the numerical geometry is
the source34 replacement in `COEFFICIENT_PROOF.md` throughout.

## 1. Fixed constants and native digit bounds

Set

    rho = 2^121,
    A = rho^3296,
    H = rho^2196,
    beta = rho^8801 - 1,
    T = DC + DR + 1 = K0 - beta*rho + 1.

The identity for T follows from DR = rho and K0 = DC + B*DR.
All these constants are positive. Their definitions are bounded and
independent of consistency or halting.

Every cell of a canonical native witness is occupied. Its four anchor
digits at 1095, 1096, 2195, and 3296 are one. All other nonzero digits lie
below exponent 2196 and are strictly smaller than rho (the ignored dummy
digit can be at most three). Consequently its integer cell value is

    A + v,  where 0 <= v < H.

For N cells, q = B^N and J = (q - 1)/beta, this gives

    A*J <= C < (A + H)*J.

A cyclic permutation of complete B-cells has exactly the same bound.

## 2. The required fixed bound is elementary

The source34 clause weights are W_j = 2^(10 + 2j), 0 <= j <= 43.
Every coefficient c_e is smaller than 2^97, because

    1 + sum_(j=0..43) W_j < 2^97.

There are 989 native support positions. Every exponent in DC is at most
5495. Including the four bare terms, DR, and the constant 2 in T+1,

    T + 1 <= (2*989*(2^97-1) + 7)*rho^5495
           < 2^109*rho^5495
          < rho^5496.

Since H < A, one obtains

    2*(T + 1)*(A + H) < 4*rho^8792
                      < rho^8801 - 1 = beta.

Thus the key bound does not depend on a numerical experiment on a particular
halting computation or on an unproved estimate for decoded digits.

## 3. Checking the F convention and the rotations

Write C = q - F - alpha and w_source = 4*w_scale. The actual transport
residual in quartic41 is exactly

    (K0 + w_source)*C - (q - 1)*z - F.

In particular F is the native residue, not a shifted copy of that residue.
The fact that the fixed coefficient MF is shifted by beta does not shift F.

Canonical witnesses have w_source = 2^(R - t), where t = d*N and
R is congruent to d*width modulo d*N. Therefore d divides R-t, and
w_source is a power of B. Both

    U = B*C mod (q - 1),
    V = w_source*C mod (q - 1)

are whole-cell cyclic permutations of C. Hence C, U, and V each lie in
[A*J, (A+H)*J). The nonnegative integer

    F_raw = DC*C + DR*U + V

is congruent to F modulo q-1 and satisfies

    T*A*J <= F_raw < T*(A+H)*J < beta*J = q-1.

The canonical F is the representative in [0,q-1), so F = F_raw. This proves
the claimed interval for F without assuming that arbitrary signed solutions
decode to canonical witnesses.

It follows that

    beta*J/2 < alpha = beta*J + 1 - F - C <= beta*J.

For the upper bound, F+C >= (T+1)*A*J >= 1. For the lower bound, use the
strict fixed inequality of Section 2. All canonical C, F, alpha are positive.

## 4. Cone soundness

Define the three weighted linear forms

    Xc = beta*F,
    Yc = 2*T*A*alpha,
    Zc = T*beta*C,

and the quadratic form

    K = 2*(Xc*Yc + Xc*Zc + Yc*Zc) - Xc^2 - Yc^2 - Zc^2.

If one coordinate is zero, K is minus the square of the difference of the
other two. If the nonzero coordinates have mixed signs, after permutation
and possibly simultaneous negation let x,y > 0 and z < 0. Then

    K = -(x-y)^2 + 2*z*(x+y) - z^2 < 0.

Thus K > 0 forces all three weighted coordinates, and therefore F, alpha,
and C, to have the same nonzero sign. In particular F*alpha > 0 and F*C > 0.
The standard positive ternary form

    Pos(a,b,c) = 1 + a^2 + b^2 + c*(c+1)

represents every positive integer over unrestricted integer arguments.
Consequently a solution of the new cone guard can restore both deleted
old positivity guards. This soundness argument does not assume q > 0 or
that the solution is canonical.

## 5. Cone completeness

Put L = T*A*beta*J > 0. The canonical bounds above give

    L <= Xc,Yc,Zc <= 2*L.

For x=L+r, y=L+s, z=L+t with 0<=r,s,t<=L, direct expansion gives

    K = 3*L^2 + 2*L*(r+s+t) + 2*(r*s+r*t+s*t) - r^2-s^2-t^2
      >= 3*L^2 > 0.

The inequality uses r^2 <= L*r and its two counterparts. Thus every
canonical native witness can be extended to a solution of

    K = Pos(a,b,c).

This establishes the needed existential completeness. No restriction on
the possible shape of an arbitrary old noncanonical solution is required.

## 6. Counts, degree, and material costs

Delete the six private coordinates of the two old Pos guards and insert
three fresh private coordinates of the new Pos guard. This yields
41 - 6 + 3 = 38 unknowns. Replacing two residuals by one yields 25 residuals.
The new guard is quadratic in the unknowns, because all weights are fixed
integers and C is linear. The sum of residual squares therefore has degree
at most four; its inherited tau^4 coefficient is one, so the degree is
exactly four.

The variable saving has a coefficient cost: the cone uses the fixed weights
beta, 2*T*A, and T*beta, and its expanded coefficients contain their products.
Any comparison must report this cost or give bounded formulas/circuits for
the weights. A variable-count improvement is not an improvement in every
possible measure of polynomial size.

## 7. Transfer to the other low-degree families

The same replacement applies to a source family only after checking that
its two guards are precisely F*alpha = Pos and F*C = Pos, that the same
coherent native tuple and C=q-F-alpha convention are used, and that its
canonical scale is a whole-cell rotation. The new argument then changes
only the guard rows and their private coordinates. It does not itself
justify unrelated eliminations or changes in a different family.


## 8. The two elimination companions in this release

The release derives its 32-variable sextic and 27-variable octic directly
from the new quartic38; it does not apply the cone to a different coefficient
tuple. Their listed restorations were reviewed against the literal source
rows. In the sextic the six removed rows define N, X, P, C2, F2, and Baux.
The additional tau change is invertible over the integers, with

    tau_old = tau_new + E*(c-eta).

Writing u=E*(c-eta) and k=eta+zeta, the affected residual is identically

    (tau_new+u)^2-(k+u)^2+(k+u)*k-1
      = tau_new^2+(2*tau_new-k)*u-1.

Its degree is three. Every other retained row also has degree at most
three, and the auxiliary row -I^2*g+y^2-1 supplies the uniform degree-six
coefficient I^4*g^2=1. Thus there are 32 coordinates and 19 residuals.

In the octic the eleven removed rows define L, N, X, P, D, Delta, C2,
F2, zeta, g, and Baux. In particular row 16 defines

    eta+zeta = 1-V+j*c+h*E,

so the proposed zeta restoration is exact, not an added inequality or
choice of branch. Each right-hand side uses retained coordinates. All
remaining residuals have degree at most four. The auxiliary row becomes

    I^2*(V^2-y^2)+y^2-1,

whose square supplies the uniform degree-eight coefficient I^4*V^4=1.
There are 27 coordinates and 14 residuals.

Both restoration maps have inverse coordinate projections (with the stated
integer shear of tau in the sextic). Consequently both are bijections of
integer zero sets, and inherit the cone quartic's existence equivalence.
The exact sparse checks in reproduce.py separately certify the vanishing
of all 17 eliminated rows and the surviving monomial coefficients. This
review inspected their mathematical meaning; finite diagnostic examples
are not used to prove the universal correspondence.
