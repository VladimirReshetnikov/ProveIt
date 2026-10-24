# Independent review: 24 integer variables at degree 10 and 22 at degree 14

## Verdict

Both extensions are mathematically valid, with the same inherited signed
Pell, canonical determinant and compiler/calibration dependencies as the
independently reviewed 23-integer degree-12 construction. Their new steps
are exact polynomial row transformations, invertible integer coordinate
shears, and monic coordinate eliminations. One transformation additionally
uses a nonzero coordinate; that condition is established below from a
retained equation and the actual fixed coefficient, without circularity.

The complete JSON packets were independently reconstructed and checked by
`audit_integer_extensions.py`. It imports no producer code. It verifies all
final rows against independently written compact formulas, restores every
arithmetic source40 row, expands the complete sum of squares, checks each
full leading homogeneous form, and authenticates the fixed payloads and
source40 pin. It also reconstructs both entire circuit output polynomials and counts the live arithmetic gates independently. Normal and optimized Python runs pass. Finite algebra checks
are separate from the mathematical arguments stated here.

## 1. Reducing the main norm using a retained product equation

Put

    Y=a-E, X=4q u^2, H=4a+3, Delta=a^2+H,
    b=ac+gamma H, N=(X+b)^2-Delta c^2-1,
    r=E-XY.

The degree-six polynomial N can be replaced, on the common zero set of
r and the other retained source equations, by

    M=XE+2Eb+Y(b^2-Delta c^2-1).

The exact polynomial identity is

    M=Y N+(X+2b)r.                                    (1)

The replacement does not require division in the final equation.
Its inverse implication uses Y!=0. The retained equation is

    Y=(2v_scale+1)q^3, q=beta J+1.

For the actual beta=2^1064921-1>1 and every integer J, q is nonzero: q=0
would give beta J=-1, impossible in the integers. The odd integer
2v_scale+1 is also nonzero. Hence Y!=0 on every common zero of the
retained equations, before applying any Pell classification or determinant
argument. With r=0, identity (1) gives M=0 iff N=0.

The exact cancellation

    b^2-Delta c^2=H(2ac gamma+H gamma^2-c^2)             (2)

shows that M has degree five, rather than the degree-seven upper bound
one would obtain from the unreduced product YN. Here degree is taken in
the actual retained coordinates; a,c and gamma are independent degree-one
unknowns. No positive sign of Y is required.

## 2. Centering the auxiliary norm

Retain the source identity V=fo-c and apply the invertible integer shear

    y_old=fo+y.

The auxiliary residual becomes

    A=(fo+y)^2-I^2(y+c)(2fo+y-c)-1,                    (3)

because

    (fo+y)^2-(fo-c)^2=(y+c)(2fo+y-c).                  (4)

Equation (4) removes the highest-degree square from the difference. With I
retained, A has degree five. The inverse shear y=y_old-fo is an integer
polynomial, so no admissible witness is lost. There are no other occurrences
of the old y outside the auxiliary arithmetic in this source projection.

## 3. The 24-variable polynomial

Start with the 26-integer octic, keep zeta, eliminate D and V by their monic
rows, apply (1) to the main norm, and apply the shear (4). The result has
24 unrestricted integer unknowns and twelve residuals. The common source
abbreviations are

    q=beta J+1, C=q-F-alpha, s=2v_scale+1,
    X=4q u^2, Y=a-E, H=4a+3, Delta=a^2+H,
    b=ac+gamma H, D=X+b, V=fo-c, k=eta+zeta,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J.

Use the unchanged determinant G and merged positivity residual Pair from
the 23-variable review, now with Bsign=eta*zeta and zeta an independent
unknown. The twelve residuals are

    a-E-s q^3,
    E-XY,
    c-eta-kY,
    tau^2+(2tau-k)E(c-eta)-1,
    M,
    k-R-1-hE,
    (K0 q+X)C-qF-Z(q-1),
    V-cj+k-hE-1,
    I-(2r+1)c^2,
    I^2-Delta(f^2-1),
    A,
    Pair.

Their degrees are 4,4,2,3,5,4,4,2,3,4,5,4. The single equation is the
sum of their squares. Its full degree-ten homogeneous part is exactly

    64 a^4 gamma^2 (c+2gamma)^2 (a-E)^2
       +4 I^4 f^2 o^2(c+y)^2.                        (5)

In particular the coefficient of I^4 f^2 o^2 y^2 is +4 and has no
fixed-port-dependent contribution. Thus degree10 holds for the actual
fixed coefficients, not just for generic symbolic ports. The full symbolic
sum of squares has 5,634 terms with the six fixed ports left symbolic.
The supplied circuit evaluates this exact polynomial in 135 live binary
operations: 68 multiplications, 35 additions and 32 subtractions.

The independent checker restores the 22 arithmetic rows of signed40.
Eleven become zero polynomial identities. The other eleven match the
arithmetic rows above after exactly the justified replacement (1). The
merged sign guard supplies the three old source sign guards as in the
previous review. This proves both soundness and completeness with the same
canonical compatibility argument.

## 4. Eliminating the strong-Pell coordinate before expanding the auxiliary norm

For the 23-variable degree12 construction, denote its strong residual by

    S=I^2-Delta(f^2-1)

and its auxiliary residual by

    A_old=y_old^2-I^2(y_old^2-V^2)-1.

Replace the latter row by

    A_new=A_old+S(y_old^2-V^2)
         =y_old^2-Delta(f^2-1)(y_old^2-V^2)-1.         (6)

This is an invertible elementary polynomial row operation: the old row
is obtained by subtracting S(y_old^2-V^2), while S is retained. No
nonvanishing assumption or integrality inference is needed.

Now use y_old=fo+y, V=fo-c and the monic row

    I=(2r+1)c^2.

After removing I and its defining equation, the two affected residuals are

    S_new=[(2r+1)c^2]^2-Delta(f^2-1),
    A_new=(fo+y)^2-Delta(f^2-1)(y+c)(2fo+y-c)-1.        (7)

Their degrees are six and seven. Applying the strong relation before
eliminating I is essential: direct substitution into I^2(y_old^2-V^2)
would create a higher degree. The row operation (6) prevents that growth.

## 5. The 22-variable polynomial

Take the compact 23-variable specification from the preceding review.
Keep its first seven arithmetic rows and its merged positivity row.
Delete I-(2r+1)c^2 and replace its strong and auxiliary rows by (7).
The remaining coordinates are exactly

    J,F,alpha,f,h,r,v_scale,tau,eta,y,gamma,o,j,E,c,a,
    u,Z,pair_root,pair_pos1,pair_pos2,pair_pos3.

There are 22 unrestricted integer unknowns and ten residuals, of degrees

    4,4,3,4,6,4,4,6,7,6.

Again the equation is their sum of squares. Its entire degree-fourteen
homogeneous part is exactly

    4a^4 f^6 o^2(c+y)^2.                              (8)

The coefficient of a^4 f^6 o^2 y^2 is therefore +4, independently of all
fixed coefficient ports. The exact degree is fourteen. The complete
symbolic sum of squares has 16,525 terms when the ports remain symbolic.
The supplied circuit evaluates this exact polynomial in 123 live binary
operations: 62 multiplications, 31 additions and 30 subtractions.

The independent source40 restoration now produces thirteen identically
zero arithmetic rows and nine surviving arithmetic rows. After the exact
operation (6), these are the nine arithmetic rows of the new packet;
the tenth row is its unchanged merged positivity guard. Thus the new
system is existence-equivalent to the preceding 23-variable system by
explicit inverse maps and row operations. It needs no additional canonical
witness argument beyond that already supplied for the 23-variable system.

## 6. Verification and conclusion

The normal and `python3 -O` executions of

    python3 audit_integer_extensions.py PATH_TO_INTEGER_PACKET

both pass. The detailed JSON audit lists the dimensions, complete leading
forms, degree witnesses and polynomial support counts. Source arithmetic
identities are verified over the full integer polynomial ring; neither
random substitutions nor finite searches are used as proofs of them.

The new 24/10 and 22/14 points are rigorously supported extensions of the
same explicit fixed-coefficient construction. They do not assert global
minimality or a new end-to-end proof-assistant certificate. The transition
from source solvability to finite syntactic ZFC refutability remains the
identified inherited ordinary compiler/Pell/calibration theorem.
