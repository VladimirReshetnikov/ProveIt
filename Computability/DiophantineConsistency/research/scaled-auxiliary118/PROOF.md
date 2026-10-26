# A uniform degree-118 replacement for the Carrier65 auxiliary factor

This is an exact equality of positive zero sets at the same four fixed
ports. It applies, in particular, to the complete certified sorted2501
tuple. It changes no native mask, machine action or coefficient recipe.
The ordinary consistency calibration is inherited from the accepted
Carrier65 theorem at those exact ports. This note adds no formal-kernel
or internal-ZFC replay and does not decide consistency.

The mechanism was identified in the inert `native/PROOF.md` member of
`ConZFC_Pell_Orientation_Exact_Projection_2026-10-25.zip`, SHA256
`7b65a024656c8e594b4d72427c91460e0d68703c5cef8ada21bc666e67439851`.
ROOT read that complete text without executing any submitted code.
The argument below states the uniform transfer directly. The submitted
numerical tuple and graph are not adopted.

## Complete definition

Let beta >= 31, K > 0 and 0 < mu < beta < omega < 2 beta be fixed integers.
The unknowns J,F,alpha,z,f,i,T,s,w,n,eta,zeta,y,gamma are all strictly
positive integers. Define the following polynomial abbreviations:

    b = beta*J, q = b+1, C = q-F-alpha,
    X = w*q, Y = s*q^3, E = X*Y, k = eta+zeta,
    ell = E*k*Y, c = k*Y+eta, a = E+Y,
    H = 4*a+3, Delta = a^2+H, D = X+a*c+gamma*H,
    R = [b*(q-F)+alpha]*(q^2-1)+(mu+q*omega)*J,
    tau = E*n+k-R, V = f^2*(c*T-R)-c,
    P = tau^2-ell*(ell+k), Q = D^2-Delta*c^2,
    S = i*Delta*c^2, W = (K+w)*C+(q-F)-z*b,
    Z = Delta*f^2-S^2,
    A = Delta*(f^2-1),
    U = S^2*(V^2-y^2)+y^2,
    Unew = A*(V^2-y^2)+y^2.

The existing polynomial is p = P*Q*U*W*Z-Delta. The new polynomial is
pnew = P*Q*Unew*W*Z-Delta. Every operation in both definitions is an
integer-coefficient polynomial operation. A is a single scalar name;
the names U and Unew distinguish the two versions in this proof only.

## Exact positive-zero-set identity

At every positive assignment, a > 0 and

    Delta = (a+2)^2-1 > 0,     Delta mod 4 is 0 or 3.

Put Zbar = f^2-Delta*i^2*c^4, an integer, so Z = Delta*Zbar.
If either p or pnew vanishes, cancellation of the nonzero integer Delta
in that mathematical equality gives a product of five integers equal
to 1. Thus every factor, and in particular Zbar, is +1 or -1.

Zbar cannot be -1. When Delta is 0 modulo 4 it has the square residue
f^2; when Delta is 3 modulo 4 its residue is f^2+(i*c^2)^2. Neither
case has residue 3, because square residues are 0 and 1. Hence Zbar = 1
and Z = Delta at a positive zero of either polynomial. No sign or
native interpretation of C, tau, V or R has been used.

The following identities hold over the entire polynomial ring:

    A-S^2 = Z-Delta,
    Unew-U = (Z-Delta)*(V^2-y^2),
    pnew-p = P*Q*W*Z*(Z-Delta)*(V^2-y^2).

Therefore pnew = p at every positive zero of either one. The identity
map on all fourteen positive coordinates is a bijection between their
zero sets. This proves both directions, including any noncanonical
positive solutions; no new witness choice or divisibility premise is
needed. The zero-set equality does not extend by this argument to
arbitrary signed assignments, because Delta's positivity was used.

For the complete sorted2501 ports, the accepted Carrier65/native theorem
therefore transfers its ordinary consistency equivalence to pnew.
Scalar inequalities alone do not give an arbitrary four-tuple a ZFC
interpretation; the actual certified native tuple remains essential.

## Gate construction and exact degree

The complete Carrier65 evaluator already computes Delta*f^2 for Z.
One additional subtraction forms A = Delta*f^2-Delta. Replace only
the coefficient input S^2 in U by A, scheduling U after A if necessary.
All previous producers remain live, since S^2 is still used by Z.
This gives a 66-operation integer-leaf evaluator: 37 multiplications,
16 additions and 13 subtractions, with the same fourteen live unknowns.
A literal graph and independent finite audit are separate deliverables;
this paragraph describes the complete construction from the accepted graph.

For the degree argument, write q0 = beta*J and k0 = eta+zeta for the
leading homogeneous forms. The degrees of a,c,Delta,S,V are respectively
6,5,12,23,8. The first factor has degree 22: ell^2 has degree 22,
whereas tau has degree 7. For the second factor put Zeta = X+gamma*H;
the exact identity

    Q = Zeta^2+2*a*c*Zeta-H*c^2

shows its degree is 18, with leading form 8*gamma*a0^2*c0. This explicitly
accounts for the cancellation between the two terms of apparent degree 22.
The new auxiliary factor has degree 30, W has degree 2 and Z degree 46.
Their complete degree-118 product is

    8*q0^67*gamma*i^2*k0^9*w^10*s^19*T^2*f^6
       *[w*(q0-F-alpha)-z*q0].

To check every factor directly, their respective leading forms are

    P:    -w^2*s^4*k0^2*q0^14,
    Q:     8*gamma*w^2*s^3*k0*q0^11,
    Unew:  w^2*s^4*k0^2*q0^14*f^6*T^2,
    W:     w*(q0-F-alpha)-z*q0,
    Z:    -i^2*w^4*s^8*k0^4*q0^28.

The coefficient of
J^68*gamma*i^2*eta^9*w^10*s^19*T^2*f^6*z is -8*beta^68, nonzero
at the actual positive beta. Thus the degree is exactly 118, not just an
upper bound. The old equation has degree 150. This is a degree reduction
at the cost of one operation, not domination on every measure or a global
minimum claim. The maintained 65-operation page remains a distinct point.
