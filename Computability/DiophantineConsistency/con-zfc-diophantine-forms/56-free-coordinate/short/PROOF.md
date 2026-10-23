# A 73-operation equation of degree 54 and a 74-operation equation of degree 46

These are new compositions of reductions present in the incoming archives at
ProveIt commit `4b4349064a750ba6347293b55874a7f92abdd0db`. The underlying compiler,
ordinary strong-rank theorem, positive-gap theorem and squared-modulus Pell
reconstruction remain inherited mathematical dependencies. No new Lean/Rocq
compilation or checked object-language ZFC derivation is asserted here.

The main short improvement uses fifteen strictly positive integer variables

    J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,e,gamma.

Use the entire package-31 fixed coefficient tuple in
`coefficients31/COEFFICIENT_BINDING.json`, including its already shifted MF.
It has `B=2^1064921` and `beta=B-1`. All four binary payloads are included.
The JSON names Jrep, transport_quotient, auxiliary_quotient, tau_root and
auxiliary_gap denote J,z,T,tau,e, respectively. Bm1 and Kconstant denote
beta and K0. These naming aliases introduce no additional variables.

## 1. Exact polynomial

All the following names are abbreviations in those fifteen unknowns:

    q=beta*J+1, C=q-F-alpha,
    X=w*q, Y=s*q^3, E=X*Y,
    k=eta+zeta, c=k*Y+eta, a=E+Y,
    H=4*a+3, Delta=a^2+H, D=X+a*c+gamma*H,
    L=E*k*Y,
    R=((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J,
    V=f^2*(c*T-R)-c, U=Delta*(f^2-1), I=i*c^2,
    N0=tau^2-L*(L+k), N1=D^2-Delta*c^2,
    Na=(V+e)^2-U*e*(2*V+e), Ws=I^2-U,
    Nk=k-h*E-R, Nt=(K0+w)*C+(q-F)-z*(q-1).

The principal equation is

    Q54 = N0^2 + Na^2 + Ws^2 + (N1*Nk*Nt-1)^2 - 2 = 0.

It has exactly 73 binary arithmetic operations: 39 multiplications,
19 additions and 15 subtractions. Its exact degree is 54. The literal
evaluator is `generated/ordinary_gap_minima73_squared_modulus_degree54.json`.

A second, lower-degree tradeoff is

    Q46 = N0^2 + N1^2 + Na^2 + Ws^2 + (Nk*Nt-1)^2 - 3 = 0.

It has 74 operations (39 multiplications, 20 additions, 15 subtractions)
and exact degree 46. Both equations use the same complete package-31 tuple.

## 2. A universal local minimum, independent of compiler semantics

Assume only that all fifteen unknowns and beta are positive integers.
Then q>=2, n=XY^2>=2, c>=3, I=i*c^2>=9 and Delta=(a+2)^2-1>1.

First, N0 is nonzero, because n(n+1) is strictly between successive
integer squares and cannot be a rational square. The equation N0=-1
is impossible by the standard elementary consecutive-product Pell
descent: for x^2-n(n+1)t^2=-1, n>=2 and t>0, one has

    n*t < |x| < (n+1/2)*t.

The positive integer t'=(2n+1)t-2|x| is smaller than t. Multiplication
by the norm-one unit 2n+1-2 sqrt(n(n+1)) gives another norm-minus-one
solution with second coordinate t', contradicting minimality. Therefore

    N0^2>=1, with equality precisely when N0=1.

Next write y0=V+e. The exact identity

    Na=U*V^2-(U-1)*y0^2

follows by expansion. The assertion

    Na^2+Ws^2>=1,
    Na^2+Ws^2=1 iff Na=1 and Ws=0                         (A)

holds on every positive assignment, before imposing any polynomial equation.
If U=0, Ws=I^2>=81, so its square alone exceeds 1. If U>0, then U>=2.
If Na=0, the equation U*V^2=(U-1)*y0^2, with gcd(U,U-1)=1,
would force U and U-1 to be integer squares, unless V=y0=0. Two positive
consecutive integers cannot both be squares, and V=y0=0 contradicts e>0.
Thus Na is a nonzero integer. Equality in (A) now forces Ws=0 and Na=+/-1.
But Ws=0 gives U=I^2. Modulo 4, Na is then congruent to y0^2 when I is
even and to V^2 when I is odd. In either case Na cannot be -1. This proves (A).

Finally, N1 cannot equal -1. Delta is either 0 or 3 modulo 4, and a direct
check of square residues excludes D^2-Delta*c^2=3 modulo 4.

## 3. Complete local equivalence of the two displayed equations

The left side of Q54+2 is the sum of three nonnegative integer blocks:
N0^2>=1, Na^2+Ws^2>=1, and (N1*Nk*Nt-1)^2>=0.
Hence Q54=0 is equivalent to

    N0=Na=1, Ws=0, N1*Nk*Nt=1.

The last product makes N1 an integer unit. Its modulo-four obstruction
excludes -1, so N1=1 and Nk*Nt=1. These are exactly the equality conditions
for Q46=0, by the same minimum argument and nonvanishing of N1.
Conversely those five conditions plainly make both Q54 and Q46 zero.
This equivalence is tuplewise and uniform in the other three fixed integer
ports; no machine simulation or unbounded search is involved in this step.

To see the gate saving, start from Q46's 74-gate schedule. Remove the square
N1^2 and the addition placing it in the total. Insert one multiplication
to change Nk*Nt into N1*Nk*Nt; change the final constant from 3 to 2.
Exactly one operation is saved, and every retained operation remains live.

## 4. Why the squared quotient preserves existence

The old gap-minimum polynomial used

    V_old=c*(T_old*f-1)-R*f^2.

There is an all-value polynomial identity

    V_new(f,T)=V_old(f,f*T).

Thus a positive zero of Q46 or Q54 maps directly to a positive zero of the
old ordinary gap polynomial using T_old=f*T. This proves soundness using
the inherited ordinary compiler theorem. It does not assume that every old
T_old is divisible by f.

For completeness, a blank-halting computation supplies a canonical
normalized witness, transferred to ordinary coordinates by
i_ordinary=Delta*i_normalized. The inherited native decoding gives

    c=psi_A(R), A=a+2, R=3 mod4,
    f^2=1+Delta*i_normalized^2*c^4,
    I=Delta*i_normalized*c^2,
    I^2=Delta*(f^2-1), c|I, f^2=1 mod c.

Here chi and psi are the standard positive Pell sequences. For odd
R=2r+1, write chi_t(R)=t*Q_r(t^2). Their elementary recurrences prove

    Q_r(0)=(-1)^r*(2r+1),
    Q_r(1-A^2)=(-1)^r*psi_A(2r+1).

Since r is odd, the positive Pell values

    V=chi_I(R)/I, y=psi_I(R)

satisfy the auxiliary norm, V=-c mod f^2, and V=-R mod c. Because
gcd(c,f)=1 and f^2=1 mod c, the quantity V+c+R*f^2 is divisible by
c*f^2. Therefore

    T=(V+c+R*f^2)/(c*f^2)

is a positive integer and has precisely the required V_new expression.
Moreover V>1 and the norm identity gives

    (I^2-1)*(y^2-V^2)=V^2-1>0.

Thus e=y-V is strictly positive. The other coordinates remain unchanged,
and all equality conditions in Section 3 hold. This proves completeness.
It is an existence-preserving reconstruction, not a coordinatewise bijection.

The inherited source proves blank K215 halting equivalent to a finite ZFC
refutation. Composing these arithmetic proofs gives, at the ordinary
mathematical proof level formalizable in ZFC,

    ZFC proves: no positive zero of Q54 iff Con(ZFC),
    ZFC proves: no positive zero of Q46 iff Con(ZFC).

This last statement imports the identified native compiler and K215 proof.
The finite circuit verifier does not independently establish either one.

## 5. Exact degree certificates

Put Q=beta*J and k0=eta+zeta, and set C1=Q-F-alpha. The factor degrees are

    deg(N0)=22, deg(N1)=18, deg(Na)=23,
    deg(Ws)=22, deg(Nk)=7, deg(Nt)=2.

The main-norm cancellation follows from the exact identity, with Z=X+gamma*H,

    (a*c+Z)^2-(a^2+H)*c^2=Z^2+2*a*c*Z-H*c^2.

Its degree-18 leading part is 8*gamma*w^2*s^3*k0*Q^11.
For Q54, only the squared grouped unit residual reaches degree 54. Its
complete leading homogeneous form is

    64*gamma^2*h^2*w^6*s^8*k0^2*Q^30*(w*C1-z*Q)^2.

The monomial J^32*gamma^2*h^2*w^6*s^8*eta^2*z^2 has coefficient
64*beta^32, nonzero for the actual positive beta. Thus degree 54 is exact.

For Q46 only Na^2 reaches degree 46, with complete leading form

    4*w^4*s^6*k0^2*T^2*f^8*e^2*Q^22.

Its J^22*w^4*s^6*eta^2*T^2*f^8*e^2 coefficient is 4*beta^22>0,
so degree 46 is exact.

`build_and_audit.py` reconstructs both literal circuits, authenticates
the copied incoming sources, checks the two local polynomial identities,
fully expands the main-norm dependency cone to verify its cancellation,
propagates homogeneous components through every gate, and verifies all
claimed leading forms, operation counts, coefficient bindings and liveness.
It passes in both normal and optimized Python mode without using assertions
as verification gates.

## 6. Scope of the improvement

The reviewed incoming collection already contains a 66-operation degree-157
equation, a 72-operation degree-80 equation, and a 75-operation degree-44
ordinary gap equation. Those results must be retained in comparisons.
Q54 and Q46 add degree/operation tradeoffs: 73/54 and 74/46. They do not
improve the 66-operation record, the degree-44 point, the nine-positive
variable count, or the ten-unrestricted-integer variable count. They are
bounded improvements within the inspected repository and incoming archive
collection; no global minimality or worldwide novelty claim is made.
