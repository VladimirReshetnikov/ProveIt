# Exact algebra of the whole-product center

All named values below are polynomial abbreviations, not extra variables.
Use the parent definitions of A,Y,k,U,b,c,E,V,G,Q,M and Z0. In particular

    E = 1+k^2 X Y^2 (X Y^2+1),       A=Y(X+1)+1,
    V = [1+2(A^2-1)U^2 E]b-c,
    G = E[1+(A^2-1)U^2 E].

As a polynomial in A over Z[Y,k,U,b,c], write E=e2*A^2+e1*A+e0, where

    e2=k^2Y^2,
    e1=k^2Y(1-2Y-2Y^2),
    e0=1+k^2Y(Y+1)[Y(Y+1)-1].

Let F=E*V and let Qj be the ordinary polynomial quotient of F by A^j.
The intended center is

    W4 = U(4AF-2Q1-Q3/2).

This is an integer polynomial. Indeed

    F=(b-c)E+2U^2b(A^2-1)E^2,

and E has A-degree two, so Q3 is coefficientwise divisible by two. No
division operation appears in the literal source graph.

## Short division-free evaluator

Define

    S = kY[(ell+k)-kY(Y+1)],        e2=(kY)^2,
    theta=U^2b,
    Rc=theta(3E+e2)-(b-c),
    Sc=4E^2+3S^2+e2^2,
    W4=U[2S*Rc+A(4EV-theta*Sc)].

Here ell=XY*kY and S=e2*A+e1 is exactly the quotient of E by A.
To prove the evaluator identity, set

    J1=quot(E^2,A)=S(2E-AS),
    J3=quot(E^2,A^3)=e2(2S-Ae2),
    H1=quot((A^2-1)E^2,A)=AE^2-J1,
    H3=quot((A^2-1)E^2,A^3)=J1-J3.

Then Q1=(b-c)S+2theta*H1 and Q3=2theta*H3. Also

    4H1+H3
      =4AE^2-3J1-J3
      =A(4E^2+3S^2+e2^2)-2S(3E+e2).

Substitution gives the displayed division-free W4 exactly. This identity
holds as an integer polynomial at every tuple; it is not a zero-set-only
identity.

## Full output and exact degree

The new graph subtracts W4 in the carrier, before multiplication by hDH.
Thus its complete Z is Z0-MW4, and the full polynomial is

    P = Q[(Z0-MW4)^2-16M^2GV^2]+16M^2G-(Z0-MW4)^2.

Let D=W4^2-16GV^2. Independent exact collection in
Z[A,Y,k,U,b,c], with weights (4,2,1,7,4,3), gives 594 nonzero terms and
weighted degree106. Its complete leading homogeneous component is

    D106 = 8 A^8 Y^8 k^8 U^6 b^2
           -48 A^6 Y^12 k^8 U^6 b^2
         = 8 A^6 Y^8 k^8 U^6 b^2(A^2-6Y^4).

The center itself has weighted degree65 and84 nonzero monomials. The naive
degree130 bound on D is not exact: the degree130 through107 components
cancel. The independently checked full decomposition is

    P=Q[Z0^2-2MZ0W4+M^2D]+16M^2G-(Z0-MW4)^2.

Using deg Q=80, deg M=11, deg Z0<=21, deg G=50 and deg W4=65, the five
summands have upper degrees122,177,208,72,152. The unique degree208 term
has leading form Q80*M11^2*D106. It is nonzero after the actual leading
substitutions A=XY, U=i(kY)^2, b=kYT-h^3(h-F), X=hw, Y=hs, h=beta J.
For example the two w powers in D106 are different and b is independent
of w. Both Q80=4A^6U^4E^2 and M11=24h^7A are nonzero. Therefore208 is
the exact total degree for the actual fixed tuple, not only an upper bound.

## Count and validation

The final evaluator has116 live binary operations:71 multiplications,
24 additions and21 subtractions, with every square and scalar product paid.
All ten original variables and the whole four-port tuple remain live.

check.py independently evaluates the actual emitted center rows and compares
all84 coefficients with the formal-quotient expression. It checks the594-term
norm difference, all preserved parent rows, the carrier shift, norm16 factor,
all coefficient bytes, and deliberate mutations after updating their operation
counts. It does not import build.py. review_graph.py uses a separate sparse
polynomial implementation and independently confirms these identities and the
actual degree208 leading form.

These are exact finite algebra checks. The unbounded Pell, positivity,
integrality and native/refutation calibration proof is supplied separately
by the parent report and the accompanying mathematical article.

