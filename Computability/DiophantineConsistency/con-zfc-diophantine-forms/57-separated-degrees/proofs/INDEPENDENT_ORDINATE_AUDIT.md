# Independent audit of the two twelve-variable ordinate reductions

Reviewed `pell_research/thirteen/PROOF.md`, Section 9, and the literal
`build_twelve_reduced.py` / `build_twelve_balanced.py` circuits. This audit
concerns the new reduction from the preceding signed auxiliary system;
the unbounded native compiler, signed auxiliary-index theorem, and K215
calibration remain the explicit inherited dependencies of that system.

## Verdict

Both adapters are correct. No additional auxiliary cofinality lemma or
assumption about the sign of the recovered strong root is needed.

## Exact adapter identity and soundness

With Q=M C, d=Q-1, and

`Z=C(D v^2+b^2-1)+d y(2-M y)`,

the identity

`M Z=Q(D v^2+b^2)-1-d(My-1)^2`

holds in the integer polynomial ring. It was also checked independently
by sparse polynomial expansion in six indeterminates.

The expression `J_M=Z^2-4C^2 Dv^2b^2` is a square modulo4. Consequently the
existing integer-unit extraction gives Nt=1, N=J_M=0, as claimed. Its
outer-interface bounds ensure C,v,b>0. Therefore

`f=Z/(2Cvb)`

is defined, rational, and satisfies f^2=D. A rational square root of an
integer is an integer. D>0 makes f nonzero; no positive sign is assumed.
For both choices of M, M>=2, so the reconstructed auxiliary coordinate
`y_old=M y-1` is strictly positive for every supplied y>=1. Multiplying
Z=2Cvb f by M gives exactly the prior auxiliary norm with y_old.
All preceding signed soundness arguments therefore apply unchanged.

## Canonical completeness

The required phase R=3 modulo4 is supported by the authentic compiler,
not by arbitrary independent choices of coefficient ports. The preserved
wave-7 `short/SQUARED_MODULUS_PROOF.md`, Section5, proves it using
q=B^n, J=1+B+...+B^(n-1), B divisible by4, MC=2 modulo4, and the low mask
forcing Cw=1 modulo4. The defining R then satisfies R=Cw+2=3 modulo4.
The chosen compact tuple satisfies the required fixed congruences.

For the same canonical outer coordinates and strong root f>0, let
m=Delta*i*c^2, Q=m^2, V=chi_m(R)/m, and y_old=psi_m(R).
Odd-index Pell polynomial identities give

* V is a positive integer;
* V=-c modulo f^2;
* V=-R modulo c;
* y_old=-1 modulo m^2=Q.

The last statement follows because psi_m(2r+1) is an even polynomial in m
with constant term (-1)^r, and r=(R-1)/2 is odd. The first two congruences
use the same exact Chebyshev identity as the inherited squared-modulus
reconstruction. Since gcd(c,f)=1 and f^2=1 modulo c, the numerator
V+c+R f^2 is divisible by c f^2, hence by c f. Its quotient
T=(V+c+R f^2)/(c f) is strictly positive.

Both new moduli divide Q: M=Q, or M=(Delta*i*c)^2 with Q=M c^2.
Therefore y=(y_old+1)/M is a positive integer. The modified T and y do
not occur in the primary carrier t; all retained coordinates remain
positive. Thus the canonical witness supplies the new equation exactly.

Independent integer fixtures tested these statements at (a+2,R) equal to
(2,3), (3,3), (4,3), and (2,7), for both moduli. The last strong root has
38,715 bits. All eight reconstructions satisfy the exact new norm, the
three congruences, and positivity of T,y. These are regression checks,
not substitutes for the universal argument.

## Degree and circuit inspection

From the supplied witness degrees:

`deg c=5, deg I=11, deg Delta=12, deg D=34, deg Q=46,`
`deg v=6, deg b=38, deg N=68, deg Nt=2`.

For M=Q,C=1, the two Z summands have degrees76 and94. The latter has a
nonzero leader. Hence deg J_M=188 and total degree=68+188+2=258.

For M=(Delta*i*c)^2,C=c^2, deg M=36 and deg C=10. The first Z summand
has degree86 and the second84. The subtraction term of J_M has degree142,
strictly less than 2*86=172. Hence the total degree is68+172+2=242.
The displayed leading products are nonzero in the integer polynomial
ring, so these are exact degrees. The balanced builder's expression
M=(Delta I)(Delta i), followed by Q=M c^2, equals the stated M and Q
identically. The checked circuits implement the intended formulas.
