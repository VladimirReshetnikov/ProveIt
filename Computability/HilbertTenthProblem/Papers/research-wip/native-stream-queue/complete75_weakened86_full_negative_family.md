# Complete negative-input zeros of the86 candidate at fixed scalar data

The [infinite outer-family theorem](complete75_weakened86_infinite_outer_family.md)
left the input and index congruences unpaid. This successor pays them,
then applies the [exact positive auxiliary lift](complete75_weakened86_auxiliary_sign_lift.md).
For the fixed scalar compiler constants

    B=16, cell_bits=4, inner_bits=1, MC=6, MF=12,

and any positive integers DC,DR, the [unchanged86 candidate](complete75_weakened_bound86_candidate.md)
has infinitely many **complete positive19-coordinate zeros at x=1** with
R<0, mu<0 and unbounded odd gaps. A concrete pair of main/first indices,
together with a deterministic Pell recipe for all19 coordinates, is
certified below. These assertions concern the actual full polynomial,
not only a subsystem or a formal ratio survivor.

The constants satisfy the compiler's scalar mask requirements. No
actual universal program with these constants is instantiated, and no
false-input zero is identified. Thus this theorem does not by itself
refute or prove a universal86 claim. The established75/87 results are
unchanged. No enormous full witness tuple is printed or evaluated:
exact modular identities, directed integer intervals and the proved
Pell identities certify the explicit recipe.

The [checker](complete75_weakened86_full_negative_family.py) and
[receipt](complete75_weakened86_full_negative_family.json) retain the
literal86=48M+38A source,19 positive supplied coordinates and degree203.
No source gate, finalizer or domain is changed.

## 1. Fixed data and the input branch

Use the width-four outer family:

    q=16, Jrep=1, X=8192, Y=4096, w=2, s=1,
    x=1, F=2, alpha=6, zplus=1, C=0,
    a=Y(X+1)=33558528, A=a+2=33558530,
    H=4a+3=134234115, E=XY=33554432,
    P=2XY^2+1=274877906945, Delta=A^2-1,
    M=q^2-1=255,
    K=q(q-F)M+MC+q(MF+B-1)=57558.                  (1)

Here MF=12 is the original mask; the literal source uses MF+B-1 in
the indicated packing term. The mask residues MC=2 modulo4 and MF=4
modulo8 hold, and their populations sum to4. The actual transport
factor is

    (DC+B*DR+X)C+(q-F)-zplus(q-1)=-1.             (2)

Thus arbitrary positive DC,DR disappear from this factor because C=0.

For Pell sequences write chi_A(t)+psi_A(t)sqrt(Delta) for the t-th
power of A+sqrt(Delta). Fix the input index v=9=2*cell_bits*x+inner_bits,
and set

    chi_v=chi_A(9), kappa=psi_A(9),
    Fv=chi_v+a*kappa,
    delta=(kappa-9)/Delta.                        (3)

The odd-index binomial congruence psi_A(9)=9 modulo Delta proves
integrality; the exact small recurrence proves delta>0. In particular

    Fv=27637344141379440275349388034199188837909049581666075532992334324937298.

We will keep this input root negative, mu=-chi_v. The letter delta in
(3) is the positive supplied coordinate, whereas Delta is the fixed
Pell discriminant.

## 2. An exact arithmetic progression paying the congruences

Fix the factor signs epsilon=-1, lambda=+1 and omega=-1. They are
compatible with transport sign-1, since epsilon*(-1)*lambda=1. The
integer46 below is a wrap coefficient, distinct from the supplied
auxiliary coordinate j.

Choose p=1 modulo4 and c=psi_A(p), and define

    N=K-2+p+46c-M*Fv,
    rho=N/(MH), Z=rho*H+Fv,
    R=K-MZ=-p-46c+2.                              (4)

Then the auxiliary target is

    R+epsilon-lambda=-p-46c=-p modulo c,           (5)

exactly the allowed target sign when p=1 modulo4. It remains to make
rho integral and to pay the main-root and first-index congruences.

The following return periods are verified by exact modular binary Pell
exponentiation; minimality is neither claimed nor needed:

    T_H=8758492,                   2^T_H=1 modulo H,
    T_M=24,                       (chi_A(T_M),psi_A(T_M))=(1,0) modulo M,
    L=5*6*T_H*T_M=6306114240,
                                  (chi_A(L),psi_A(L))=(1,0) modulo MH.

Also L is divisible by4 and2T_H. Here

    MH=34229699325,
    gcd(L,MH)=45,
    psi_A(13)=30187770076 modulo MH.

On p=13+Lz, c is constant modulo MH. Solving the single linear
congruence N=0 modulo MH gives the residue

    z=208720040 modulo (MH/45).

The checker computes this residue by an exact modular inverse, verifies
the original congruence, and obtains

    p0=1316212416417369613,
    S0=4796808763206686400.

Finally the exact Pell state at E modulo E is(1,0). Replacing the step
S0 by lcm(S0,E) therefore freezes both p and c modulo E. Put

    S=2514909272844107199283200,
    p=p0+S*t, t>=0.                               (6)

For every such p we have

    p=1 modulo4, 2^p=X modulo H,
    N=0 modulo MH, c=15494321 modulo E.            (7)

The main-root congruence from the outer theorem is
chi_A(p)-a*psi_A(p)=2^p modulo H. Consequently

    gamma=(chi_A(p)-a*c-X)/H                       (8)

is an integer. To pay the first-index equation, prescribe

    n=13587 modulo16777216=E/2.                   (9)

Since P=1 modulo E, its Pell recurrence gives psi_P(n)=n modulo E.
Thus, with k=2psi_P(n),

    k+p+46c-1=0 modulo E,
    h=(k+p+46c-1)/E,
    k-hE-R=-1=epsilon.                            (10)

No search through the enormous first-index period is used. The exact
return identities and the solved linear congruence prove(7)-(10) for
the entire progression; finite checks only supplement these identities.

## 3. Strict positivity before choosing the ratios

All p in(6) exceed13. Two fully materialized, small-index inequalities
checked at p=13 are

    psi_A(13)>M*Fv+K+13,
    psi_A(13)-psi_A(12)>X.                        (11)

The recurrence gives psi_A(p+1)>2psi_A(p). Thus the first inequality
persists as c>M*Fv+K+p for every integer p>=13, and the successive
psi differences increase, preserving the second. In particular

    0<N<47c<Mc,
    gamma*H=2c-psi_A(p-1)-X>c.                    (12)

Equations(7),(8),(12) imply positive integers rho and sigma=gamma-rho.
They also imply gamma>1. The values Z in(4), delta in(3) and h in(10)
are positive integers, and R<0. Substituting(3),(4) into the actual
input root gives

    C-Z+a*kappa+rho*H=-chi_v,
    mu^2-Delta*kappa^2=1.                         (13)

The negative sign is exact, not inferred from a finite fixture.

## 4. Infinitely many ratio hits with the prescribed first index

Let lambda_A=A+sqrt(A^2-1) and lambda_P=P+sqrt(P^2-1), and set

    theta=log(lambda_A)/log(lambda_P),
    beta=log(sqrt(P^2-1)/(2Y*sqrt(A^2-1)))/log(lambda_P),
    h_ratio=log((Y+1)/Y)/log(lambda_P),
    N0=E/2.

The outer theorem proves 1/2<theta<1 and theta irrational: the two
quadratic fields differ because the2-adic valuation of A^2-1 is even
and that of P^2-1 is odd; also A<P<2A^2-1. Here0<h_ratio<1.

Consider t_p=p*theta+beta with p restricted by(6). Its increments are
S*theta, so t_p modulo N0 is dense on the circle of length N0. This
uses only irrational rotation: S*theta/N0 is irrational. The elementary
pigeonhole proof in the outer theorem applies to every tail, hence the
open interval

    (13587+h_ratio/3, 13587+2*h_ratio/3) modulo N0   (14)

is reached infinitely often. On each hit set n=floor(t_p). Because
0<h_ratio<1, this n satisfies(9). The fractional part lies strictly
between h_ratio/3 and2h_ratio/3.

For completeness, the exact conjugate correction is retained. With
r=(Y+1)/Y, the dominant ratio R0 satisfies

    Y*r^(1/3)<R0<Y*r^(2/3),
    c/k=R0*(1-lambda_A^(-2p))/(1-lambda_P^(-2n)).

For all sufficiently large hits the correction lies between1-epsilon0
and1/(1-epsilon0), where epsilon0=1/[12(Y+1)]. The exact inequality
(1-z/3)^3>1-z for z=1/(Y+1) gives epsilon0<1-r^(-1/3).
The two strict bounds therefore imply

    kY<c<k(Y+1).                                 (15)

This is the same proved error margin as in the outer theorem, with
the additionally prescribed n residue. Since n/p tends to theta,
we have n<p<2n eventually and the odd gap2n-p tends to infinity.
No density assumption about two unrelated indices is made: both n
and its residue are obtained from the single rotation(14).

Define the remaining outer coordinates by

    eta=c-kY, zeta=k(Y+1)-c,
    tau_gap=chi_P(n)-XY^2*k.

The first two are positive by(15). Since P=2XY^2+1 and k=2psi_P(n),

    tau_gap=2psi_P(n)-psi_P(n-1)>0.

This pays the actual first norm and both ratio inequalities.

## 5. All five auxiliary coordinates and all eight factors

Every p in(6) is1 modulo4 and c is odd. The previously proved auxiliary
sign theorem applies to the target(5). A completely explicit positive
recipe, without a search for a sufficiently large auxiliary index, is

    m=2cp, f=chi_A(m), t_strong=psi_A(m),
    i=t_strong/c^2, T=Delta*t_strong,
    ell=p+2m, V=chi_T(ell)/T, y_aux=psi_T(ell),
    o=(V+c)/f, j=(V-p-46c)/c.                     (16)

The canonical composition proof gives c^2 dividing t_strong, and the
odd-index quotient identities give

    V=-c modulo f, V=p modulo c.

Thus every quotient in(16) is integral. Positivity of j also has a
uniform elementary bound: c>2p and c>=3, T>=c^2, ell>=3, whence

    V>=chi_T(3)/T=4T^2-3>=4c^4-3>47c>p+46c.

All five coordinates in(16) are positive. The first and auxiliary
Pell identities give their two norms equal to1; the linear factor
is lambda=+1 by(5).

Together,(1),(3),(4),(8),(10),(15),(16) specify exactly the19 supplied
coordinates

    Jrep,F,alpha,zplus,f,h,i,j,o,s,w,tau_gap,
    eta,zeta,y_aux,Z,delta,rho,sigma.

At those coordinates the literal factor values, in source order, are

    norm_first=1, norm_main=1, norm_input=1, norm_aux=1,
    norm_index=-1, norm_transport=-1, norm_strong=1, norm_linear=1.

Their product is1, so the actual final polynomial is zero. The checker
executes all86 literal rows under a symbolic substitution and proves
all eight factor formulas and the complete product identity. It also
checks192 exact rational arbitrary-point full-output identities,
including96 signed cases. The exact-division mapping also agrees on192
integer and rational input pairs and never produces floating-point values.
These latter identities are source audits;
the integer/positive full-zero conclusion follows from the proof above.

## 6. A concrete full19-coordinate recipe

The exact main/first indices

    p=3572130746085641437869936970845936422413,
    n=2381436634762533967520279822849047278867      (17)

satisfy(6) with t=1420381555969979 and satisfy(9). The checker verifies
all modular conditions in(7),(10) by modular Pell exponentiation.
It then certifies both strict inequalities(15) using the directed
integer interval algorithm of the outer packet at256 and384 bits.
The narrower intervals lie inside the wider ones. Each endpoint has
the exact meaning mantissa times2 to the stored integer exponent;
no giant bit string is constructed. The complete endpoint integers
are recorded in the receipt.

For example, the256-bit endpoints all share exponent
92876028755751323689141350997236597903101, and their mantissas are:

| Quantity | Lower mantissa | Upper mantissa |
|---|---:|---:|
| kY | 64897448891409855901917887706000893376664288730777577406587231958565157203991 | 64897448891409855901917887706000893377498482219313918313415552608870846425760 |
| c | 64905375903257910615531575821972679173086383959976793208269902744190762073493 | 64905375903257910615531575821972679173828808797230429689291884234777563926140 |
| k(Y+1) | 64913292995143110261268941877804116251023825910643489901071262044492541275574 | 64913292995143110261268941877804116251858223059699493000503788827769496534751 |

These strict endpoint separations certify an actual full-zero recipe,
not merely the existence supplied by density. Namely use(17) in the
formulas for all19 coordinates, including the fixed canonical auxiliary
indices(16). Their integrality, positivity and exact zero evaluation
follow from the preceding identities. The coordinate integers are
astronomical; their materialization is neither performed nor required.
The approximate continued-fraction search used to locate(17) is absent
from the checker and provides no part of the correctness certificate.

```sh
python3 complete75_weakened86_full_negative_family.py
```

Author receipt generation and the final fresh default replay pass. Root
read the full proof/source, inspected the exact-division helper, and
passed a fresh final default replay with no findings. Native independently
read the full proof/source and passed a fresh replay; its separate
recurrence-matrix modular oracle checked256 progression cases, and its
own literal executor/manual substitution checked256 complete eight-factor
and output identities, including128 signed cases. Its independent512-bit
rational/integer-square-root closed-form Pell oracle certified both
concrete strict ratios, all six enclosure bounds inside the saved384-bit
intervals, and the exact c bit length
92876028755751323689141350997236597903357. No giant Pell coordinates
were materialized. All five local links and whitespace checks pass.
Native also inspected the final exact-division delta and passed another
fresh default replay. An additional64 independent maps with180- to243-digit
signed integer arguments agreed exactly with Fraction and symbolic inputs,
with no floating values; manual quotient cross-products also passed.
The source, receipt and note are frozen after these reviews.

This packet proves full positive candidate zeros at the stated scalar data;
it does not identify those constants with an actual rejecting universal
program or assert a false-input zero.
