# Equal-diagonal relators permit a cheaper quotient consumer

For every noncentral integral relator P with equal diagonal entries,
the existing signed two-form quotient append has an exact10M+9A
schedule, instead of10M+10A. If either of the relatively prime reduced
off-diagonal entries is a unit, the cost is9M+9A. In particular the whole
previous unit-pivot obstruction family admits the latter18-operation
append. Its common-basis obstructions remain valid; they were never
circuit lower bounds.

This is a local all-integer identity on the unchanged four signed inputs
and three output accumulators. It changes no input form, selector lane,
positive guard or witness. It does not assert that these relators occur
in the unmaterialized universal alphabet, or reassign a lower operation count to an
already frozen complete source. Root requested a bounded exploration
of independent input/output bases and simultaneous quotient consumers.

## 1. Retained cut and equal-diagonal left invariant

Keep the quotient-pair note's exact definitions. For a fixed P in SL2(Z),
put A=S(P), retain its integral two-row matrix V and right inverse J0,
and set

    E=(A-I3)J0, T=V*A^-1*J0.

The inherited identities are

    A-I3=E*V, S(P^-1)-I3=-E*T*V, T in SL2(Z).

Thus the increment on arbitrary integer signed inputs t_+,t_- is

    E*z, z=t_+-T*t_-.                                    (1)

Its three coordinates are appended to the original ordered accumulators
(d,e,f). Computing z by the original dense quotient schedule costs4M+4A:
four fixed-coefficient products, two sums and two subtractions. Here M
counts multiplication, including by a supplied fixed integer, and A
counts either addition or subtraction. No off-zero positivity of the
signed cut is required or claimed.

Now suppose

    P=[p,q;s,p], p^2-q*s=1, (q,s)!=(0,0).                 (2)

The last condition excludes only the central matrices among this class.
The representation is

    A=[p^2,-2pq,q^2;
       -ps,p^2+qs,-pq;
       s^2,-2sp,p^2].                                    (3)

The integer row n=(s,0,-q) satisfies n*A=n: its three product coordinates
are s*(p^2-qs)=s,0 and -q*(p^2-qs)=-q. Consequently n*E=0. Writing E_i
for row i of E gives

    s*E_1=q*E_3.                                         (4)

This argument uses the actual E derived from the fixed relator, not
arbitrary independent coefficient ports.

## 2. Integral common row and the19-operation append

Let g=gcd(|q|,|s|)>0, q0=q/g and s0=s/g. Choose fixed integers alpha,beta
with alpha*q0+beta*s0=1, and prepare the integer two-entry row

    k=alpha*E_1+beta*E_3.                                 (5)

Dividing(4) only in the fixed integer relation gives s0*E_1=q0*E_3.
Then q0*k=E_1 and s0*k=E_3 by the Bezout identity. Hence

    E*z=(q0*(k*z), E_2*z, s0*(k*z))^T.                  (6)

The same proof covers q=0 or s=0: the other reduced entry is a unit,
and the corresponding zero E row causes no division by zero. Preparing
g,alpha,beta,k is fixed coefficient arithmetic, not a runtime operation.
There are no runtime divisions or supplied divisibility assumptions.

The fully appended schedule after z is

    k1z=k1*z1; k2z=k2*z2; u=k1z+k2z;
    e1z=E[2,1]*z1; e2z=E[2,2]*z2; v=e1z+e2z;
    first=q0*u; third=s0*u;
    d'=d+first; e'=e+v; f'=f+third.                       (7)

The two scalar forms cost4M+2A, the two scales cost2M, and the three
appends cost3A. Thus the consumer costs6M+5A and the complete local
append costs

    (4M+4A)+(6M+5A)=10M+9A.                              (8)

All products in(7), including any zero or unit products, may be retained
in this uniform template. Its exact saving from the original10M+10A
append is one addition. The coefficient interface can use the four
entries of T, two entries each of k and E_2, and q0,s0; every one of
these ten fixed roles is tied to(2)--(5).

## 3. A unit reduced entry saves one more product

If q0=+/-1, then rho=s0/q0 is an integer and E_3=rho*E_1. Compute the
two forms E_1*z and E_2*z directly at4M+2A, form rho*(E_1*z) at1M,
and append all three coordinates at3A. The consumer is5M+5A, giving

    (4M+4A)+(5M+5A)=9M+9A.                               (9)

The sign is absorbed into the fixed integer rho; no runtime negation
or extra coordinate transform is omitted. If instead s0=+/-1, use E_3*z
and E_2*z, scale the former by q0/s0 for the first coordinate, and append
in the original(d,e,f) order. The same count applies. In particular the
noncentral triangular cases are covered. We retain all other products,
even if a further special coefficient is zero or a unit.

For the previous obstruction family g>=3, put

    p=g^2+1, h=g^2+2, P_g=[p,g;g*h,p], L=p*g.

The retained quotient uses

    J0=[0,0;-1,0;0,1],
    T=[2p^2-1,-L;-4hL,2p^2-1].

Directly multiplying the handwritten expression for S(P_g)-I by J0
gives

    E=[2L,g^2;
       -2g^2*h,-L;
       2hL,g^2*h].                                      (10)

The third row is exactly h times the first, so(9) applies with rho=h.
This proof has not evaluated a stored source or coefficient array.

For example g=3 gives

    E=[60,9;-198,-30;660,99],
    T=[199,-30;-1320,199].                               (11)

The previous proof still excludes a unit entry in every common integral
conjugate of T, a unimodular cyclic basis and a rational triangularization.
The saving here comes from the original output consumers instead. The
prior equal-diagonal3M+3A quotient product can also be used: its core
with the two differences costs3M+5A, giving8M+10A with this5M+5A
consumer. This is another18-operation schedule, not a further saving.

## 4. What independently changing the bases actually requires

For any fixed C_+,C_- in GL2(Z), define

    y_+=C_+*t_+, y_-=C_-*t_-,
    T'=C_+*T*C_-^-1, E'=E*C_+^-1.

The exact original-coordinate increment is

    E'(y_+-T'*y_-)=E*(t_+-T*t_-).                        (12)

All these fixed coefficients are integral. This legitimizes independent
bases algebraically, but both input conversions and all three consumers
belong in a paid schedule. At this local cut the formed input words
already exist; changing their recipes is a different source task.

For example C_+=T^-1,C_-=I makes T'=I and E'=E*T. A literal dense
implementation still pays4M+2A for y_+=T^-1*t_+, then2A for y_+-t_-,
then6M+6A for the E*T append:10M+10A again. This is a valid comparison,
not a lower bound for every independent-basis implementation.

**Remark 1 (refuted free identity-side conversion).** It is false that
one can make T'=I, replace E by E*T, and leave both runtime inputs
unchanged. At(11), with t_+=(1,0)^T,t_-=(0,0)^T and zero accumulators,
the correct increment E*t_+ is(60,-198,660)^T. The omitted-conversion
formula E*T*t_+ is(60,198,660)^T. The middle outputs differ by396.
This is a counterexample at the exact arbitrary-integer cut, not a
claim of a genuine native history with those values. Equation(12),
which includes the conversion, remains valid.

**Remark 2 (the old basis obstruction is not a consumer lower bound).**
The stronger inference that the P_g family cannot admit any append
below20 operations is refuted by(9)--(10). The previous frozen note
explicitly excluded that inference. Its no-pivot/no-cyclic-basis/no-
triangularization results are unchanged, and neither that note nor this
one proves a generic arithmetic-circuit lower bound.

**Open question 1 (general relators and complete composition).** Root
asked whether independent bases or simultaneous E/T factorization can
improve the generic append. The present result settles only the stated
equal-diagonal subclass. An arbitrary P need not have equal diagonals,
and no free conversion to that class is asserted. Whether another paid
schedule improves the generic cut, or whether any actual fixed universal
relators satisfy(2), remains open here. Only a separately emitted and
audited complete source may incorporate any resulting occurrence-based
saving. No current whole-compiler total, degree or source liveness is
changed by this note.

## 5. Provenance and execution boundary

The author found the two-operation consumer saving on the earlier
pivot-obstruction family while pursuing root's independent-basis task.
The author and root then independently obtained the equal-diagonal
primitive-row extension. Root subsequently read the complete draft and
independently checked n*A=n, the Bezout reconstruction including zero
and sign cases, both paid append counts, the explicit E family, the
omitted-conversion counterexample, and all independent-basis identities
and charges. The full mathematical challenge passed with no correction.
His terminology clarification in the opening was applied before freeze.

All new identities and operation ledgers are handwritten. Dependencies
were read as inert text. No supplied, archived, committed, predecessor
or frozen helper was executed or imported; no saved scientific source
or coefficient array was evaluated or degree-propagated. No scientific
sampling, source emitter or build was used. Only fresh byte/read-span
metadata may accompany the proof. New files remain in/tmp; repository
files, Git and earlier frozen artifacts are unchanged.
