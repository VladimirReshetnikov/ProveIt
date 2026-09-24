# Dyadic balanced wrong indices for the weakened Pell kernel

The weakened **42=24M+18A Pell kernel** admits a positive solution with

    q=16, r=269, J=2r+1=539,
    actual main index p=329,
    X=2^329, Y=2^91, scale q^3=4096.

All ten kernel equations hold, including the first norm, the strict ratio
interval, both exponent/index quotients and both fixed-minus auxiliary
signs. Nevertheless

    v_2(binom(538,269))=popcount(269)=4<12,

so the required divisibility by4096 fails. Unlike the earlier rational
cubic family, this example has **odd r=2 modulo3**. Consequently the
even-tile-alphabet modulo-three restriction does not exclude every wrong
index of this weakened kernel.

This is a **kernel counterexample**, not a false raw-input witness for the
complete75 candidate. No actual compiler packing, spatial transport or
raw-input interface is attached. In particular q=16 is a kernel scale;
this note does not identify it with a power of a particular compiled
cell radix. Full75 soundness remains open, and the complete76 theorem is
unchanged.

The [checker](../verification/explore_dyadic_balanced_wrong_index.py) and
[receipt](../verification/explore_dyadic_balanced_wrong_index.json)
materialize the seven first/main equations and the finite auxiliary CRT
precursors. The enormous final auxiliary Pell coordinates are supplied
by the proved construction in
[the single-product auxiliary-scale note](EXPLORATION_SINGLE_PRODUCT_AUXILIARY_SCALE.md),
Section2; they are not expanded numerically.

## 1. Exact source and operation scope

The source is exactly the weakened kernel of the cited note. Write

    D0=q^3, X=wD0, Y=sD0, E=XY,
    a=Y(X+1), A=a+2, Delta=A^2-1, J=2r+1.

Its ten equations are

    (E^2+X)(Yk)^2 = tau(tau+1),
    c = Yk+eta,
    k = eta+zeta,
    k = r+1+hE,
    a = E+Y,
    d_main = X+ac+gamma(4a+3),
    d_main^2 = 1+Delta*c^2,
    i*c^2 = Delta*(f^2-1),
    Delta*(f^2-1)*((jc-J)^2-y_aux^2) = 1-y_aux^2,
    jc-J = of-c.                                           (1)

All supplied coordinates are positive integers. The dependency provides
the42 primitive instructions and their exact source-residual map. The
new checker reruns that source audit. No instruction or source equation
is changed here: replacing the published43-operation auxiliary-square
kernel by this42-operation kernel still gives only the existing
**75=40M+35A candidate**, whose soundness has not been proved.

## 2. An exactly balanced dyadic family

Choose an odd positive integer D and an odd divisor n>1 of2D^2+1. Put

    ell=(2D^2+1)/n,
    r=n+D-1, p=n+2D, J=2r+1,
    v=D-1+ell, X=2^p, Y=2^v.                              (2)

Then r and p are odd, p-1>r, and

    n=2r+2-p, J-p=n-1>0,
    nv=p(p-1-r)-(n-1).                                   (3)

The second identity follows because p-1-r=D and

    pD-(n-1)=n(D-1)+(2D^2+1)=nv.

Define the positive real root only as a useful identity:

    Froot^n=(X+1)^(p-1)/(2^(n-1)X^r).

Equation(3) gives exactly

    Froot^n=Y^n(1+1/X)^(p-1).                            (4)

No rationality of Froot is required. The essential choice is that its
leading dyadic factor is the integer Y. This avoids searching the binary
digits of a large irrational leading factor.

For the theorem below assume additionally that q is a power of two,
q>=16, and

    q^2<=r<q^4,
    q^3 divides X and Y,
    X>4pY,
    gcd(p,psi_A(p)) divides J,                            (5)

where A=Y(X+1)+2. These are explicit hypotheses, not conclusions for
every divisor in(2). To obtain a divisibility counterexample also require

    popcount(r)<3log_2(q).                                (6)

The two q16 examples below satisfy all these conditions. The separate
q8 numerical example illustrates the formulas but does not meet q>=16.

## 3. Strict first/main ratio

Use the Pell sequences

    chi_z(t)+psi_z(t)sqrt(z^2-1)=(z+sqrt(z^2-1))^t.

Set

    a=Y(X+1), A=a+2, Delta=A^2-1,
    E=XY, P=2XY^2+1,
    c=psi_A(p), d_main=chi_A(p), k=psi_P(r+1).

Writing m=p-1, the leading ratio is

    R0=(2a)^m/(4XY^2)^r
      =Y(1+1/X)^m.                                      (7)

Indeed the residual powers of2 andY cancel by(3). Elementary Pell
recurrence bounds, valid for z>=2 and t>=2, give

    (2z-1)^(t-1)<=psi_z(t)<=(2z)^(t-1).

Consequently

    c/k >= R0*(1+3/(2a))^m
                   /(1+1/(2XY^2))^r > R0 > Y.             (8)

For the strict comparison, m>r and
3/(2a)>1/(2XY^2), since3XY>X+1.

In the other direction, 2P-1>4XY^2 gives

    c/k < R0*(1+2/a)^m
        =Y*(1+(Y+2)/(XY))^m.                            (9)

The simplification is exact:

    (1+1/X)(1+2/[Y(X+1)])=1+(Y+2)/(XY).

For z>0 with mz<1, expansion against the geometric series gives
(1+z)^m<1/(1-mz). Here X>4pY and Y>=2 imply

    XY>m(Y+2)(Y+1),

because (Y+2)(Y+1)<=3Y^2 for Y>=2. Hence, for
z=(Y+2)/(XY), mz<1/(Y+1). Applying the geometric bound to(9) proves

    c/k < Y/(1-mz) < Y+1.                               (10)

Together(8)--(10) establish Y<c/k<Y+1. In particular

    eta=c-Yk>0, zeta=(Y+1)k-c>0

are integers and satisfy the two interval equations in(1).

The same estimates show Y<Froot<Y+1: from(4) and(7),
Froot^n/Y^(n-1)=R0<Y+1, while Y^n<Froot^n. Thus the chosen
power of two is also exactly floor(Froot), although this fact is not
needed to define the witnesses.

## 4. The seven first/main equations and their positive quotients

The two Pell norms hold by construction. Since P is odd, chi_P(r+1)
is odd, so

    tau=(chi_P(r+1)-1)/2

is a positive integer. The identity
P^2-1=4Y^2(E^2+X) then gives the first equation of(1).

As P=1 modulo E, the psi recurrence gives k=r+1 modulo E.
Strict growth gives k>r+1, so

    h=(k-r-1)/E

is a positive integer. The identity a=E+Y is immediate.

For H=4a+3=4A-5, the sequence

    chi_A(t)-(A-2)psi_A(t)

has initial values1,2 and is congruent to2^t modulo H by its
recurrence. Thus

    gamma=(d_main-X-ac)/(4a+3)

is integral. It is strictly positive because

    d_main-ac=2c-psi_A(p-1)>c>X.

Here p>=3, A>X, and psi_A(p)>A. This proves all seven
first/main equations with positive coordinates.

Conditions(5) also give positive integers w=X/q^3 and s=Y/q^3.
They imply a>q^6>J and E>=q^6>r+1; in particular J<c.
These are the retained preliminary size conditions, not a compiler
packing assertion.

## 5. Exact auxiliary extension

Let g=gcd(p,c), sigma=(-1)^((p-1)/2), and choose t0 by

    t0 = ((-sigma*J-p)/g)*(4p/g)^(-1) modulo c/g,
    (-1)^t0=-sigma.

The inverse exists, and c/g is odd, so adding c/g if necessary
achieves the parity condition. Put

    f=chi_A(2p)=2d_main^2-1,
    R=2Delta*c*d_main,
    i=4Delta^2*d_main^2,
    s_aux=p+4pt0,
    U=chi_R(s_aux)/R, y_aux=psi_R(s_aux),
    j=(U+J)/c, o=(U+c)/f.                                (11)

Section2 of the cited exact-g lemma proves, for precisely these
parameters,

    R^2=i*c^2=Delta*(f^2-1),
    U=-J modulo c, U=-c modulo f,
    R^2(U^2-y_aux^2)=1-y_aux^2.

It also proves that U,j,o,y_aux and all other auxiliary coordinates
are strictly positive integers. These identities supply the last three
equations of(1), since U=jc-J=of-c. The condition g|J is necessary
and sufficient for this prescribed construction, not for arbitrary
weakened-kernel auxiliary solutions.

The checker materializes c,d_main,f,R,i,t0,s_aux and checks the
CRT residue, parity, coefficient norm and size inequalities. It does
not evaluate chi_R(s_aux) or psi_R(s_aux); the lemma supplies those
enormous coordinates and their equations exactly.

## 6. Concrete examples and the failed neighboring candidate

|D|n|ell|q|r|p|J|v|gcd(p,c)|v_2 binom(2r,r)|
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
|59|211|33|16|269|329|539|91|1|4|
|35|817|3|16|851|887|1703|37|1|6|
|13|113|3|8|125|139|251|15|1|6|

The first row is primary. It has A=278 modulo329 and c=50
modulo329, so the exact auxiliary criterion holds. The checker
materializes c with138,089 bits and k with137,998 bits, verifying
all seven first/main residuals as zero. For q16 the required binomial
valuation is12, exceeding the primary value4 and secondary value6.
The third row has q8 and is explicitly outside the q>=16 theorem.

The nearby choice D31,n641,ell3 gives r671,p703,J1343,v33,
but gcd(p,c)=37 and J=11 modulo37. It therefore fails this CRT
extension, despite satisfying the dyadic balance. The checker retains
that rejection rather than silently treating coprimality as automatic.

Both q16 examples have r=2 modulo3. The existing even-alphabet
packing congruence allows that residue when the cell count is odd.
This defeats that particular exclusion argument; it does not produce
packed words, an allowed computation, or a false accepted input.

## 7. Verification boundary

The checker reruns the exact unchanged42-kernel/75-candidate source
audit from its dependency, verifies the parameter identities over all
odd divisors greater than one for odd D from1 through101, and checks
the three displayed examples with exact integer arithmetic. The seven
first/main equations, positivity, scale divisibility, strict ratios,
finite auxiliary precursors and failed neighboring CRT case are
checked directly. The final three auxiliary equations use the proved
exact-g construction; its enormous Pell outputs are not materialized.

The CLI writes the receipt only with `--write`; its default invocation
freshly recomputes and compares the complete JSON value. Dependency
hashes use CRLF-to-LF normalization. Author and two independent complete
scoped proof/source reviews pass, as do fresh default receipt checks.
