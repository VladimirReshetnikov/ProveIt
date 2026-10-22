# A direct twelve-positive-variable construction

## Status and comparison

This is a new ordinary algebraic reduction of the pinned native/Pell
construction, with a complete proof below.  It reduces the direct explicit
positive-variable family from thirteen to twelve variables.  It is not a
global variable minimum; Jones's separate nine-variable compiler remains a
different benchmark.  The reduction is not Lean/Rocq formalized.

The emitted literal product circuit has 151 operations (97 multiplications
and 54 additions/subtractions), exact total degree 1609, and twelve strictly
positive variables.  Its three-equation system has 147 operations and
maximum degree 1600.  This is a variable-count improvement and costs degree
and evaluator size.  `algebra12_build.py` emits `radical12_product.json`.

The four coefficient ports are one complete valid fixed-blank compiler tuple
`beta=B-1, Kconstant, MC, MF`, with the shifted MF convention.  This delivery binds the whole T4 tuple in
`../coefficients/T4_CONSTANTS.upstream.json`, through its established common
compiler interface.  The circuit port `Kconstant` is the coefficient named
`K0` in the package-wide coefficient evaluator.  The historical package06
tuple remains an alternative only as a whole tuple, not a source of mixed ports.

The original repository snapshot is
`f0ae4e0991ca44a7bb4e5671d42e33d775e48035`.

## 1. Formula

Retain the eleven positive variables

    J,F,alpha,z,h,i,T,s,w,eta,zeta

and add a positive variable `t`.  In all formulas below abbreviations are
polynomials, not quantified variables.  Put

    q=beta J+1, Cw=q-F-alpha, X=wq, Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y, H=4a+3,
    Delta=a^2+H=(a+2)^2-1,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J,
    Nk=k-hE-R,
    Nt=(Kconstant+w)Cw+q-F-z(q-1),
    Lfirst=E kY, A=1+Lfirst(Lfirst+k).

The crucial strong multiplier restriction is

    I=H i c^2, D=1+Delta I^2, Q=Delta^2 I^2, d=Q-1.

Thus the old normalized multiplier is `H i`, not `i`.  Also put

    v=cT, z0=c+RD,
    P0=Q D v^2, Z0=Q z0^2,
    e=P0+Z0-1, B=2Q v z0,
    M=2(D+v^2), G=1+Delta c^2,
    tauBound=Lfirst+k+1,
    fBound=(a+2)I+1,
    yBound=2(v fBound+z0),
    Ubound=M tauBound+yBound,
    ell=1+H Ubound,
    S=Ht+ell(ac+X), W=HM.

Define a finite polynomial norm as follows.  In the formal quotient ring
`Z[all retained variables,r]/(r^2-G)`, form

    Z=S-ell r,
    U=d(Z^2+W^2 A)-H^2 e,
    V=2dWZ,
    F0=U^2+A V^2-H^4 B^2 D,
    F1=2UV,
    F=F0^2-A F1^2.

Reduce the result uniquely to `F=F_even+F_odd r` by replacing every `r^2`
by G.  Define the ordinary integer polynomial

    R12=F_even^2-G F_odd^2.

The system is

    Nk=1, Nt=1, R12=0.

The single equation is

    P12 = Nk Nt (1+R12)-1 = 0.

No algebraic root, division, variable exponent, or quantified auxiliary
symbol occurs in this definition: the quotient-ring instruction is a fixed
finite polynomial computation.  The supplied JSON circuit expands it into
151 ordinary binary arithmetic gates.  In the circuit `H^4 B^2 D` is
evaluated as `4 H^4 P0 Z0`.

## 2. The inherited inequalities used here

The proof of package09's ROOT_AMALGAMATION_PROOF establishes, under the weak
transport/index assumptions `Nt=nu, Nk=epsilon` with equal signs in
`{1,-1}`, the coefficient bounds and elementary inequalities

    q>=16, 0<R<q^4-2, E>=q^4>R+2,
    k=R+epsilon+hE>R,
    A>8(c^2+R^2),
    d(D+v^2)^2 A > Q(Dv^2+z0^2) = e+1.

That derivation uses neither the main root nor gamma.  Replacing the old
normalized multiplier by H*i does not affect it.  Since our M is twice the
old weight, we obtain the stronger bound

    d M^2 A > 4(e+1).                              (2.1)

All of `H,I,D,Q,d,v,z0,B,G,A,M` are strictly positive, with d>=1, D>1,
G>1 and A>1.  Moreover `B sqrt(D)<=e+1` by `(v sqrt(D)-z0)^2>=0`.

## 3. Radical interpretation is only a proof device

The polynomial R12 is the product, over the eight choices

    r=+-sqrt(G), f=+-sqrt(D), tau=+-sqrt(A),

of the factors

    d(S-ell r-HM tau)^2-H^2(e-Bf).                 (3.1)

This follows by first taking the quadratic norm in f, then in tau, then
in r.  It can also be verified by direct expansion of the displayed
formula.  Thus a zero of R12 gives roots r,f,tau and a real number y such
that

    r^2=G, f^2=D, tau^2=A,
    d y^2=e-Bf,
    S=ell r+H(M tau+y).                           (3.2)

The first three roots are real because G,D,A>0.  The last equality makes
y real.  Conversely any tuple (3.2) gives R12=0.

## 4. Uniqueness of the radical tuple

For any real branch, using Q/(Q-1)<=2,

    |y|^2 = [Q(vf-z0)^2-1]/d
            <2(v sqrt(D)+z0)^2,
    |y| <2(v fBound+z0)=yBound.

Also `sqrt(A)<tauBound` and `sqrt(D)<fBound`; the latter follows from
`D=1+((a+2)^2-1)I^2 < ((a+2)I+1)^2`.
Consequently

    |M tau+y| < Ubound.                           (4.1)

The doubled weight and (2.1) give

    M^2 A > (e+B sqrt(D))/d >= |y|^2.              (4.2)

Indeed the numerator on the right is at most `2(e+1)-1` whereas the left
after multiplication by d exceeds `4(e+1)`.

Suppose two radical tuples satisfy (3.2) for the same rational S.
If their r signs differ, the magnitude of their r contribution is
`2 ell sqrt(G)>2H Ubound`, larger than the difference of their remaining
contributions by (4.1).  Hence r must be identical.
Then `t0=M tau+y` is identical.  If their tau signs differ, their tau
contribution has magnitude `2M sqrt(A)`, exceeding the difference of the
y contributions by (4.2).  Thus tau is identical; then y is identical;
then f is identical by `d y^2=e-Bf`, because B is nonzero.
Thus the radical tuple is unique among all real branches.  An algebraic
conjugate with imaginary y cannot satisfy (3.2), since all other summands
are real.

Every embedding of the number field generated by r,f,tau,y fixes S and
the integer coefficients and produces another allowed tuple.  Uniqueness
therefore fixes each generator under every embedding.  In characteristic
zero each generator is rational.  Equivalently this conclusion follows
by taking a normal closure and using the fixed field of its Galois group.

## 5. Rational roots are integral; gamma is restored

Since r,f,tau are rational and their squares are integers, all three are
integers.  From (3.2), H*y is an integer.  Write y=u/v in lowest terms.
Then v|H and `v^2|d`, since `d y^2=e-Bf` is an integer.  But

    Q=Delta^2 H^2 i^2 c^4,
    gcd(H,d)=gcd(H,Q-1)=1.

Hence v=1: y is an integer.  Now define

    gamma=(r-ac-X)/H.

The identity (3.2) gives `t=ell gamma+M tau+y`.  Hence ell*gamma is an
integer; the denominator of gamma divides H, and `ell=1+H Ubound` is
coprime to H.  Thus gamma is an integer as well.

This restores exactly the main Pell norm, normalized strong equation,
first norm, and auxiliary norm:

    (ac+X+gamma H)^2-Delta c^2=1,
    f^2-Delta(H i)^2 c^4=1,
    tau^2=1+Lfirst(Lfirst+k),
    Q Vaux^2-(Q-1)y^2=1,
    Vaux=c(Tf-1)-R f^2.

The identity for Vaux uses `f^2=D`.
The restored y is nonzero: otherwise the auxiliary norm would give
`Q Vaux^2=1` with integral Vaux and Q>1.  The roots f and tau are
nonzero because D,A>1.  Thus taking absolute values of tau and y
preserves the equations and supplies their required positive values.

The recovered f,tau,y,gamma may have signs.  This is covered by the
signed-domain proof of package14, and the signed-quotient proof used in
package09: their soundness arguments require the multiplier nonzero,
positive X,Y, and the retained positive ports; oddness of the multiplier
and squareness of w are only particular sufficient conditions in their
29-integer parameterization.  Here the multiplier H*i is strictly
positive and w is positive, so these conditions hold directly.  The
Pell rank argument recovers p=R; signed gamma is then forced to the
positive main-root branch using the short residue interval.  Thus a
blank accepting K215 tableau is decoded.  This step must be stated
explicitly; the old positive-gamma theorem alone would not suffice.

## 6. Completeness with the restricted multiplier

Start with a canonical positive blank-tableau witness in the established
compiler.  Its main index R satisfies `R=3 (mod 4)`, its main values are
`c=psi_{a+2}(R)` and `r=chi_{a+2}(R)`, and gamma is positive.  All basic
coordinates and tau can be kept.  We rechoose only the strong and auxiliary
witnesses to force the old multiplier divisible by H.

Put N=H*c^2 and let

    M_R = [[chi_{a+2}(R), Delta psi_{a+2}(R)],
           [psi_{a+2}(R), chi_{a+2}(R)]].

Its determinant is 1.  Reduction modulo N is an element of the finite
group SL_2(Z/NZ), whose cardinality is at most N^4.  Its order divides
`(N^4)!`.  Take `m=R*(N^4)!`.  The Pell multiplication law yields
`psi_{a+2}(m)=0 (mod N)`.  Set

    i=psi_{a+2}(m)/(Hc^2)>0,
    f=chi_{a+2}(m)>0,
    rho=Delta psi_{a+2}(m),
    Vaux=chi_rho(R)/rho,
    y=psi_rho(R)>0.

Oddness of R makes Vaux an integer.  The usual odd quotient polynomial
identities, with R=3 modulo4, give

    Vaux=-c (mod f),  Vaux=-R (mod c),
    f^2=1 (mod c).

These identities hold for the new m; they do not depend on retaining the
old strong witness.  To check them: rho^2=-Delta=1-(a+2)^2 modulo f and
rho^2=0 modulo c, and the odd Chebyshev quotient evaluated at these two
arguments gives the stated signs.  Define

    o=(Vaux+c)/f,
    T=(o+Rf)/c.

Both are positive integers.  Integrality of T follows from
`of=-R (mod c)` and `f^2=1 (mod c)`.  Their definition gives the exact
Vaux polynomial in Section 5.  Finally set

    t=ell gamma+M tau+y>0.

Then (3.2) holds, so R12=0.  This proves completeness without assuming
that every old witness already satisfies the new divisibility restriction.

## 7. Single equation and sign recovery

At a zero of P12 all three integer factors are units.  Since
`Delta=0 or3 (mod4)`, we have `G=1+Delta*c^2=0 or1 (mod4)`.
The norm `R12=F_even^2-G F_odd^2` cannot be 2 modulo4.  Consequently
`1+R12` cannot be -1 and must be 1.  Thus R12=0 and Nk,Nt have equal
signs epsilon.  The inherited inequalities in Section2 deliberately
permit those signs.  Sections3-5 restore the signed Pell witnesses.
The inherited signed rank and ratio proof then forces epsilon=1 and
decodes acceptance.  Completeness gives a positive zero with all factors1.

Therefore both the system and the single polynomial are solvable exactly
when the blank K215 machine halts.  Composing with its established finite
ZFC-refutation calibration and negating gives the desired equivalence,
formalizable in ZFC.  This is an equivalence theorem, not a consistency
proof or a newly checked formal-assistant theorem.

## 8. Exact degree certificate

All retained unknowns have degree1 and the four fixed ports have degree0.
The relevant exact degrees are

| object | degree |
|---|---:|
| X,Y,E,k,c,a,H,Delta,R | 2,4,6,1,5,6,6,12,4 |
| Lfirst,A,I,D,Q,d | 11,22,17,46,58,58 |
| v,z0,e,B,M | 6,50,158,114,46 |
| tauBound,fBound,yBound,Ubound,ell | 11,23,50,57,63 |
| G,S,W | 22,74,52 |

For a uniform proof make the substitution of every unknown by lambda
times a corresponding independent indeterminate, and work with formal
Laurent series at lambda infinity over the resulting characteristic-zero
coefficient field.  The two roots of G have expansions

    r_+=ac+2c+terms of degree below5,
    r_-=-r_+.

Hence `Z_+=S-ell r_+` has exact degree68 and leading form
`-2 ell_top c_top`; `Z_-` has degree74 and leading form
`2 ell_top a_top c_top`.  Both roots of A have degree11, so `W tau`
has degree63 and is lower than either Z.  Both roots of D have degree23.
Consequently in each factor (3.1) the leading term is `d Z^2`:
the subtracted `H^2 e` has degree170 and `H^2 Bf` degree149, whereas
`d Z_+^2` has degree194 and `d Z_-^2` degree206.  There are four factors
of each kind, giving exact degree

    deg(R12)=4*194+4*206=1600.

Its nonzero leading form is

    2^16 d_top^8 ell_top^16 a_top^8 c_top^16.

The degrees of Nk and Nt are7 and2 with nonzero leading forms.  Therefore
the final product has exact degree1609.  This is a formal coefficient-field
calculation, not an asymptotic numerical guess; the nonzero leading forms
also show that every valid fixed beta produces the stated degree.

## Principal source dependencies

Paths below are beneath
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/`:

* `09-combined13/proofs/ROOT_AMALGAMATION_PROOF.md`: weak-sign bootstrap,
  domination of the weighted radicals, signed quotient restoration.
* `09-combined13/upstream/compiler/06_fixed_blank_67_proof.md` and
  `06_pell_lemma_audit.md`: canonical blank compiler and Pell completeness.
* `14-integer29/proofs/signed_domain_proof.md`: signed gamma, normalized
  rank, unsigned main-root recovery, and canonical odd-rank congruences.
* `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` (from
  repository root): machine/refutation endpoint; its formal status does
  not extend automatically to the new Diophantine reduction.
