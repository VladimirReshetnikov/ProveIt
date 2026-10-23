# A root-centered equation in thirteen positive integers: degree 114, 83 operations

## Result and fixed interpretation

The explicit polynomial in `polynomial.json` has exactly thirteen strictly
positive integer unknowns, total degree **114**, and **83** live binary
arithmetic operations: 46 multiplications, 19 additions and 18 subtractions.
Squares and multiplication by fixed scalars count as multiplications.
Intermediate registers are abbreviations, not additional unknowns.

Use the whole compact44 native tuple, with `beta=2^590069-1`. Its four actual
payloads, compressed and raw hashes, and aliases are fixed by
`COEFFICIENT_BINDING.json`. The port `MF` is the already shifted
`MF_source=MF_native+2^590069-1`. No port is mixed with another tuple.
The compact-tuple proof supplies the same native blank-machine interface;
the ordinary strong equation below is related to its canonical normalized
witness by `i_ordinary=Delta*i_normalized`.

ZFC proves that the polynomial has a positive integer zero if and only if
the fixed syntactic ZFC proof predicate has a finite refutation. Consequently
ZFC proves that its lack of positive integer zeros is equivalent to
`Con(ZFC)`. The inherited native compiler and literal K215 calibration are
ordinary mathematical dependencies. This package is not a new end-to-end
proof-assistant certificate and does not prove either consistency or
inconsistency.

At the thirteen-positive frontier, the construction reduces the source59
adjunct's degree126/91-operation point to degree114/83, and reduces the
source57 degree132/83 point's degree at the same operation count. Those
comparisons concern the named authenticated constructions, not a universal
minimum or literature priority.

## 1. Complete definition

Supply the thirteen positive integers

    J,F,alpha,z,f,i,T,s,w,eta,zeta,gamma,t.

Every other letter is the following polynomial abbreviation:

    q=beta J+1, C=q-F-alpha,
    X=wq, Y=sq^3, E=XY, k=eta+zeta,
    c=kY+eta, a=E+Y, H=4a+3, Delta=a^2+H,
    ell=E kY, A1=1+ell(ell+k), G=1+Delta c^2, b0=X+ac,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J,
    Nt=(K0+w)C+q-F-z(q-1),
    U=4q^4, r=k-R-1,
    Dstar=U b0+H(U gamma-r), Nmain=Dstar^2-U^2 G,
    I=i c^2, Q=Delta(f^2-1), d=Q-1, Ns=I^2-d,
    V=c(Tf-1)-R f^2, Eaux=Q V^2-1,
    x=t+ell, delta=x^2-A1,
    N=(d delta-Eaux)^2-4d A1 Eaux.

The equation is

    P13 = Nt(1+Nmain)Ns(1+N)-1 = 0.                (1)

The literal circuit uses `Cw` for `C` and `delta` for `x²-A1`, to distinguish
both from fixed coefficient names and `Delta`. All powers have fixed
nonnegative exponents. The term `z` here is the positive **old product**
transport coordinate. It is one greater than the shifted coordinate used
in the Q42 quartic's equation `(K0+w)C=F+z_shift(q-1)`. They must not be
identified without that shift.

## 2. The centered two-root norm

For arbitrary values of four indeterminates d,x,A,e, one has the exact
polynomial identities

    (d(x^2-A)-e)^2-4dAe
      = (d(x^2+A)-e)^2-4d^2 x^2 A
      = d^2(x^2-A)^2-2d(x^2+A)e+e^2.             (2)

The first form saves one multiplication relative to the middle form, and
the middle form exposes the rational square root. Suppose d,x,A are
positive integers and the common expression vanishes. Then

    tau0 = [d(x^2+A)-e]/(2dx)

is rational and has square A. A rational square root of an integer is an
integer. Thus `tau0` is an integer, possibly negative, and

    d(x-tau0)^2=e.                               (3)

This elementary two-root elimination needs no independence assumption on
square classes, no auxiliary integrality saturation, and no choice of
independent Galois signs. It is a direct consequence of (2).

The meaningful centering is `x=t+ell`. Its exact cancellation is

    delta=t^2+ell(2t-k)-1.                       (4)

Thus delta has degree12 rather than the apparent degree22 of either square
term separately. Completeness will use `t=tau-ell+y>0`; the positivity of
this shifted coordinate is part of the proof, not an arbitrary affine
substitution on all parent tuples.

## 3. Product-unit guard and root restoration

At a positive integer zero of (1), its four integer factors are units.
The residue of Nmain modulo4 is the square Dstar², because U is a multiple
of4. The residue of N modulo4 is the square `(d delta-Eaux)²`. Consequently
neither Nmain nor N can equal −2; both are zero and both corresponding
factors equal +1.

For every integer a, `Delta=a²+4a+3` is 0 or3 modulo4. Therefore
`Q=Delta(f²-1)` is 0 or1 modulo4. Since I² is 0 or1 modulo4,
`Ns=1+I²-Q` is 0,1 or2 modulo4, never −1. Thus Ns=+1, so

    Q=I^2,  Nt=1,  Nmain=0,  N=0.              (5)

All input coordinates are positive; in particular c>1 and I=ic²>1.
Hence Q>1 and d>0. The case f=1 is automatically excluded by (5), so no
extra shift of f is needed. Also x=t+ell>0 and A1>0.

If V=0, then Eaux=−1 and the first norm in (2) is

    (d delta+1)^2+4d A1>0,

contrary to N=0. Thus V is a nonzero integer and Eaux=Q V²−1>0.
Apply Section2 with A=A1 and e=Eaux. It gives an integer tau0 with
tau0²=A1 and an integer y0=x−tau0 with d y0²=Eaux. Define

    tau=abs(tau0)>0,  y=abs(y0)>0.

These restored roots satisfy exactly

    tau^2-ell(ell+k)=1,
    Q V^2-(Q-1)y^2=1,
    (ic^2)^2=Delta(f^2-1).                       (6)

The equality `ell(ell+k)=(XY²)(XY²+1)k²` follows from ell=XY²k.
Together with Nt=1 and Nmain=0, (6) is the entire ordinary-strong
fourteen-coordinate absorber of source50, with the original positive
T and all other retained coordinates. We have not yet invoked a rank
theorem or assumed that the absorbed quotient is positive.

## 4. Why the absorber restores the omitted quotient

The exact original proof is included as
`upstream/FOURTEEN_ABSORPTION_PROOF.md`; its SHA256 is
`697e3e39bbcdca7d72d04db2802777cb0a1df17c1aa146100c056412b64471a3`.
The argument is restated to make its order explicit.

Nt=1 first gives C>0. Indeed if C<=0, then
`Nt <= 1-F-(z-1)(q-1)<=0`, a contradiction. The authentic complete
tuple's mask bounds yield

    q>=16, 3q<R<q^4-2, E>=q^4>R+2,
    kY<c<k(Y+1), a+2<2E.

Nmain=0 makes `g=Dstar/U` a rational square root of the integer G, hence
an integer. It is positive: H<5a, b0>akY, r<k and gamma>0 give

    Dstar>U b0-Hk>ak(UY-5)>0.

Thus `g²-Delta c²=1`. Modulo U the defining carrier gives
`U | H(k-R-1)` without canceling H prematurely.

Put A0=a+2 and P0=2XY²+1. Ordinary Pell classification gives p,n>=1 with

    g=chi_A0(p), c=psi_A0(p),
    tau=chi_P0(n), k=2psi_P0(n).

Since P0>A0 and c>k, one has p>n. The first recurrence gives
`k=2n modulo4XY²`. This modulus is a multiple of U. Also H is odd,
H=3 modulo q, and if3 divides q then H=3 modulo27. Thus
`gcd(U,H)<=3`; with `mu=U/gcd(U,H)` one obtains

    mu>=4q^4/3>R+1,
    2n=R+1 modulo mu,
    n>=(R+1)/2>=25.

This lower bound is obtained before recovering p=R. Consequently p>=26
and Pell growth gives

    c>A0 Delta^2, c>2p, c>2R.                   (7)

The ordinary strong-rank lemma, with its now-verified strict hypothesis,
applies to `(ic²)²=Delta(f²-1)`. It gives

    f=chi_A0(m), p|m, c|m, m>=c>2p,
    I=Delta psi_A0(m), c^2|(f^2-1).            (8)

This is the proved rank lemma in `upstream/ORDINARY_BLANK_PROOF.md`, Section4;
it handles the possible nonfundamentality of A0 in the underlying Pell
group. Equation(8) is not inferred by dividing the strong equation by Delta.

The auxiliary Pell equation in (6), `V=-c modulo f`, and the odd abscissa
quotient identity give an odd index j0 with `j0=+p or -p modulo m`.
The additional congruences `Q=0 modulo c`, `f²=1 modulo c`, and
`V=-R modulo c` give `j0=+R or -R modulo c`. Since c|m and
0<p,R<c/2 by (7), the signed index theorem implies p=R. The proof of this
signed step is included in the ordinary source, Section5; it does not
require V to be positive.

Now n<p=R and |2n-R-1|<R<mu, forcing 2n=R+1. Therefore
`r=k-2n` is divisible by4XY², and hence by both E and U. Restore

    h=r/E, gamma_old=gamma-r/U.

The first is positive because psi_P0(n)>n for n>=25. The second equals
`(g-b0)/H`; since n>=2, k>=4P0>X, c>X, and g>(a+1)c, it is also positive.
All fifteen positive ordinary compiler coordinates have now been restored.
Its inherited soundness yields a blank K215 halt and a finite ZFC refutation.

## 5. Constructive completeness

Start with a canonical positive ordinary compiler witness of a blank K215
halt. Canonical normalized witnesses yield these ordinary witnesses by
`i_ordinary=Delta*i_normalized`. Its established index theorem gives
p=R=2n-1, so `r=k-2n` is a positive multiple of4XY², hence of U.
Set

    gamma=gamma_old+r/U,
    t=tau-ell+y.

Both are integers and positive. For t this follows from
`tau²=1+ell(ell+k)>ell²`, so tau>ell, and y>0. Retain the other eleven
coordinates. Then x=t+ell=tau+y, `Eaux=d y²`, and
`A1=tau²`. Identity(2) gives N=0; the carrier gives Dstar=Ug and
Nmain=0. Nt=Ns=1 are unchanged. Hence (1) has a positive integer zero.

This is an explicit existence-preserving construction. It does not assert
that every parent root pair has a fixed sign relative to an arbitrary t,
or that every old positive tuple is carried by a linear bijection.

## 6. Exact degree and operation count

All thirteen unknowns have degree1; fixed ports have degree0. Put

    q0=beta J, E0=w s q0^4,
    k0=eta+zeta, c0=k0 s q0^3, ell0=E0 c0.

The degrees of E0,c0,ell0 are6,5,11. The inner quantities have

    deg Q=deg d=14, deg V=7, deg Eaux=28,
    deg A1=22, deg delta=12.

The three terms of the last expression in (2) have degrees52,64,56.
Only the middle term reaches64, so

    N64=-4 E0^6 c0^4 T^2 f^6.                  (9)

Equivalently, the efficient evaluator's square has degree at most56 and
its correction `-4d A1 Eaux` has exact degree64.

For the main residual use the exact cancellation identity

    Nmain=U^2[2ac(X+H gamma)+(X+H gamma)^2-Hc^2-1]
          -2UH r(X+ac+H gamma)+H^2 r^2.

The displayed terms have degrees26, at most25, and at most20. Thus

    (Nmain)26=128 q0^8 E0^2 c0 gamma.

The remaining factors have degree22 and2, with leaders

    (Ns)22=i^2 c0^4,
    (Nt)2=w(q0-F-alpha)-z q0.

Therefore degP13<=114. Substituting every supplied variable by the single
indeterminate z gives a coefficient of

    2^19 beta^67

at z^114: Nt has leader−2, Nmain has leader256 beta^19, Ns has
leader16 beta^12, and N has leader−64 beta^36. This number is nonzero on
the actual fixed coefficient slice, proving **exact degree114**.

The gate list contains exactly83 binary gates, all live. The independent
checker does not import `build.py`. It authenticates the complete tuple
and source pins, verifies41 named formulas against the gate list by
independent sparse polynomial arithmetic, proves all three norm identities
and the main cancellation, checks the universal weighted degree bound,
and evaluates six complete polynomial rays over three finite fields using
the actual fixed tuple. Normal and optimized Python agree. These finite
checks support transcription and degree, not the unbounded semantic theorem.

## 7. Reproduction and provenance

Run `python3 build.py` followed by `python3 check.py`. Both use only the
standard library. `section.tex` contains the mathematical section for the
combined report. The compact native builder and transition data are included
under `upstream/`; their complete reconstruction is also replayed in the
accompanying nine-variable package.

All fetched sources have exact provenance in `SOURCE_PINS.json`, at the
current repository commit `beb0192cb8dc36f78c369c080f2adfbc1887a486` or an
explicit historical pin. Upstream mathematical prose is retained unchanged.
The coefficient proof, the ordinary strong-rank proof, the source50 absorber,
and source59 merger/comparator are included. The mathematical reduction
was developed and reviewed by separate agents within one AI-assisted
session; this is internal review, not external peer review.
