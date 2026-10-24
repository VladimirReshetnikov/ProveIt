# Independent audit: the unweighted thirteen-integer equation

## Finding and scope

The proposed unweighted construction is mathematically sound relative to the exact ordinary native/refutation calibration imported from source 34, the source-71 determinant guard, and the incoming `ZFC_Diophantine_Joint_Guards_2026-10-24` affine residue-oriented parent. It defines one ordinary polynomial over the integers in thirteen unrestricted integer variables. Its exact total degree is 1408. It uses the same six fixed coefficient ports as the parent, without the additional coefficient majorants of the earlier weighted construction.

This note independently checks the reduction, especially the order of the realness and positivity arguments, all possible degenerate cases, the separation needed for square extraction, restoration of the main congruence, and the actual specialized leading homogeneous form. It does not assert a new end-to-end proof-assistant formalization, global minimality, or historical priority. The evaluator must separately be verified to implement the stated universal norm and the pinned coefficient tuple.

## 1. Exact coordinates and definitions

The independent variables are

    j, C, z, h, r, v, w, T, c, n, t, p2, p3 in Z.

Use the coherent source-34 tuple `beta,K0,MC,MF`, with `MF` already shifted, and the source-71 determinant scales

    beta = 2^1064921 - 1,
    Acone = 2^1113,
    Bcone = 2^666104.

Define the polynomial registers

    J0 = 6j+1;               q = beta*J0+1;
    W = 4(3w+1);
    F = (K0+W)C-z(q-1);      alpha = q-F-C;
    X = qW;                 Y = (2v+1)q^3;
    E = XY;                 a = (X+1)Y;
    H = 4a+3;               Delta = a^2+4a+3;
    R = [q(q-F)-C](q^2-1)+(MC+qMF)J0;
    k = R+1+hE;
    eta = c-Yk;             zeta = k-eta;
    i = 2r+1;               I = i*c^2;
    Df = 1+Delta*I^2;       Q = Delta^2*I^2;
    delta = Q-1;            V = Df(cT-R)-c;
    Cy = QV^2-1;
    Dt = 1+k^2*X*Y^2*(XY^2+1);
    Dm = 1+Delta*c^2;       b0 = X+ac;
    U = Acone*F;            Wcone = Bcone*C;
    G = U*Wcone-(q-U-Wcone)^2;
    Peta = eta*zeta;
    Pair = G*Peta-(t^2-G-Peta+1)^2;
    Ag = Pair-1-p2^2-p3(p3+1).

The original transport row and definition of `C` hold identically:

    (K0+W)C-F-z(q-1) = 0,
    C = q-F-alpha.

Indeed this is monic elimination in the variable `F`, combined with the unimodular coordinate change from `alpha` to `C`. It does not use a divisibility assumption, an inequality, or a coprimality premise.

Let

    F32(Z;A0,A1,A2,A3,A4)
      = product over all epsilon in {+1,-1}^5 of
        (Z-sum(epsilon_i*sqrt(Ai),i=0,...,4)).

This is the universal integer polynomial obtained by expanding in formal square-root variables and replacing each squared root by the corresponding `Ai`. Invariance under each formal sign change removes all odd powers. Its degree in each radicand is at most 16. Set

    Z = Hn+b0,
    P13 = delta^16 * F32(Z;
                        Dm, H^2*Df, H^2*Dt, H^2*Ag, H^2*Cy/delta).

Multiplication by `delta^16` clears every apparent denominator. The final equation is `P13=0`; it contains neither quantified auxiliary registers nor division or square-root operations. The preceding radical display specifies an ordinary fixed polynomial.

## 2. Unconditional realness and denominator audit

These facts hold at every integer assignment, before assuming `P13=0` or any sign guard.

The integer `J0` is odd and is 1 modulo 3. Since `beta` is odd and is 1 modulo 3, `q` is even and is 2 modulo 3. The value `q` is nonzero: `beta>1` cannot divide `-1`. Its actual fixed size gives `|q|>=16`. The factors `3w+1` and `2v+1` never vanish, hence

    |X|>=64,     |Y|>=4096,
    |a|=|X+1||Y| >= (|X|-1)|Y| >18.

The integer `a` is even. Therefore `Delta=(a+2)^2-1>1` is odd and `H=4a+3` is nonzero. In particular `Dm>=1` and `Df>=1`. Also `Dt>=1`, because `XY^2` is an integer and the product of two consecutive integers is nonnegative.

There are two denominator cases:

* If `c=0`, then `Q=0`, `delta=-1`, `Cy=-1`, and `Cy/delta=1`.
* If `c!=0`, then `Q=Delta^2*i^2*c^4>1`, because `i=2r+1` is nonzero. Also `Df>|c|+1`. Put `b=cT-R`. If `b=0`, then `|V|=|c|>=1`; if `b!=0`, then `|V|>=Df-|c|>1`. Consequently

      Cy/delta = V^2+(V^2-1)/(Q-1) >=1.

Thus `delta` never vanishes, and `Dm,Df,Dt,Cy/delta` are all strictly positive on every integer assignment. This explicit treatment of `c=0` is essential: positivity of the joint guard has not yet been recovered.

## 3. Recovering positivity before square extraction

Suppose `P13=0`. Since `delta!=0`, one complex linear factor of the universal norm vanishes. The center is real, and four of its five radical terms are real by Section 2. If `Ag<0`, the remaining term is a nonzero purely imaginary number, since `H!=0`. It cannot cancel the four real terms and the real center. Therefore `Ag>=0`.

It follows that

    Pair = Ag+1+p2^2+p3(p3+1) >0.

For arbitrary integers `u,v,s`, the inequality

    uv-(s^2-u-v+1)^2 >0

forces `u>0` and `v>0`: nonpositive product is impossible, while if both are negative then `s^2-u-v+1>|u|+|v|>=2sqrt(uv)`. Applying this to `G,Peta,t` gives

    G>0,       eta*zeta>0.

This obtains the strict guards without yet asserting that `Ag` is a square. The source determinant theorem then gives the required common signs of `q,F,C,alpha`.

Write

    x=|X|, m=|Y|, K=|k|, Cabs=|c|.

Because `eta,zeta` are nonzero integers of the same sign, `K>=2` and `theta=eta/k` satisfies `0<theta<1`. From `c=k(Y+theta)` one obtains

    K(m-1)<Cabs<K(m+1).

In particular `c!=0`, `Cabs>8190`, `Q>1`, and `delta>0`.

## 4. Quantitative root separation

Take the nonnegative real roots

    d=sqrt(Dm), f=sqrt(Df), tau=sqrt(Dt),
    g=sqrt(Ag), y=sqrt(Cy/delta).

Here `g` may be zero; the other roots are positive. All estimates below precede any Pell-index decoding.

First, with `aa=|a|`,

    sqrt(Delta)>aa-3>xm/2.

The first-root and strong-root estimates are

    K(xm^2-1)<tau<K(xm^2+1),
    f>(xm/2)*Cabs^2,
    tau>2Cabs,               f>2tau,
    f>3Cabs^2.

To check the only non-immediate comparison, use `xm^2+1<2xm^2` and the strip inequality:

    f/tau > Cabs^2/(4Km)
            > K(m-1)^2/(4m)
            >= (m-1)^2/(2m) >2.

The main root obeys

    Cabs/5 < d/|H| < Cabs/2.

For the lower bound, `d>Cabs(aa-3)`, `|H|<=4aa+3`, and `aa>18` imply `(aa-3)/(4aa+3)>1/5`. For the upper bound, `d<(aa+3)Cabs`, `|H|>=4aa-3`, and `aa>5` suffice.

The determinant controls the newly added guard root. The exact identity

    12G = 4q^2-[3(U+Wcone)-4q]^2-3(U-Wcone)^2

shows `G<=q^2/3`. Since `eta*zeta<=k^2/4` and `Ag<G*eta*zeta`,

    g < |q|K/2 < Cabs/10.

The second inequality follows from `Cabs>K(m-1)`, `m>=|q|^3`, and `5|q|<m-1`. It remains valid when `g=0`.

Now distinguish the integer `b=cT-R`.

If `b=0`, then `V=-c`, and `Q>Cabs^2` implies

    Cabs<y<Cabs+1.

The increasing order

    g, d/|H|, y, tau, f

is strictly superincreasing after deleting a possible zero `g`. Indeed `d/|H|>2g`; `y>Cabs>d/|H|+g`; `y+d/|H|+g<1.6Cabs+1<2Cabs<tau`; and `f>2tau`.

If `b!=0`, then

    |V|>=f^2-Cabs>2f,        y>|V|>2f.

The increasing order

    g, d/|H|, tau, f, y

is strictly superincreasing. The previously established bounds give `d/|H|>2g`, `tau>2Cabs>d/|H|+g`, `f>2tau`, and `y>2f`.

Thus in both cases no nonempty signed subsum of the nonzero five magnitudes can vanish.

## 5. Rationality, integrality, and the main residue

Divide the vanishing norm factor by `H`. It expresses the rational number `n+b0/H` as a signed sum of

    d/|H|, f, tau, g, y.

Every term has a rational square. In the finite multiquadratic field generated by these roots, any automorphism fixes that signed sum. If it changed any nonzero term, subtracting the transformed relation would give a nonempty signed subsum equal to zero, contradicting Section 4. Thus every root is fixed by the Galois group and is rational. This argument allows dependent square classes and zero `g`; it does not assume linear independence of the five original radicals.

Rational square roots of the integer radicands `Dm,Df,Dt,Ag` are integers. For the auxiliary root, use the adjacent-coefficient Pell descent: if `Q>1` and `V` are integers and `y` is rational with

    QV^2-(Q-1)y^2=1,

then `y` is an integer. In lowest terms `y=a/e`, one has `e^2|(Q-1)`. With positive absolute values and `|V|>1`, the transformation

    V'=(2Q-1)V-2(Q-1)y,
    y'=(2Q-1)y-2QV

preserves the norm, keeps `V'` integral, preserves the reduced denominator of `y`, and satisfies `0<|V'|<|V|`. Descent reaches `|V|=1`, when `|y|=1`. This is the inherited source-69 lemma, applied only after `Q>1` has been proved.

Choose signed integer roots according to the actual vanishing factor. Absorbing the possible sign of `H`, write

    Hn+b0 = d+H(f+tau+p1+y),
    p1^2=Ag.

Then

    gamma=n-f-tau-p1-y=(d-b0)/H

is an integer. Therefore `d=X+ac+Hgamma` has exactly the required main-root residue and satisfies `d^2-Delta*c^2=1`. This is a genuine congruence recovery; it would not follow from square extraction alone without the common factors `H` on the other four terms.

## 6. Exact recovery of all inherited witnesses

The restored `p1` gives the complete old joint-guard equation. Define

    Iold = Delta*i*c^2,
    rold = (Delta*i-1)/2,
    oold = f(cT-R),
    jold = Df*T-1-R*Delta*i^2*c^3.

These are integers, since `Delta` and `i` are odd. Direct calculation gives

    Iold=(2rold+1)c^2,
    Iold^2=Delta(f^2-1)=Q,
    f*oold=V+c,
    jold*c=V+R.

The first-root equation is restored with the inherited centered root `tau-XY^2k`. Transport holds identically by Section 1. The residue-oriented native coordinates are `J3=2j` and `w3=w`, so the exact existing source applies without dropping the previously proved residue restrictions. Consequently every integer zero of `P13` yields an integer zero of the calibrated parent, and hence a finite syntactic refutation under its imported ordinary theorem.

## 7. Canonical completeness and noncircular witness choice

Start with the parent's canonical witness for a finite refutation. Its canonical repunit `J0` is odd and is 1 modulo 3, so `j=(J0-1)/6` is an integer. The existing residue-oriented `w` is retained. Monic transport recovers the same `F,alpha` from the retained `C,z`. The native outer values `h,v,c` and the fixed coefficient tuple are retained.

Regenerate the normalized strong witness as follows. Put `A=a+2`, with `A` even, `R=3 modulo 4`, `c=psi_A(R)>0`, and `D=chi_A(R)`. Take

    I=psi_A(Rc),             f=chi_A(Rc).

The composition identity `I=c*psi_D(c)` and `D^2-1=Delta*c^2` give `c^2|I`; the odd-power expansion has leading term `c*D^(c-1)` and every later term is divisible by `c^2`. The recurrence modulo 2 gives `psi_A(n)=n modulo 2`, so both `I` and `c` are odd. Thus `i=I/c^2` is a positive odd integer and `r=(i-1)/2` is integral.

The source-61 positive auxiliary reconstruction lemma (`lem:auxcomplete`) applies to these fresh `f,I`: its hypotheses are `R>=3`, `R=3 modulo 4`, `c=psi_A(R)`, `f^2-Delta I^2=1`, `f,I>0`, and `c|I`. It supplies `T` and the integer auxiliary root `y` with the exact polynomial value `V=f^2(cT-R)-c` and `Q=(Delta I)^2`. This use is stronger than merely retaining an arbitrary old auxiliary witness; no unproved divisibility of an arbitrary old quotient by `f` is assumed.

Choose a joint-guard representation `t,p1,p2,p3`. Retain `p2,p3,t`, and let the root `p1` be absorbed by the norm. All coordinates except `n` are now fixed. If the canonical main root is `D=b0+Hgamma`, choose

    n=gamma+f+tau+p1+y.

It is an integer with no imposed sign. Then `Hn+b0=D+H(f+tau+p1+y)`, so one factor of the universal norm vanishes. None of the quantities used to choose `n` depends on `n`. This proves the reverse existence implication.

## 8. Exact specialized degree 1408

The fully substituted register degrees are

    deg(H)=6, deg(Delta)=12, deg(Df)=18,
    deg(Q)=deg(delta)=30, deg(R)=5, deg(V)=23, deg(Cy)=76,
    deg(Dm)=14, deg(Dt)=34, deg(Ag)=44, deg(Z)=7.

Thus the four integer radicands have degrees `14,30,46,56`, and the numerator of the fifth has degree `deg(H^2*Cy)=88`.

The universal norm is weighted homogeneous of weight 32 when `Z` has weight 1 and each radicand has weight 2. A term using the auxiliary radicand to power `s` has, after denominator clearing, degree at most

    30(16-s)+88s+56(16-s) = 1376+2s <=1408.

The degree 56 bound also covers each pair of center factors, whose degree is 14. Only `s=16` can attain 1408. The coefficient of the sixteenth power of one radicand in the universal norm is +1, as is seen by setting the center and all other radicands to zero. Hence the top homogeneous form is exactly the sixteenth power of the degree-88 part of `H^2*Cy`.

For an actual specialized nonzero leading form, put

    q0=6 beta j, W0=12w, Y0=2v q0^3,
    a0=W0 q0 Y0, i0=2r,
    F0=W0 C-q0 z, R0=-q0^3 F0.

Then

    (H^2*Cy)_88 = 16*a0^10*i0^6*c^12*R0^2,

and therefore

    (P13)_1408 = (16*a0^10*i0^6*c^12*R0^2)^16.

This is nonzero for the actual fixed `beta>0`, because all the displayed leading factors are nonzero polynomials in the thirteen independent variables. The argument proves exact specialized degree 1408 and nonzeroness, not merely a gate-degree upper bound or a generic-parameter statement.

## 9. Remaining verification boundary

The new mathematical reduction is complete relative to the stated inherited source theorem. A delivery audit must still bind the universal norm implementation, all six coefficient recipes and hashes, the literal DAG and operation count, and the pinned inherited proof files. Modular evaluations provide useful implementation checks but are not a substitute for the symbolic norm identity or the native/refutation calibration. The claim is an improved explicit member of the audited family; it is not a proof that no simpler Diophantine equation exists.

## 10. Audited centered thirteen-variable endpoint: degree 1392

The final centered variant replaces `Z=Hn+b0` by

    Z=H(n+V)+b0.

Since `V` is an integer polynomial in the other twelve coordinates, the map `n_old=n_new+V` is an integer bijection on each fiber. Its inverse is `n_new=n_old-V`. Therefore every existence equivalence above applies without modification. In particular, completeness uses `n=gamma+f+tau+p1+y-V`. This argument is specific to the unrestricted integer domain and asserts nothing about preserving positivity.

An invertible polynomial translation does not in general preserve total degree. The claimed degree 1392 has been checked separately as follows. Work in the free algebra over the integer polynomial ring with `u^2=d=Dm`, `v^2=e=H^2Ag`, and basis `1,u,v,uv`. Let

    A=H^2Df, B=H^2Dt, Cnum=H^2Cy,
    Xformal=Z+u+v,
    J=delta*(Xformal^2-A-B)-Cnum,
    K=J^2-4*(delta^2*A*B+delta*Cnum*(A+B)),
    L=K^2-64*delta^3*A*B*Cnum*Xformal^2.

The two successive quadratic norms of `L` are exactly the cleared five-root norm. Assign weights 7 and 28 to the basis symbols `u,v`, respectively. This agrees with the degrees 14 and 56 of their squares and gives a multiplicative filtration.

Writing `s=Hn+b0`, the scalar part of `J` has the exact canceled form

    J0=delta*(s^2+2HVs+d+e-A-B)-H^2*(V^2-1).

Its leading term is `Q0*e0`, of degree 86. The weighted degrees of the coefficients on `1,u,v,uv` are respectively `86,66,87,65`. The unique weight-87 term is `2Q0*Z0*v`. Therefore `K` has unique leading scalar `(2Q0Z0)^2e0`, of degree 174: its scalar subtrahend has degree at most 164. The subtrahend in `L` has weighted degree at most 312. Hence `L` has unique leading scalar `16Q0^4Z0^4e0^2`, of degree 348. Its four conjugates have the same leading scalar, and their product has exact degree `4*348=1392`.

With the Section 8 leading forms, put

    eta0=-h*X0*Y0^2,
    Q0=a0^4*i0^2*c^4,
    V0=-a0^2*i0^2*c^4*R0,
    Z0=4a0*V0,
    e0=-16a0^2*eta0^4.

The actual specialized highest form is

    (P13_centered)_1392
      =2^80*a0^128*i0^64*c^128*R0^16*eta0^32.

It is nonzero. In particular the coefficient of

    j^800*w^160*v^192*h^32*r^64*c^128*z^16

is exactly `2^1456*3^960*beta^800>0`. The `z^16` term in `R0^16` is uniquely selected, so this coefficient is not inferred merely from uncanceled gate degrees.

## 11. Audited centered fourteen-variable companion: degree 696

The companion adds the integer coordinate `p1` and retains the full joint-guard residual

    Jguard=Pair-1-p1^2-p2^2-p3(p3+1),
    S=Jguard^2.

Put `Fstrong=(a+2)I`, `ell=XY^2k`, and

    Z=H(n+2V+2ell+k+2Fstrong)+2b0,
    N4=delta^8*F16(Z;4Dm,4H^2Df,4H^2Dt,4H^2Cy/delta),
    P14=S+N4+S*N4.

For integer inputs, `P14=0` implies `(1+S)(1+N4)=1`. Since `S>=0`, both integer factors must equal 1, so `S=N4=0`. The guard therefore supplies the four-root separation established above after omitting `g`. A vanishing factor yields signed integer roots with

    Z=2d+2H(f+tau+y).

Consequently `H` divides `2(d-b0)`. The integer `H=4a+3` is odd, so it divides `d-b0` and restores `gamma`. Conversely, from canonical parent roots choose

    n=2gamma+2f+2tau+2y-2V-2ell-k-2Fstrong.

This proves the two-way existence equivalence. Unlike the simple thirteen-variable shear, the half-centered fourteen-variable presentation is justified by these explicit implications, not by claiming an integer bijection of all old carrier coordinates.

The exact degree is independently checked by substituting every independent variable `x` by `t*x` and working in the Laurent-series field at `t=infinity`. Set

    Uf=2H*Fstrong, Ut=H(2ell+k), Uy=2HV,
    Scenter=Hn+2b0.

The scaled radicands equal

    4H^2Df=Uf^2+4H^2(1-I^2),
    4H^2Dt=Ut^2+H^2(4-k^2),
    4H^2Dy=Uy^2+4H^2(V^2-1)/delta.

The centers have degrees `15,23,29`; their corrections have degrees `18,26,28`. The corresponding formal square-root deviations from the centers have degrees at most `3,3,-1`. Binomial expansion in the Laurent field is legitimate because each correction has lower degree than its center squared.

Of the sixteen conjugate factors, eight first fail to cancel `Uy`, four further factors first fail to cancel `Ut`, and two further factors first fail to cancel `Uf`. Their leading degrees are respectively `29,23,15`. The final main-root pair has leading degree 14 and leading form

    (H0*n+2a0*c)^2-4a0^2*c^2=H0^2*n(n+c),
    H0=4a0.

All root corrections are lower degree than that pair. Clearing `delta^8` adds 240. Thus

    deg(N4)=8*29+4*23+2*15+14+240=608.

Its nonzero leading form is

    (N4)_608=2^60*a0^66*i0^34*c^68*R0^8*ell0^4*n(n+c),
    ell0=h*X0^2*Y0^3.

Since `S` has degree 88 and leading form `eta0^8`, the unique highest summand of `P14` is `S*N4`, of degree 696. The coefficient of

    j^396*w^82*v^94*h^12*r^34*c^68*z^8*n^2

is `2^748*3^478*beta^396>0`. This proves exact degree 696 for the actual fixed coefficient tuple.

## 12. Audited thirteen-variable CRT companion: degree 1088

The following additional construction changes the polynomial coordinates and guard while keeping the same thirteen unrestricted integer variables and six fixed coefficient ports. In the Section 1 definitions replace

    Y=(2v+1)q^3

by

    Y=qv.

Every downstream register uses this new `Y`. Retain the definition of `Pair`, and replace the guard radicand by

    Ag=v^2*Pair-1-p2^2-p3(p3+1).

Define two moduli and their polynomial scale

    M=2q^2, L=4H+1, U=M*H,
    Z=U(n+V)+M*L*b0+H(v-q^2).

The single polynomial is

    P13_CRT=delta^16*F32(Z;
                M^2*L^2*Dm, U^2*Df, U^2*Dt, U^2*Ag, U^2*Cy/delta).

### 12.1 Unconditional realness, including the new zero-scale boundary

The bounds `|q|>=16` and `|X|>=64` are unchanged. If `v=0`, then `Y=a=0`, `H=3`, and `Delta=3`. If `v!=0`, then `|Y|>=16` and `|a|>18`, so again `Delta>1`. Thus `Delta` is positive and odd at every assignment, and `H,M,L,U` are all nonzero. The previous unconditional proof of `delta!=0` and `Dy=Cy/delta>=1` uses only `Delta>1`, odd nonzero `i`, and the two cases `c=0` or `c!=0`; it applies unchanged. Likewise `Dm,Df,Dt` are all positive.

At a norm zero the guard radical is consequently the only one that could be imaginary. Therefore `Ag>=0`. Its definition gives

    v^2*Pair=Ag+1+p2^2+p3(p3+1)>0.

This proves `v!=0` and `Pair>0` in that order, without assuming the missing cubic-scale congruence. It then proves `G>0`, `eta*zeta>0`. In particular, putting `mY=|Y|`, `K=|k|`, and `Cabs=|c|`,

    mY>=16, K>=2,
    K(mY-1)<Cabs<K(mY+1),
    Cabs>30.

The proof has not yet recovered `v=q^2*(odd)` and does not use that stronger property prematurely.

### 12.2 Separation with the altered main-root scale

Use positive roots `d,f,tau,y` and the nonnegative root `g=sqrt(Ag)`. As before,

    tau>2Cabs, f>3Cabs^2,
    b=0 implies Cabs<y<Cabs+1,
    b!=0 implies y>2f,

where `b=cT-R`. These estimates only require `mY>=16`, `x=|X|>=64`, and the strip bounds.

The guard bound is now

    g<|v|*|q|*K/2=K*mY/2<(8/15)*Cabs.

Indeed `Ag<v^2*G*eta*zeta`, `G<=q^2/3<q^2`, and `eta*zeta<=K^2/4`; then `mY/[2(mY-1)]<=8/15`.

The main root is comparable to the first root. Specifically,

    d>K*((x-1)mY-3)*(mY-1),
    tau<K*(x*mY^2+1).

The inequality `d>3tau/4` follows from

    4[((x-1)mY-3)(mY-1)]-3(x*mY^2+1)
      =mY^2(x-4)-4mY(x+2)+9>0,

valid for `x>=64,mY>=16`. Since `lambda=L/H=4+1/H` lies strictly between 3 and 5,

    lambda*d>2tau.

Also `d<2Cabs*sqrt(Delta)` and `f>Cabs^2*sqrt(Delta)`, so

    f>Cabs*d/2>15d>2lambda*d.

If `b=0`, the increasing order

    g, y, tau, lambda*d, f

is strictly superincreasing: `y>g`; `y+g<(23/15)Cabs+1<2Cabs<tau`; and the last two entries are each more than twice their predecessors. If `b!=0`, the increasing order

    g, tau, lambda*d, f, y

is strictly superincreasing by the same bounds and `y>2f`. A zero `g` is omitted. Thus dividing the vanishing norm factor by `U` again gives rationality of every radical. Since `lambda` is a nonzero rational number, rationality of `lambda*d` implies rationality of `d`. Integer-square-root integrality and adjacent Pell descent give integer signed roots `d,f,tau,p1,y`.

### 12.3 Recovering both congruences without a coprimality assumption

The algebraic definitions give

    H=3 modulo q,
    q=2 modulo 3,
    H odd.

Hence `gcd(H,q)=1` and `gcd(H,M)=1`, because `M=2q^2`. This is a proved identity-level property of the new coordinates, not an assumption about canonical witnesses. Also `L=1 modulo H`.

Write the actual signed root relation as

    U(n+V)+M*L*b0+H(v-q^2)
       =M*L*d+U(f+tau+p1+y).

Modulo `M` it gives `H(v-q^2)=0`; coprimality yields

    v=q^2*(2v_old+1)

for an integer `v_old`. Therefore `Y=(2v_old+1)q^3`, exactly the old cubic odd-scale condition. Modulo `H`, the same root relation gives `M*L(d-b0)=0`. Since both `M` and `L` are units modulo `H`,

    gamma=(d-b0)/H

is an integer. This restores the old main-root congruence as well. All other strong, auxiliary, index, and transport restorations are unchanged.

The recovered `Pair>0` gives the original strict guards. The new `p1` represents the scaled positive number `v^2*Pair`, so it is not claimed to be the old private guard coordinate. To obtain an actual old joint-guard tuple, use the positivity surjection to represent the positive integer `Pair` by `1+p1_old^2+p2_old^2+p3_old(p3_old+1)`. These three coordinates are private to the inherited guard and can be regenerated. This distinction is necessary for exact source restoration.

### 12.4 Canonical completeness and the carrier integer

Begin with a canonical parent witness and its normalized strong/auxiliary regeneration. Set

    v=Y_old/q=q^2*(2v_old+1).

Retain `t` with `Pair>0`, and choose fresh `p1,p2,p3` representing the positive integer `v^2*Pair` by the three-square positivity expression. Then `Ag=p1^2`. All coordinates other than `n` are fixed. Set

    n=L*gamma+f+tau+p1+y-V-(v-q^2)/M.

The final quotient is an integer by the displayed value of `v`. Substitution gives the required signed root relation exactly, hence a polynomial zero. No witness depends on `n` before this final choice.

### 12.5 Exact degree 1088 and a specialized coefficient

The new degrees are

    deg(a)=deg(H)=4, deg(Delta)=8,
    deg(Df)=14, deg(Q)=deg(delta)=22,
    deg(V)=19, deg(Dt)=22, deg(Ag)=30,
    deg(M)=2, deg(U)=6, deg(Z)=25.

The scaled main and guard radicands have degrees 22 and 42, the scaled strong and first radicands have degrees 26 and 34, and the scaled auxiliary numerator has degree 72. In the same biquadratic evaluator used in Section 10, assign root weights 11 and 21 to the scaled main and guard radicals. The four weighted components of the canceled `J` have degrees

    64, 58, 68, 54.

The unique highest component is the guard component. Squaring gives a unique scalar of degree 136; the scalar correction has degree at most 128. The next square gives a unique scalar of degree 272; its correction has degree at most 248. Two quadratic norms therefore give exact degree `4*272=1088`.

For the actual leading form, now use

    q0=6beta*j, W0=12w, Y0=q0*v,
    X0=q0*W0, a0=X0*Y0,
    i0=2r,
    F0=W0*C-q0*z, R0=-q0^3*F0,
    k0=R0+h*a0, eta0=-Y0*k0,
    U0=8q0^2*a0.

The top homogeneous polynomial is

    (P13_CRT)_1088
      =2^112*q0^64*a0^128*i0^64*c^128*R0^16*v^16*eta0^32.

It is nonzero. The coefficient of

    j^480*w^160*v^208*h^32*r^64*c^128*z^16

is exactly `2^976*3^640*beta^480>0`. Here both summands of `k` have degree five, so the full `k0=R0+h*a0` must be retained in the highest form. The selected `h^32` coefficient uniquely chooses the `-h*X0*Y0^2` term from each of the thirty-two factors of `eta0`; the selected `z^16` then uniquely chooses `q0^4*z` from every factor of `R0^16`. All remaining factors are monomials. The exponent sum is 1088.
