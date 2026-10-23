# Independent review of the ratio-separated twelve-positive construction

Reviewed proof: `research/roots/RATIO12_PROOF.md`, 22 October 2026.
Repository snapshot: `a477d0fc8b6feda53796835564a988015e744d4d`.

## Verdict and boundary of review

The proposed ratio separation is sound in the stated **positive** domain,
relative to the inherited inputless K215/Pell interface. The new polynomial
has12 positive unknowns,116 binary operations and exact degree1081. The
shifted three-equation version has110 operations and maximum degree1072.
This review checked the new inequalities, root recovery, signs, transport
shift, and leading degrees independently of the generator. A separate
structural program imported no candidate generator and verified the frozen
circuit ledgers, dependency validity, and liveness.

The argument must not be cited over the enlarged signed-s domain used for
the separate24-integer result. In particular G>A and the inner-weight proof
use positivity in essential places. The two constructions legitimately have
different weights and degrees.

## 1. Inner weight: the constants have enough margin

Write a0=a+2. The weak exterior bounds already give X>=16, Y>=4096,
k>E=XY and 0<R<k. Hence a0=E+Y+2<2E and c<2kY. It follows that

    ell=kEY>a0*c/4,
    ell>E^2 Y>8a0^2.

The second inequality follows, for example, from a0<2E and Y>32.
Since A=1+ell(ell+k)>ell^2,

    A>a0^2*c^2/16,       A>64a0^4.

With I=ic^2, D=1+(a0^2-1)I^2<a0^2 I^2; also c<I^2. Consequently

    b=c+RD<2k a0^2 I^2.

For M=kI^2+T^2, M^2>=4kI^2T^2, so

    AM^2>(k/4)Dv^2>8Dv^2,
    AM^2>=Ak^2 I^4>16b^2>8b^2.

The first strict comparison uses k>E>=16*4096>32. Averaging the two
weaker last bounds gives AM^2>4(Dv^2+b^2). As d=Q-1>=Q/2,

    dAM^2>2Q(Dv^2+b^2)=2(e+1).

Thus removing the extra factor2 from the older inner weight is justified;
it is not a numerical extrapolation from a small fixture.

For any coherent f'=+-sqrt(D), an auxiliary root satisfies
d(y')^2=e-Baux*f'. The absolute-value bound, also valid for complex y', is

    d|y'|^2<=e+Baux sqrt(D)
             <Q(v sqrt(D)+b)^2
             <=2Q(Dv^2+b^2)<dAM^2.

Hence |y'|<M sqrt(A).

## 2. Ratio separation really removes the large extra factor

Using c>kY and Delta>(E+Y)^2, direct expansion gives

    G-A > k^2[(E+Y)^2Y^2-EY(EY+1)]
          =k^2[EY(2Y^2-1)+Y^4]>0.

Every root x of the inner polynomial F is Mt+y' for a choice of t^2=A and
the corresponding auxiliary root. Therefore

    |x|<2M sqrt(A)<2M sqrt(G).

The polynomial F has rational coefficients after the input integers are
fixed. If G were nonsquare, x=(W-Lsqrt(G))/H and its quadratic conjugate
x'=(W+Lsqrt(G))/H would both be roots. Their separation is

    |x'-x|=2L sqrt(G)/H>4M sqrt(G),

contradicting their strict root-radius bounds. This only uses ordinary
quadratic conjugation; no unsupported independence of several radical
extensions is required.

Thus the selected main root u is integral. Because W>0 and all weights
are positive, u<0 would give

    W=Lu+Hx<-L sqrt(G)+2HM sqrt(G)=-sqrt(G)<0.

Hence u>0, and x=(W-Lu)/H is rational.

## 3. Rational inverse formulas have nonzero denominators

For a coherent pair f,t define

    C=d(x^2+M^2A)-e,
    V=C^2+D Baux^2-4d^2x^2M^2A.

The coherent factor identity is

    C+Baux*f=2dxMt.

The weight bound proves C>e+2>0. Also Baux=2Qvb>0 in this positive
domain. If x=0, then

    F(0)=[(dM^2A-e)^2-D Baux^2]^2>0,

because dM^2A-e>e+2 and Baux sqrt(D)<=e+1. Thus x!=0. Squaring the
coherent identity and using f^2=D, t^2=A gives

    V+2C Baux*f=0.

Therefore the displayed formulas

    f=-V/(2C Baux),       t=(C+Baux*f)/(2dxM)

are valid rational expressions with established nonzero denominators.
The integer squares f^2=D and t^2=A imply f,t are integers. With
y=x-Mt and vf-b integral, rational Pell saturation proves y integral.
This is a sound use of the specialized saturation lemma; a generic
rational-square argument would not suffice for y.

## 4. Main-root congruence and signed quotient

Now x=Mt+y is integral and L=1 modulo H, so W=Lu+Hx gives
u=X+ac modulo H. Thus gamma=(u-X-ac)/H is integral. In fact gamma is
positive: the already available bounds give k>E=XY>X and c>k, while
u^2=1+Delta*c^2 and Delta>(a+1)^2 imply u>(a+1)c. Hence

    gamma*H=u-ac-X>c-X>0.

This short argument avoids invoking the first-Pell classification a
second time merely to obtain c>X.

The restored equations are exactly the normalized first, main, strong,
and auxiliary core equations. A negative f may be replaced by -f together
with -T without changing them. The cited signed-quotient interface allows
that sign, so no unsupported positivity restoration of T is needed.
The inherited index/unit recovery and machine compiler then apply.

For completeness, the canonical positive roots give the positive integer
r=gamma+2Mu+Mt+y. It satisfies W=Lu+H(Mt+y), so one factor vanishes.
All exterior equations retain their canonical value1.

## 5. Transport shift and direct norm comparison

The norm itself and R do not involve z. The coordinate change
z_new=z_old-1 changes Nt=1 exactly into

    (K0+w)Cw=F+z_new(q-1).

Every positive new solution maps to an old one by z_old=z_new+1. In the
other direction, decoder soundness gives Cw>0, X=wq=2^R, and R>3q, so
w>q>F. It follows that

    (K0+w)Cw-F=(z_old-1)(q-1)>0,

and z_old>=2. This proves the positive zero-set bijection without using
the decoded fact w=2^R/q prematurely in the original weak bootstrap.

The shifted comparison saves one addition. Independently, comparing the
two final norm terms rather than subtracting and comparing to zero saves
one operation in the system convention. Both savings are real in the
repository's stated metric, which does not charge equality tests. They do
not reduce the unchanged product polynomial's116 operations.

## 6. Exact degrees and arithmetic check

The proof's degree chain checks out. In the positive input grading,
deg(M)=23, deg(HM)=deg(L)=29, deg(W)=11 and deg(n)=80. The decisive
coefficient C0 has unique leading term -H^2e of degree134; the competing
term d(Z0+n) has degree at most126. Consequently the final even
coefficient N0 has unique highest term H^8e^4 of degree536. The odd
coefficient has degree at most488. Thus the outer norm has exact
degree1072, while the other subtracted term has degree at most998.

Its highest form is

    2^32 i^48 k0^96 w^80 s^176 q0^656(q0-F)^16.

Multiplication by the exterior factors adds degrees7 and2, giving1081.
The coefficient of J^677*h*z*i^48*eta^96*w^81*s^177 is
2^32*beta^677, which is nonzero for every authentic beta>0.

The independently run `audit_new_circuits.py` confirms:

| Circuit | Unknowns | Operations | Multiplies | Add/subtract | Degree upper bound |
|---|---:|---:|---:|---:|---:|
| ratio12 product | 12 | 116 | 74 | 42 | 1081 |
| ratio12 system | 12 | 111 | 72 | 39 | 1072 |
| ratio12 shifted system | 12 | 110 | 72 | 38 | 1072 |

Every gate and every supplied input is live. The unbounded exact-degree
argument above supplies the lower bound; the structural program alone
would only provide upper bounds. The finite circuit checks do not prove
the inherited compiler or decide whether any of these equations has a zero.
