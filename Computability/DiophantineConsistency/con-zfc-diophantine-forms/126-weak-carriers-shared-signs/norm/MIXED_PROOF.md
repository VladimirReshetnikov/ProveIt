# Mixed CRT, selective coprime fusion, and weak projection in eleven integers

This is the independent ordinary mathematical proof of the delivered mixed
CRT eleven-integer construction. It does not claim a new proof-assistant
endpoint or reprove the retained native/refutation calibration.

## 1. Complete definitions

Independent integer coordinates are `j,C,z,h,r,v,w,T,c,n,s`. Use the SAME
six fully fixed source34 coefficients `beta,K0,MC,MF,cone_A,cone_B` as in
the incoming Coprime_Projection integer package. In particular
`beta=2^1064921-1`, `cone_A=2^1113`, `cone_B=2^666104`, and `MF` is already
shifted. Define polynomial abbreviations

    J=6j+1, q=beta*J+1, W=12w+4,
    X=qW, Y=qv, E=XY, a=E+Y,
    H=4a+3, Delta=a^2+H=(a+2)^2-1,
    F=(K0+W)C-z(q-1),
    R=(q(q-F)-C)(q^2-1)+(MC+q*MF)J,
    k=R+1+hE, eta=c-Yk,
    Derr=(cone_A*F-q)^2+(cone_B*C-q)^2,
    Budget=k^2(q^2-Derr)-4q^2 eta^2, D=3Budget-4,
    L=XY^2*k, Dt=1+L(L+k),
    Dg=1+D*Dt*s^2, P=Dt*Dg,
    I=r c^2, Df=1+Delta I^2,
    Q=Delta^2 I^2, delta=Q-1,
    V=Df(c-R+4IT)-c,
    Cy=QV^2-1, Da=delta*Cy,
    K=X(3c-2X)+2,
    M=2q^2, Dc=M H,
    zc=Dc*T+M*K+H(v-q^2),
    Ac=(zc^2+3Dc^2)(zc^3-19Dc^3),
    S=s r M^5 H,
    Z=S(n+3QV)-Ac,
    u=S^2 Df, b=9S^2 Da, e=81S^2 P.

Set

    F8=[(Z^2-u-b-e)^2-4(ub+ue+be)]^2-64ube Z^2.

The single final equation is `F8=0` over eleven unrestricted integers.
It is the ordinary polynomial obtained by the product of eight linear
factors `Z +/- sqrt(u) +/- sqrt(b) +/- sqrt(e)`. No radical occurs in
the actual polynomial specification.

The omitted factor4 in `Dg` is justified: `q` is even, as are `cone_A`
and `cone_B`; hence `Derr`, `q^2`, and `Budget` are divisible by4.
Therefore `D=3Budget-4` is divisible by4 and `Dg=1 (mod4)` already.
Completeness uses a positive ordinary Pell solution directly, so it does
not require squaring that solution to force an extra even ordinate.

## 2. Bootstrap before imposing the scale congruence

The authentic fixed coefficients imply `q` even, `q=2 (mod3)`,
`|q|>=beta-1>=16`, and `|X|>=4|q|`. Also `a=qv(X+1)` is a multiple
of q. If `v=0`, then `a=0` and `Delta=3`. If `v!=0`, then
`|a|>=|q|(|X|-1)>3`. Thus `Delta>1` on EVERY integer assignment.
The odd integer `H=4a+3` is always nonzero. `M=2q^2>0` and

    H=3 (mod q), gcd(H,q)=1, gcd(H,M)=1.

Here `gcd(q,3)=1` uses `q=2 (mod3)`; the factor2 is harmless since H
is odd. In particular `Dc!=0`. Furthermore `Df>=1` and `Dt>=1`,
because `Dt=1+ell(ell+1)k^2` with integer `ell=XY^2`.

The polynomial `pi(x)=(x^2+3)(x^3-19)` has no rational zero. Therefore
`Ac=Dc^5*pi(zc/Dc)` is nonzero for every integer assignment. At `S=0`,
all scaled radicands vanish and `F8=Ac^8!=0`. Every zero thus has
`s,r!=0`.

At this stage neither `v` nor `c` is known nonzero. Nevertheless `Da>0`.
If `c=0`, then `I=Q=0`, `delta=Cy=-1`, and `Da=1`. If `c!=0`, then
`I!=0`, `|I|>=c^2`, and `Df>|c|+1`. Writing `V=Df*b0-c` with
integer `b0=c-R+4IT`, either `b0=0` and `|V|=|c|>=1`, or
`|V|>=Df-|c|>1`. Thus `Q>1`, `Cy>0` and `Da>0` in this case too.

In a vanishing conjugate factor, if `Dg<0`, the term `sqrt(P)` is
the sole nonzero imaginary term. This is impossible. Since `Dg` is
odd, it is strictly positive. If `Budget<=1`, divisibility of Budget
by4 actually gives `Budget<=0`, whence `D<=-4` and
`Dg=1+D Dt s^2<=-3`. Thus `Budget>=4`, in particular `Budget>=2`.

## 3. Extract roots and recover CRT BEFORE auxiliary descent

The three integer radicands `Df,Da,P` are positive. Unconditionally,
`q=2`, `W=1`, and `X=2 (mod3)`, so `a,H,Delta=0 (mod3)`.
It follows that `Df=Da=1 (mod3)` even when I is zero; these two
radicands are units at3. A vanishing factor divided by S is a rational
signed sum of

    sqrt(Df), 3sqrt(Da), 9sqrt(P).

Decompose the positive integer radicands into squarefree parts. Within
any nontrivial squareclass not divisible by3, the first two root
coefficients have respective 3-adic orders0 and1 whenever present,
whereas the last has order at least2. A unique least order cannot cancel.
If the squareclass is divisible by3, only the last radicand can belong
because Df and Da are 3-adic units. That singleton cannot cancel either.
Linear independence of squarefree radicals therefore forces all three
roots to be rational, hence integral. No assumption that P is a unit at3,
no factor2 in I, and no hidden oddness hypothesis is used. Since `gcd(Dt,Dg)=1`, the product square
splits into integral `tau^2=Dt` and `g^2=Dg`. Write `f^2=Df` and
`ytilde^2=Da`. The factor identity gives `S|Ac` immediately; auxiliary
descent is not yet needed or invoked.

As `M^5|S`, we have `M^5|Ac`. For each prime p with `p^m||M`, the
carrier scale Dc has p-valuation at least m. If `v_p(zc)=b<m`, the
leading term `zc^5` in

    Ac=zc^5+3Dc^2 zc^3-19Dc^3 zc^2-57Dc^5

has valuation5b, strictly smaller than every other term, contradicting
`p^(5m)|Ac`. Therefore `M|zc`. Since `zc=H(v-q^2) (mod M)` and
`gcd(M,H)=1`,

    v=q^2(2v_old+1), v_old=(v-q^2)/(2q^2) in Z.

Thus `Y=(2v_old+1)q^3`, restoring exactly the original cubic scale.
In particular `Y!=0`. If `c=0`, then

    Budget=k^2[q^2(1-4Y^2)-Derr]<=0,

contradiction. Therefore `c,I!=0` and `Q>1`. Now
`y=ytilde/delta` is rational and satisfies
`QV^2-(Q-1)y^2=1`; the parent's adjacent-coefficient denominator
descent makes y integral. All of its hypotheses have been established
before it is used.

Finally, `H|Ac`, `zc=M K (mod H)`, and `Dc=0 (mod H)` imply
`H|M^5 K^5`. Coprimality gives `H|K^5`.

## 4. Weak projection and the unchanged source semantics

Put `Kquad=X(X+2ac)-1`. The exact identity

    K=HXc-2Kquad

and oddness of H give `H|Kquad^5`. Use absolute main-root folding,
then only the pre-projection rank proof of the copied centered source.
Its inputs are the now-restored cubic scale, `Budget>0`, the first,
strong and auxiliary norms, `c^2|I`, and the two exact residues

    V=-c (mod f), V=-R (mod c).

The second follows from
`V+R=Delta I^2(c-R)+4I Df T`; the first is immediate from Df=f^2.
No parity assumption on `I/c^2` is used. The centered guard yields
the common nonzero sign of q,F,C,q-F-C and `|c/k-Y|<1/2`.
The cited pre-projection proof supplies

    c=sign(c)*psi_(a+2)(R), R=2t+1, t>=24,
    |Y|>(|X|-3)^t/2-1.

Set `x=|X|`, `sigma=sign(c)`, and
`Pi=(sigma X-2^R)(2^R sigma X+1)`. The signed Pell congruence is
`2^R Kquad=Pi (mod H)`, so `H|Pi^5`. The ratio bound implies
`|H|>x(x-3)^t`. The authentic beta implies `x>=2^64`, and therefore

    |Pi|^5<2^(20t+20)x^10 < x^(t+1)/2^t < |H|.

Indeed `64(t-9)>(21t+20)` holds for all `t>=24`, with margin at
least436. Thus Pi=0. Its second factor is odd and nonzero, so
`sigma X=2^R`. The parent's centered orientation and uniform half-binomial
proof restore `X,c,k,Y>0` and `0<eta/k<1/4`. Its fresh odd-witness
construction then restores an actual old signed native source zero.
Compose the retained ordinary native/compiler/refutation calibration.

## 5. Completeness with a fixed strong pair

Start from the parent's canonical outer witness. Replace its cubic-scale
coordinate by `v=q^2(2v_old+1)`; all other outer arithmetic is unchanged.
The canonical bound gives Budget>=64, so `D=3Budget-4>0`. Also
`Dt=1 (mod3)` on the restored scale, and `D=2 (mod3)`, so `D Dt`
is positive and nonsquare. Choose a positive Pell solution

    g^2-(D Dt)s^2=1.

This is exactly the new guard `Dg=g^2`; no parity modification is needed.
Now choose a single strong pair `I,f` with `4s c^2|I` and put
`r=I/c^2`. Thus `I=rc^2`. Every prime factor of `m=sr` divides I.
The supported-modulus interpolation theorem in the incoming Round14
proof attains every auxiliary T residue modulo m while keeping this
same strong pair fixed.

The canonical main projection gives `H|K`. Define the integer

    kappa=K/H+(v-q^2)/M.

Then `zc=Dc(T+kappa)` and

    Ac/S=H^4*pi(T+kappa)/(sr).

Choose an intersective residue `a0` modulo m for `pi(x+kappa)`, then
interpolate `T=a0 (mod m)` with the already-fixed `I,f`, supplying
the corresponding integral auxiliary ordinate y. The quotient Ac/S
is integral. With `tau^2=Dt`, choose

    n=Ac/S+f+3delta*y+9tau*g-3QV.

One conjugate factor vanishes. The order is canonical outer witness,
guard s/g, one strong pair I/f/r, intersective residue, interpolated T/y,
then n. No strong-pair choice is changed after requesting a residue.

## 6. Exact total degree416

The relevant exact register degrees are

    q1, X2, Y2, a4, H4, Delta8, R5, k5, eta7,
    Budget16, Dt22, Dg40, P62,
    I3, Df14, Q22, V19, Cy60, Da82,
    M2, Dc6, zc7, Ac35, S16,
    u46, b114, e94.

Let `C0=3SQV` (degree57), `z0=Sn-Ac` (degree35), and
`omega=Z^2-b`. The exact identity

    b-C0^2=9S^2[-Q(V^2+1)+1]

gives

    omega=z0^2+2C0*z0+9S^2[Q(V^2+1)-1], deg(omega)<=92.

Rewrite the identical final norm as

    [(omega-u-e)^2-4(ue+b(u+e))]^2-64ube Z^2.

The inner bracket has unique top summand `-4b_top e_top` of degree208:
the square has degree at most188; ue has degree140; bu degree160.
The final correction has degree368. Thus the whole degree416 form is
exactly `16b_top^2 e_top^2`, provided its actual coefficient specialization
is nonzero, as proved next.

For highest homogeneous parts write

    q0=6 beta j, W0=12w, X0=q0W0, Y0=q0v,
    a0=X0Y0, F0=W0 C-q0 z,
    R0=-q0^3 F0, k0=R0+h X0Y0,
    I0=rc^2, S0=2^7 s r q0^10 a0.

The strong and fused radicand leading forms are

    Da0=a0^12 I0^8 R0^2,
    P0=-12q0^2 X0^4 Y0^10 k0^6 s^2.

Consequently the entire highest form is

    (F8)_416 = 2^64*3^14 s^12 r^24 c^32 q0^84
                   X0^40 Y0^52 R0^4 k0^12.

Taking the unique highest power h^12, then the z^4 term from R0^4,
gives the actual nonzero coefficient

    [j^216 w^52 v^64 h^12 z^4 s^12 r^24 c^32] F8
       = 2^384 * 3^282 * beta^216 > 0.

The exponents sum to416. This proves exact degree after substituting
the full authentic coefficient tuple, not merely a syntactic degree
bound or a numerical line test.

For the cubic-scale sibling with `Y=(2v+1)q^3`, `S=srH`, the same omitted
guard4 gives exact degree464. Its entire highest form is

    2^24*3^14 s^12 r^24 c^32 q0^4 h^12 X0^52 Y0^64 R0^4,

where now `Y0=2v q0^3`. A nonzero actual coefficient is

    [j^264 w^52 v^64 h^12 z^4 s^12 r^24 c^32] F8
       = 2^456 * 3^330 * beta^264 > 0.

## 7. Sources and proof boundary

The immediate fused source is the incoming Coprime_Projection `integer/`.
Its copied centered proof and signed-quadratic proof supply the unbounded
source semantics and full-residue groundwork. Carriers_and_Even_Indices
`crt12/PROOF.md` supplies the mixed-modulus carrier precedent. Powered_Round14
`radicals/PROOF.md` supplies the weak fifth-power projection and the
supported-modulus interpolation theorem. The exact coefficient tuple and
ordinary native/refutation calibration remain inherited mathematical
dependencies. The new construction is their proved composition with early
CRT, prime3 root separation, a shorter polynomial center, and a redundant
guard factor removed. Finite algebraic checking
does not establish or replace those unbounded calibrations.

## 8. Exact finite audit, as executed

`audit_independent.py` imports neither the producer nor its DAG helper and
uses only the Python standard library. It has been run successfully in
normal and optimized Python. It authenticates all six full coefficient
payloads against fixed source hashes; proves every named register by local
free-ring identities; expands all eight conjugate factors and verifies the
complete35-coefficient norm identity; proves the universal center defect;
checks the entire highest homogeneous forms and actual attained coefficient;
recounts topology, live arithmetic operations and coordinate closure; and
rejects six targeted circuit changes in each of the four variants. Modular
replays and small parity/CRT controls are supplementary only. The receipt
records the finite scope; the unbounded arithmetic proof and inherited
calibration remain the ordinary mathematical arguments cited above.
