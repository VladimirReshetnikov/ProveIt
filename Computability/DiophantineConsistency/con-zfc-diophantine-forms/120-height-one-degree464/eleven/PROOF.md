# Eleven unrestricted integers, degree 464, and 122 arithmetic operations

## 0. Result, comparison, and proof boundary

This contribution combines the selective coprime fusion of the incoming
`ZFC_Diophantine_Coprime_Projection_2026-10-24.zip` with the fifth-power
saturation and supported-modulus interpolation of
`ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24.zip`.
The source snapshot is ProveIt commit
`45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6`.

The selected polynomial has eleven unrestricted integer variables, exact
degree **464**, and **122** live binary additions, subtractions, and
multiplications. A companion has exact degree **488** and **121** operations.
The incoming eleven-integer selective-fusion forms had degree 688 with 126
operations, and degree 728 with 122 operations. Thus the selected equation
lowers both degree and cost relative to the former, and lowers degree at
the same cost relative to the latter. These are comparisons on the same
whole fixed coefficient tuple and the same integer domain, not claims of
a global optimum.

There are four changes:

1. Replace the large carrier scale `I H^5` by `s r H`, retaining only a
   fifth-power divisibility before the final native projection.
2. Set `I=2r c^2`, separating the strong Pell scale from the guard coordinate
   while preserving the evenness required by the coprime parent's parity
   argument.
3. Use `Dg=1+D Dt s^2`. The previous factor 4 is unnecessary because the
   centered budget is always a multiple of 4.
4. Give the strong, auxiliary, and fused roots weights 2, 1, and 4, and
   translate the free integer coordinate by `QV`. The already live `QV`
   register is reused.

The ordinary arithmetic proof below restores exactly the inherited source
whose finite-refutation calibration is retained in `source/`. The logical
conclusion is the same ZFC-provable biconditional as that source:
the selected polynomial has an integer zero if and only if there is a
finite syntactic ZFC refutation. The report neither proves consistency nor
supplies a new proof-assistant or encoded object-ZFC proof of the whole
calibration. Exact finite artifact checks and the unbounded ordinary proof
are separately identified.

## 1. Complete polynomial definition

The independent coordinates are

    j,C,z,h,r,v,w,T,c,n,s in Z.

The six fixed positive integers `beta,K0,MC,MF,cone_A,cone_B` are the whole
source34 tuple, supplied by their complete compressed payloads, byte hashes,
and finite reconstruction recipe in `coefficients/`. In particular,

    beta=2^1064921-1, cone_A=2^1113, cone_B=2^666104.

The `MF` payload is already shifted, as recorded in `BINDING.json`. None of
these six values is a quantified variable or selected by a consistency
search. Define the following integer polynomials:

    J=6j+1; q=beta J+1; W=12w+4;
    X=qW; Y=(2v+1)q^3; E=XY;
    a=E+Y; H=4a+3; Delta=a^2+H=(a+2)^2-1;
    F=(K0+W)C-z(q-1);
    R=(q(q-F)-C)(q^2-1)+(MC+q MF)J;
    k=R+1+hE; eta=c-Yk;
    Derr=(cone_A F-q)^2+(cone_B C-q)^2;
    Budget=k^2(q^2-Derr)-4q^2 eta^2;
    D=3Budget-4; ell=XY^2; L=ell k;
    Dt=1+L(L+k);
    Dg=1+D Dt s^2; P=Dt Dg;
    I=2r c^2; Df=1+Delta I^2;
    Q=Delta^2 I^2; delta=Q-1;
    V=Df(c-R+4IT)-c;
    Cy=QV^2-1; Da=delta Cy;
    K=X(3c-2X)+2;
    S=srH; zc=HT+K;
    Ac=(zc^2+3H^2)(zc^3-19H^3).

For the selected polynomial put

    Z=S(n+QV)-Ac;
    u=4S^2 Df; b=S^2 Da; e=16S^2 P,

and define

    E8 = [(Z^2-u-b-e)^2-4(ub+ue+be)]^2-64ube Z^2.

The equation is **E8=0**. The direct companion replaces `Z` by `Sn-Ac`.
Every displayed abbreviation is substituted into the final expression.
The literal JSON graphs contain only integer leaves, the eleven variables,
the six fixed numerals, and binary addition, subtraction, and multiplication.
No radical, division, variable exponent, or implicit witness is an operation
of either polynomial.

The universal identity

    E8 = product_{epsilon in {-1,1}^3}
             (Z-epsilon1 sqrt(u)-epsilon2 sqrt(b)-epsilon3 sqrt(e))

holds in the free triquadratic algebra, including after specialization to
dependent, negative, or zero radicands. The finite checker proves equality
of all 35 collected coefficients by multiplying the eight factors.

The two polynomials have equivalent integer-zero existence by the
polynomial bijection `n_direct=n_centered+QV`, with all other coordinates
fixed. This does not claim that the two polynomials are identical.

## 2. Unconditional facts and the smaller positivity guard

The unchanged source restrictions give, for every integer assignment,

    q even, q=2 mod3, |q|>=beta-1>=16,
    X=2 mod3, |X|>=4|q|>=64,
    |Y|>=|q|^3>=4096.

Consequently `a` is even, `H` is odd and nonzero, and `Delta>1` is 3 modulo
4. Also `Dt>=1`: it equals `1+ell(ell+1)k^2`, and an integer consecutive
product is nonnegative. Since `X` is a multiple of 8, `Dt=1 mod8`.

Both cone coefficients and `q` are even, so `Derr` is a multiple of 4.
Hence

    Budget=0 mod4, D=0 mod4, Dg=1 mod4.

This unconditional congruence is why the additional factor 4 of the old
guard can be deleted. It must be established from the actual even cone
coefficients; treating them as arbitrary symbolic constants would not
justify the deletion.

The polynomial `pi(t)=(t^2+3)(t^3-19)` has no rational root. Therefore
`Ac=H^5 pi(T+K/H)` never vanishes, because `H!=0`. If `S=0`, the norm
equation becomes `Ac^8=0`, which is impossible. At any zero, `S!=0` and
therefore `s,r!=0`.

This step does not yet prove `c!=0`. If `c=0`, then `I=0`, `Df=1`, `Q=0`,
`delta=Cy=-1`, and `Da=1`. If `c!=0`, then `|I|>=c^2`, `Q>1`, and
`Df>|c|+1`. Writing `bfront=c-R+4IT`, either `bfront=0`, so `|V|=|c|>=1`,
or `|V|>=Df-|c|>1`. Thus `Da>0` in either case, including `c=0`.

At a zero, a conjugate norm factor vanishes. If `Dg<0`, the radical of
`e=16S^2 Dt Dg` is its only nonzero imaginary term, since `Df,Da>0`.
This is impossible. Since `Dg=1 mod4`, it follows that `Dg>0`. If
`Budget<=1`, its divisibility by 4 gives `Budget<=0`, whence `D<=-4` and

    Dg=1+D Dt s^2<=-3.

Therefore `Budget>=4`, in particular `Budget>0`. It follows that `k!=0`,
`Derr<q^2`, and `|eta/k|<1/2`. The disk inequality supplies the common
strict sign of `q,F,C,q-F-C`, exactly as in the centered source. More
explicitly, with `U=cone_A F` and `W1=cone_B C`,

    (U/q-1)^2+(W1/q-1)^2<1

gives `0<F/q<2/cone_A`, `0<C/q<2/cone_B`, and `F/q+C/q<1`.
Since `|Y|>=4096` and `c/k=Y+eta/k`, we also obtain `c!=0`,

    |k|(|Y|-1/2)<|c|<|k|(|Y|+1/2),
    sign(c)=sign(kY).

Only now assert `I!=0` and `Q>1`. This order prevents a circular
nonzero assumption in applying the Pell descent.

## 3. Three radicals recover all four square conditions

The positive radicands `Df,Da,P` are odd: `I` is even, so `Df=1 mod4`,
`Q=0 mod4`, and `Da=1 mod4`; both `Dt` and `Dg` are odd. Dividing a
vanishing norm factor by the nonzero integer `S` says that a signed sum

    2 sqrt(Df) + sqrt(Da) + 4 sqrt(P)

is rational. A positive odd integer radicand is an odd square times an
odd squarefree integer. Distinct squarefree radicals are linearly
independent over the rationals. Inside any nontrivial squareclass, the
least 2-adic valuation of its participating coefficients is unique, since
the weights are 2, 1, and 4 and all multiplying square roots are odd.
Such a class cannot cancel. All three radicals are therefore rational,
and hence integral.

Moreover

    gcd(Dt,Dg)=gcd(Dt,1+D Dt s^2)=1.

Positive coprime integers whose product is a square are separately
squares. Thus integral roots exist with

    f^2=Df, tau^2=Dt, g^2=Dg, ytilde^2=Da.

Set `y=ytilde/delta`. It satisfies

    QV^2-(Q-1)y^2=1.

The adjacent-coefficient descent makes this rational `y` integral.
For completeness, if `y=a/b` is reduced then `b^2|Q-1`; the transformations

    V'=(2Q-1)V-2(Q-1)y,
    y'=(2Q-1)y-2QV

preserve the equation, keep `V'` integral, and preserve the reduced
denominator `b`. With positive signs and `|V|>1` one has
`-|V|<V'<|V|`, while the norm excludes `V'=0`. Descent reaches
`|V|=|y|=1`, so `b=1`. The hypotheses `Q>1` and integral `V` were
proved first.

All normalized radicals are now integers. The factor equation therefore
gives `S|Ac`, and reduction modulo `H` gives

    H | K^5.                                                    (1)

We do not infer `H|K` from (1) alone.

## 4. Recover the missing main Pell condition before projection

This stage uses the unchanged, retained signed folding and centered rank
lemmas; it does not use the stronger determinant guard of the separate
twelve-integer source. The full source interfaces are
`source/signed-quadratic-proof.md`, Sections 2 and 5, and
`source/centered11-proof.md`, Section 5.2. Their relevant hypotheses are
precisely the common native signs, centered strip, first norm, strong norm,
auxiliary norm, and residues now established:

    f^2-Delta I^2=1,
    tau^2-XY^2(XY^2+1)k^2=1,
    QV^2-(Q-1)y^2=1,
    V=-c mod f, V=-R mod c,
    c^2|I, I!=0.

The second residue follows from

    V+R=Delta I^2(c-R)+4I Df T.

Here is the content of the inherited folding argument, to expose the
interface rather than hide a missing main norm. Define the Pell sequences
by `chi_A(m)+psi_A(m)sqrt(A^2-1)=(A+sqrt(A^2-1))^m`. With
`A=|a+2|`, write `|f|=chi_A(m0)`, `|I|=psi_A(m0)`. The auxiliary norm
at parameter `rho=Delta|I|` has an odd index `nu`; the exact odd-index
quotient identity and residue modulo `f` give
`psi_A(nu)=+/-|c| mod |f|`. Reducing and reflecting the index modulo
`2m0`, the strict bound `2|I|<|f|` prevents wrapping and yields
`|c|=psi_A(p)` for a positive index `p`. Thus the main norm is recovered,
not assumed.

The divisibility `c^2|I` gives `p|m0` and `|c||m0` by the Pell
multiplication formula. The auxiliary residue modulo `c`, the first
norm, and the native packing estimates then identify the two small
indices. These are exactly the pre-projection conclusions of the centered
source; no oddness of `I/c^2` is needed. With `x=|X|` and
`sigma=sign(c)`, they give

    R=2t+1, t>=24,
    c=sigma psi_(a+2)(R),
    |Y|>(x-3)^t/2-1,
    |H|>x(x-3)^t.                                           (2)

For the last estimate, use `|H|>=4(x-1)|Y|-3`; after substituting the
preceding bound its excess over `x(x-3)^t` exceeds
`(x-2)(x-3)^t-4x+1>0` at `x>=64,t>=24`.

## 5. Fifth-power saturation completes the projection

Put `Kquad=X(X+2ac)-1`. The exact polynomial identity

    K=HXc-2Kquad

and oddness of `H` show from (1) that `H|Kquad^5`. The retained signed
Pell congruence is

    2^R Kquad = (sigma X-2^R)(2^R sigma X+1) modulo H.

Let the product on the right be `Pi`. Taking fifth powers gives
`H|Pi^5`. There is no illicit cancellation of a nonunit modulo a composite
integer in this deduction.

The actual, unchanged coefficient `beta` gives

    x>=4(beta-1)>=2^64.

Both factors of `Pi` have absolute value less than `2^(R+1)x`. Consequently

    |Pi|^5<2^(10R+10)x^10=2^(20t+20)x^10.

On the other hand, (2) and `x-3>x/2` imply

    |H|>x^(t+1)/2^t.

For `t>=24` and `x>=2^64`,

    x^(t-9)>=2^(64(t-9))>2^(21t+20),

because `64(t-9)-(21t+20)=43t-596>=436`. Therefore
`|Pi|^5<|H|`. The integral divisibility `H|Pi^5` forces `Pi=0`.
Its second factor is odd and nonzero, so `sigma X=2^R`.

The source's final orientation and centered half-binomial argument now
give `X,c,k,Y>0`, `0<eta/k<1/4`, and the exact main projection. In
particular Section 5.4 of `source/centered11-proof.md` explicitly
regenerates a fresh odd strong/auxiliary pair and an actual old signed
Q41 zero. It does not relabel the incoming even strong multiplier as odd.
The retained ordinary native/compiler/refutation calibration therefore
supplies a finite syntactic ZFC refutation.

This completes soundness for every signed assignment to all eleven
coordinates.

## 6. Supported-modulus interpolation and completeness

The inherited interpolation theorem is stated and proved in
`source/POWERED_PROOF.md`, Section 5. Its interface is important here.
Suppose `A0>1` is even, `Delta=A0^2-1`, `R=3 mod4`, and
`c=psi_A0(R)>0` with `c=R mod4`. Given a positive `s`, choose one
positive strong pair satisfying

    I=psi_A0(m0), f=chi_A0(m0), 4s c^2|I.

For this same fixed pair, every residue class modulo every positive
integer `M` whose prime divisors divide `I` contains a `T` such that

    V=f^2(c-R+4IT)-c,
    (Delta I)^2 V^2-((Delta I)^2-1)y^2=1

has an integer `y`. The strong pair does not depend on the subsequently
selected residue.

This extends the earlier interpolation only modulo `I`. It is not
justified by the first-order congruence alone. The retained proof takes
`lambda=4m0 f` as a period modulo `f^2`, sets `d=lcm(lambda,4I)`, and
uses the Pell indices `nu(h)=nu0+dh`. For every prime `p|I`, it proves

    v_p(T(h1)-T(h2))=v_p(h1-h2).

The key identity is `v_p(d)=v_p(4I)`; elementary Pell lifting proves the
displayed equality, including `p=2`. Thus `h -> T(h)` induces a
bijection on every `Z/p^e Z` with `p|I`; CRT gives every requested class
modulo `M`. The full valuation calculation is copied in the source.

Now start with the same canonical outer witness supplied by a finite
syntactic refutation in the calibrated source. Keep `j,C,z,h,v,w,c`.
Its centered estimates give

    Derr<=q^2/2, 0<eta/k<1/4,
    Budget>q^2 k^2/4>=64,

and `Dt=tau^2` is a positive square. Also `Dt=1 mod3`: since `X=2 mod3`,
`ell=XY^2` is 0 or 2 modulo 3, so `ell(ell+1)=0 mod3`.
Consequently `D Dt` is positive and 2 modulo 3, hence nonsquare.
Ordinary Pell existence supplies positive integers `g,s` with

    g^2-D Dt s^2=1.

This is the revised guard directly; the old extra squaring of a Pell unit
is unnecessary. We now have `P=(tau g)^2`.

The canonical source has exactly the interpolation hypotheses above,
with `A0=a+2`. Choose one fixed `I,f` divisible as stated, and define

    r=I/(2c^2).

Then `r` is a positive integer divisible by `2s`, and `I=2r c^2` exactly.
For `M=sr`, every prime of `M` divides `I`. This prime-support condition
is sufficient even though `M` need not divide `I`.

The canonical main projection gives `H|K`; set `kappa=K/H`. The polynomial
`pi(x)=(x^2+3)(x^3-19)` has a root modulo every positive integer. For
clarity, at odd primes other than 3 and 19, either the cube map is bijective
or a primitive cube root of unity gives a root of `x^2+3`; all chosen roots
are simple. At 2 the cubic has a simple odd root. At 19 the quadratic has
the simple root 4. At 3 write `x=1+3u`: the equation `x^3=19` becomes
`u+3u^2+3u^3=2`, whose derivative is 1 modulo 3. Hensel lifting and CRT
give roots modulo every prime power and then every modulus. The complete
original argument is retained in `source/PRIME_TWELVE.md`.

Choose a residue `a0 mod M` with `pi(a0+kappa)=0 mod M`. Only after
this choice invoke supported-modulus interpolation to obtain
`T=a0 mod M` and an integral `y`, keeping `I,f,r` fixed. Then

    Ac=H^5 pi(T+kappa),
    Ac/S=H^4 pi(T+kappa)/(sr) in Z.

Finally take

    n=Ac/S+2f+delta y+4tau g-QV

for the selected equation, or omit `-QV` for its direct companion. One
conjugate factor vanishes. The quantifier order is outer data, guard
pair `s,g`, one fixed strong pair `I,f,r`, intersective residue, auxiliary
pair `T,y`, then `n`. There is no circular choice of the strong pair after
the residue is selected.

Together with soundness, this proves integer-zero existence equivalent to
finite syntactic refutability of ZFC, by composition with the explicitly
retained ordinary calibration.

## 7. Exact degree and operation counts

All eleven variables have total degree 1 and all fixed numerals degree 0.
The relevant prefix degrees are

    I:3, S:8, Df:18, Q:30, V:23, Da:106,
    Dt:34, Dg:60, P:94, Ac:35,
    u:34, b:122, e:110.

For the selected center let `B0=Sn-Ac` and `C0=SQV`, so `Z=B0+C0`.
The exact cancellation is

    b-C0^2=-S^2[Q(V^2+1)-1],
    omega:=Z^2-b
          =B0^2+2C0 B0+S^2[Q(V^2+1)-1].

Its three displayed terms have degrees 70, 96, and 92, respectively.
Thus `omega` has degree 96. Rewrite the same norm as

    [(omega-u-e)^2-4(ub+ue+be)]^2-64ube Z^2.

Inside the outer square the unique highest term is `-4be`, of degree
232. The final subtracted term has degree 388. Hence the selected total
degree is 464 with leading homogeneous form `16 b_top^2 e_top^2`.
The raw evaluator's naive syntactic bound 488 is therefore not its actual
degree. The checker applies the exact cancellation at its precise live
node, and proves a nonzero leading coefficient through every live node.

For the direct companion, `deg Z=35`; the unique leading form is
`b_top^4`, of degree 488.

To show that the leading coefficients remain nonzero after binding the
actual full numeral tuple, put

    q0=6 beta j, Y0=2v q0^3, a0=12w q0 Y0,
    F0=12wC-q0 z, R0=-q0^3 F0.

Then

    b_top=2^12 s^2 r^10 c^16 a0^14 R0^2,
    e_top=-3*2^10 s^4 r^2 h^6 q0^2 a0^12 Y0^6.

In the selected polynomial the coefficient of

    C^4 j^260 w^56 v^64 h^12 s^12 r^24 c^32

is exactly `2^484 3^318 beta^260>0`; the variable exponents sum to 464.
In the direct polynomial the coefficient of

    C^8 j^248 w^64 v^56 s^8 r^40 c^64

is `2^480 3^312 beta^248>0`; the variable exponents sum to 488.
These are actual coefficient identities, not numeric samples or generic
coefficient assumptions.

The selected graph has 77 multiplications, 24 additions, and 21
subtractions, for 122 operations. The direct graph has the same 77
multiplications and 21 subtractions, and 23 additions, for 121. Each square
and fixed-scalar multiplication costs one operation; numeral leaves and
register reuse are free. The center adds just one live addition because
`QV` is already used in forming `Cy=(QV)V-1`.

## 8. Reproduction and scope of checks

Run `python3 build.py`, `python3 check.py`, and `python3 -O check.py`.
The checker authenticates all six complete numeral payloads, reconstructs
the full native coefficient tuple from its finite recipe, authenticates
the retained source files, checks every live arithmetic gate through exact
free-ring register identities, independently multiplies all eight generic
conjugates, proves the exact center and projection identities, checks all
live topology and operation counts, and establishes the degree bounds
and attained coefficients. It also regenerates both JSON artifacts exactly.
No check is disabled by Python optimization; failures use explicit raises.

The source notices and licenses are retained. The DAG helper and sparse
polynomial primitive are credited adaptations of the incoming package.
`source/COPRIME_PROOF.md` and `source/POWERED_PROOF.md` identify the two
immediate mathematical parents; their retained dependencies identify the
native/compiler and finite-refutation interfaces. Independent ordinary
review of this composition is supplied separately by the parent report.

These finite checks establish concrete transcription, identity, size,
degree, coefficient, and reproducibility claims. They do not turn an
ordinary mathematical calibration proof into a new Lean/Rocq certificate,
prove Con(ZFC), or establish global minimality of any metric.

## 9. Further research questions

The current leading degree is controlled by the interaction of the
auxiliary radicand with the fused first-Pell/guard radicand. Can a smaller
coprime guard preserve the centered strip and the noncircular witness
order? Can a new interpolation chart shorten `Ac` while excluding all
zero-carrier assignments? Can the prime-support interpolation proof be
formalized once as a reusable arithmetic theorem, so future compositions
have a compact checked dependency rather than repeated ordinary proofs?
These are open directions, not claims of further reductions in this packet.
