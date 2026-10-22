# Unscaled saturation: the improved twelve-positive and twenty-six-integer forms

## Verdict

The unscaled-y resultant needs neither `i=Hj` nor the replacement of y by
`(Q-1)y`. The rational auxiliary Pell saturation lemma can be applied
**before** restoring gamma. This gives the simpler valid construction
with exact degrees 1257 over twelve positive variables and 2465 over
twenty-six unrestricted integers. Circuit operation totals must be read
from the final emitted files; this note proves the mathematical change
and the uniform degrees independently.

This construction supersedes the degree-heavier variants in the preceding
audits. Their conclusions remain valid, but their extra divisibility or
scaling is unnecessary once rational Pell saturation is available.

## 1. Definition and conjugate bounds

Retain the original normalized i; do not multiply it by H. Use

    A1=1+L(L+k), A2=1+Delta c^2,
    I=i c^2, S=Delta I, Q=S^2, D=1+I S, d=Q-1,
    v=cT, b=c+RD, e=Q(Dv^2+b^2)-1, B=2Qvb.

For positive supplied ports take `W=2(Sv+b)`. For the seven-positive-port
signed domain with `i=2r+1`, `w=w0^2`, and signed h,T,t, take

    W=2*((S*i)*v²+b).

There is **no factor d in either W**. With P=HW put

    K=P+1, M=6W, u=6P=HM, Z=Ht+K(X+ac).

The unscaled formal factor is

    F(tau,g)=[d(Z-u tau-Kg)^2-H^2 e]^2-H^4 B^2 D,
    tau^2=A1, g^2=A2.

Let Res be its four-sign norm. The equation is

    Nk Nt(1+Res)-1=0,

or equivalently the system Nk=Nt=1, Res=0 after soundness. The same
mod-four norm argument excludes 1+Res=-1 without any new premise.

On a vanishing branch put `y=(Z-u tau-Kg)/H`. If B!=0, define

    f=(e-dy^2)/B.

Then f^2=D and `dy^2=e-Bf`. The same relation holds for every actual
conjugate. Because sqrt(D)<|S|, Q/d<2, and
`(S*i)v²>=|S||v|` on the signed domain, every such conjugate satisfies

    |y'|<sqrt(2)(|S||v|+b)<W.

If B=0, then v=0 and the factor directly gives

    dy^2=e=Qb^2-1,

so every conjugate again has |y'|<sqrt(2)b<W. Thus this bound is valid
without first excluding T=0 or dividing by B.

## 2. Rationality, saturation, and only then gamma

When X>0, the already proved `A2<16A1` and the weights above give

    u sqrt(A1)>K sqrt(A2)+HW,
    K sqrt(A2)>HW.

The same multiquadratic Galois argument first fixes tau and then g. They
are rational with integral squares, hence integers. The defining linear
relation now makes y rational.

If B!=0, f is rational and f^2=D is integral, hence f is integral. Set
`V=vf-b`, an integer. Then

    S^2 V^2-(S^2-1)y^2=1.

The rational auxiliary Pell saturation lemma, applied with |S|>1,
proves y integral. If B=0, the same lemma applies directly with V=-b,
using `dy^2=Qb^2-1`. It does not require an f in that branch.

Only now set gamma=(g-X-ac)/H. Its denominator divides H and

    K gamma=t-M tau-y

is an integer. Since K=1 modulo H, gamma is an integer. This order
avoids any use of gcd(H,d), any restriction on i beyond its original
domain, and any claim that y is automatically integral merely because
dy^2 is integral.

## 3. Signed zero-square boundary

For the twenty-six-integer domain allow w=w0^2 to be zero initially.
Then tau^2=A1=1, so tau is already an integer. The second separation
inequality `K sqrt(A2)>HW` still holds and forces g to be rational,
hence integral. Consequently y is rational.

The two B branches from Section 2 apply unchanged: either recover
integral f and saturate with V=vf-b, or saturate directly with V=-b.
In both cases y and then gamma are integral. The retained main norm
therefore gives, at X=0,

    (ac+H gamma)^2-(a^2+H)c^2=1.

Reducing modulo H yields 0=1, impossible. This excludes w0=0 before
the first separation inequality is ever used. No circular growth or
integrality assumption enters this boundary argument.

## 4. Signed zero auxiliary quotient and final soundness

After w>0, the source weak bootstrap gives Delta>R and 1<b<Q, exactly
as in the preceding twenty-six-integer audit. If T=0 then B=0 and
saturation has already made y integral in

    Qb^2-(Q-1)y^2=1.

As before, |y|>=b+1 contradicts b<Q. Therefore T!=0 and B!=0. The
formula for f is now available, and all normalized source equations
are restored with the exact signed domain proved by package 14.

For twelve positive supplied variables, T and i are positive from the
outset and X>0, so neither boundary argument is needed. The same
saturation-first order gives integral gamma and the signed-core theorem
supplies soundness for the recovered roots.

## 5. Completeness is immediate

For twelve positive variables start with any old normalized positive
solution. For twenty-six integers use the already available canonical
odd-i/square-w positive solution. Keep every retained coordinate and put

    t=M tau+K gamma+y.

It is positive on the canonical positive solution, though the integer
variant does not need that sign. Its corresponding formal factor
vanishes. Thus no Pell-period choice, new congruence, or new completeness
lemma is needed in either domain.

## 6. Uniform exact degrees

For the twelve-positive-variable form, the relevant ordinary degrees are

    deg(d)=46, deg(K)=deg(u)=44, deg(L)=11, deg(Z)=55.

Both radicands have leading square Ltop^2. In the four formal factors,
the highest linear forms `Z-u tau-Kg` are

    Ktop Ltop * (-6), Ktop Ltop * (-4),
    Ktop Ltop * 6, Ktop Ltop * 8.

The terms H^2 e and H^4 B^2 D are strictly lower than their respective
competitors. Consequently

    Res_top=1152^4*dtop^8*(Ktop Ltop)^16.

It is nonzero and has degree `8*46+16*(44+11)=1248`. The outer index
and transport factors add 7+2, giving exact degree **1257**.

For the twenty-six-integer form, using weight two on the seven positive
ports and w, and weight one on the other supplied variables,

    deg(d)=90, deg(W)=74, deg(K)=deg(u)=86,
    deg(L)=22, deg(Z)=108.

The sign-safe extra product `(S*i)v²` has degree 68, below b's degree
74, so it does not alter W's leader. The same nonzero leading form has
degree `8*90+16*(86+22)=2448`. The outer factors add 13+4, giving exact
degree **2465**.

Writing Q0=beta J and k0=eta+zeta, independently computed leaders are

    dtop=i^2 k0^4 w^4 s^8 Q0^28,
    Ktop=8i^2 k0^4 w^3 s^7 Q0^27(Q0-F),
    Ltop=w k0 s^2 Q0^7.

After odd/square substitutions and the seven positivity maps, the
degree-2465 monomial

    J_a^1578 h r^48 eta_a^224 w0^194 s_a^418 z_a^2

has coefficient `+2^124*3^8*beta^789`, which is nonzero for beta>0.
This supplies a uniform exact-degree certificate independent of finite
numerical tests.

## Scope

The mathematical revision is approved. It retains the same compiler,
signed-domain and formalizability dependencies; it is not a new
proof-assistant certification or a global minimality claim. The final
frozen circuits must separately confirm their advertised operation
counts and coefficient bindings.

### Final literal-circuit check

The final emitted files were subsequently checked independently:

- `roots/root12_saturated_product.json`: twelve variables, 139 operations
  (93 multiplications and 46 additions/subtractions), SHA-256
  `fbfa374237b93dc02da02bf2b13387e7751fc826dd28758385e77c698841554c`.
- `integers/integer26_unscaled_four_root192_degree2465.json`: twenty-six
  variables, 192 operations (117 multiplications and 75 additions/subtractions),
  SHA-256 `a115e85d85a1750e58742e9859bcbb82572e01228ad707ad27ba96d212f9b640`.

Every gate and input is live. Each file passed 240 fresh comparisons
against independently coded direct rank-four multiplication, including
signed/zero inputs for the integer variant. The receipt is
`UNSCALED_FINAL_CIRCUIT_CHECKS.json`; its executable checker was independently
authored and interprets received JSON only as inert arithmetic data.
