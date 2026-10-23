# Optional lower-degree twelve-positive-variable variant

Keep all definitions and the proof of NORM12_PROOF.md except the weight.
Write I=i*c^2 and replace Bnd by

    W = 4*T*I + 2 + 2*R*(a+6)*i^2*c^3,
    L = 1+H*W.

The same finite polynomial norm and three finalizers are used. This
alternative has positive supplied variables only; the signed integer26
extension is not claimed for this weight.

## Conjugate separation proof

The weak outer bootstrap gives R>0 and k=R+epsilon+hE>R, since
epsilon in {1,-1}, h>0, and E>2. Thus c>R. Also a>=2 and c>1.
Every auxiliary conjugate satisfies

    |y'|<2*(v*sqrt(D)+b),

as in the primary proof. Moreover sqrt(G)>a*c, and
sqrt(D)<(a+2)*I. Therefore

    |y'|/sqrt(G)
      < 2*T*I*(a+2)/a + 2/a + 2*R/(a*c)
         + 2*R*(Delta/a)*i^2*c^3
      < 4*T*I + 2 + 2*R*(a+6)*i^2*c^3 = W.

The second line uses (a+2)/a<=2, R<c, 2/a<=1, and
Delta/a=a+4+3/a<a+6. Hence

    H*|y'| < H*W*sqrt(G) < L*sqrt(G).           (1)

Also H*sqrt(A)>2*sqrt(G). Indeed sqrt(A)>kEY,
sqrt(G)<(a+2)c<2(a+2)kY, and E>=2 gives

    H*E >=2H=8a+6>4(a+2).

Combining this with (1),

    H*L*sqrt(A)>2L*sqrt(G)>L*sqrt(G)+H*|y'|.

These are precisely the two separation inequalities needed to force the
first root and the main root rational in the primary proof. Everything
after that, including the special auxiliary Pell integrality lemma,
main congruence, signed-gamma bridge, parity finalizer, and canonical
positive completeness, is unchanged. The new positive witness is
r=gamma+W*u+L*t+y.

## Exact size

Now deg(W)=27 and deg(L)=33. The norm leading form is the primary leading
form divided by (a_top*c_top)^16, namely

    2^80*i^48*k0^96*w^96*s^192*q0^720*(q0-F)^16,

where q0=beta*J and k0=eta+zeta. Thus the exact norm degree is 1168 and
the product degree is 1177. Its coefficient at

    J^741*h*z*i^48*eta^96*w^97*s^193

is +2^80*beta^741, uniformly nonzero. The sum of squares has degree2336.

| Presentation | Variables | Equations | Degree | Operations |
|---|---:|---:|---:|---:|
| Lower-degree system | 12 positive | 3 | max1168 | 119 |
| Lower-degree product | 12 positive | 1 | 1177 | 123 |
| Lower-degree SOS | 12 positive | 1 | 2336 | 126 |

The separate builder emits these three packets and compares each norm to
the independent eight-component conjugate-product evaluator on 24 signed
assignments. Signed fixtures check polynomial identities only; semantic
equivalence here is claimed over the positive supplied domain.
