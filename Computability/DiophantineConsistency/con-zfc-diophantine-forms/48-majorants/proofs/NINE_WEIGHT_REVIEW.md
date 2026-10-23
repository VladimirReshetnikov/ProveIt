# Independent review of the smaller separating weight

The root's proposed replacement of the old separating weight by `h` is sound under the stated positive-domain assumptions. This review concerns a universal algebraic lemma; it does not assume that the tuple already satisfies any Pell or source equations.

Assume `R,N>=8`, positive integers `w,s,h,i,j,b`, and nonnegative `phi` in the source domain. Define

    U=N^2*w, Y=N^2*s, M=R*Y,
    P=2*M^2*U, K=R+1+h*(P-1), A=M*(U+1),
    C=2*R+1+b*w+phi, J=4*A-5,
    D=(A^2-1)*C^2+1,
    E=i*J*D*C^2, F=(A^2-1)*E^2+1,
    G=A+F*(C*D+1-A), H=2*R+1+j*C,
    I=(G^2-1)*H^2+1,
    a0=(P^2-1)*K^2+1, a1=D*F*I,
    d=i*J*D*C, V=D*d*G*H, Bstar=P*(P+R).

The definition of `d` is a polynomial. The equality `d=E/C` is used only to explain its origin and is not a division in the output equation.

## The two strict root bounds

First, `K>1`, so

    a0=P^2*K^2-K^2+1 < (P*K)^2.

Moreover,

    h*(P+R)-K=(h-1)*(R+1)>=0,

and therefore `sqrt(a0)<h*Bstar`.

The parameter sizes imply `A>=2`, `C>1`, `d>=3`, and `H>=1`. The identity

    A^2-2*P=M^2*(U-1)^2>0

gives `D>A^2>2P`, and `E>D`. Consequently

    F>(2P-1)*(2P)^2>2P^2.

Also `R<P`, so `Bstar=P(P+R)<2P^2`. Since `CD+1-A>1`, it follows that `G>F>Bstar`, with enough integer margin to conclude `G>=Bstar+2`.

Because `I=(G^2-1)H^2+1>=G^2`, we obtain `a1>=I>=G^2>Bstar^2`, hence `sqrt(a1)>Bstar`.

For the upper bound, `E=Cd` and `D-1=(A^2-1)C^2` yield

    F=(D-1)*d^2+1=D*d^2-d^2+1.

An exact expansion now gives

    V^2-a1 = D^2*d^2*(H^2-1) + D*I*(d^2-1).

As `G>=Bstar+2` and `H>=1`,

    I=(G^2-1)H^2+1 > Bstar*G*H.

Since `d>=3` implies `d^2-1>2d`, the second term alone is strictly greater than `2*Bstar*V`. The first term is nonnegative. Thus

    V^2-a1 > 2*Bstar*V.

The quantities are positive and `V>Bstar`, so

    (V-Bstar)^2-a1 > Bstar^2>0,

and `sqrt(a1)<V-Bstar`.

In particular,

    sqrt(a0)<h*Bstar<h*sqrt(a1).

This is the separation inequality required to rule out zero signed radical sums.

## The new polynomial finalizer

Let the inherited source provide positive `u,v,Mdiv` satisfying `0<v/u<Mdiv-1`. The margin `m=K^2*Gcap-4*(C-KY)^2*Gcap-8*g*K^2` is an integer polynomial in the existing witnesses, not an extra variable. With the nonnegative finalizer witness `n`, put

    Theta=u*(n+Mdiv)+v-u*m*(2*Mdiv+h*V),
    Q=(Theta^2-(u*m)^2*(a0+h^2*a1))^2
        -4*(u*m)^4*h^2*a0*a1.

The factorization over a splitting field shows that `Q=0`, when `um!=0`, makes `Theta/(um)` a signed sum of `sqrt(a0)` and `h*sqrt(a1)`. This rational sum is nonzero by the strict separation just proved. If `r=epsilon*sqrt(a0)+delta*h*sqrt(a1)` is a nonzero rational, then

    sqrt(a0)=(r^2+a0-h^2*a1)/(2*epsilon*r)

is rational, and the other root is rational as well. Rational square roots of integers are integers. This argument does not require independent square classes.

Write the signed integer roots as `r0,r1`. The strict integral bounds imply

    r0>=-h*Bstar+1,
    r1>=-V+Bstar+1.

Therefore the reconstructed integer

    Z=2*Mdiv+h*V+r0+h*r1

satisfies

    Z>=2*Mdiv+h+1.

The polynomial equation then gives

    n+Mdiv+v/u=m*Z.

As in the old finalizer, `m=0` is impossible because the left side is positive; positivity of Z and the left side forces `m>0`. Integrality yields `u|v`. Conversely, when the roots are integral, `u|v`, and the computed margin `m>0`, keep that margin and set `n=m*Z-Mdiv-v/u`; the size bound makes n nonnegative (indeed positive). Thus the existential finalizer equivalence is preserved without adding a witness or changing the margin.

The old proof's exact source bounds and variable domains still have to be retained. In particular, this lemma does not justify extending the nine-variable equation to arbitrary integer domains without separate positivity guards.

## Review conclusion

No algebraic, sign, or denominator gap was found in the proposed substitution. The relation-combining polynomial uses the smaller weight `h` and center `hV` while preserving the full existential interface. Operation counts and exact total degree must be computed from the emitted literal circuit, with the new defect identity used to expose cancellations.
