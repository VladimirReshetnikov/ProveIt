# A toy-port zero after freeing the strong/auxiliary ordinate

Consider the maintained 65-gate graph, but let the input formerly called
`i` supply `S` directly, and delete `normalized_S=i*Delta*c²`. This keeps
14 positive inputs and produces 64 live operations. An original positive
zero maps forward via `S=i*Delta*c²`; the reverse map requires divisibility
by `Delta*c²`.

The symbolic construction below gives a full positive zero at the **toy**
ports

```
beta=31, K=9, MC=14, MF=46.
```

They satisfy `beta>=31`, `K>0`, and `0<MC<beta<MF<2*beta`; they are not
the current ports. At this zero `S=Delta*c` with `c>1`, so the original
strong factor cannot be repaired by any positive original `i` while the
other coordinates are fixed. The huge Pell values are symbolic and
unexpanded. This has passed independent external review; it is not a Lean/PDF result,
current-port zero, or unrestricted existential nonequivalence.

## Scalar and first/main factors

Set

```
q=32, J=1, F=1, alpha=14, C=17, gap=975,
R=998911, X=2^R, w=2^(R−5), N=(R−1)/2,
Y=(1/2)*sum_{j=0}^N binom(2N,j)*X^(N−j),
s=Y/q³, E=X*Y, h=E*Y, a=E+Y, A=a+2,
H=4*a+3, Delta=A²−1.
```

The checker verifies the literal rank, `R=3 mod 4`, and
`v2(Y)=popcount(N)−1=15`, so s is a positive odd integer. It also checks
`w=2 mod 31`; hence

```
z=1+((K+w)*C−F)/31
```

is a positive integer and the transport factor is 1. The valuation and
following Pell/floor facts use the reviewed general argument in
`../current14-carrier64-current-full-zero/`, not a new kernel theorem.

Write `(u+sqrt(u²−1))^j=chi_u(j)+psi_u(j)*sqrt(u²−1)`, and set

```
k=2*psi_(2h+1)(N+1), tau=chi_(2h+1)(N+1),
c=psi_A(R), D=chi_A(R),
eta=c−Y*k, zeta=k−eta, n=(tau−k+R)/E,
gamma=(D−X−a*c)/H.
```

The general binomial floor bound gives `Y<c/k<Y+1`, so eta and zeta are
positive. The first-Pell congruences and growth give positive integer n;
the trace recurrence gives positive integer gamma. The first and main
norm factors are both 1.

## Free ordinate and auxiliary norm

In the 64-gate graph set the fresh input `S=Delta*c` and set `f=D`. The
main norm immediately gives

```
Delta*f²−S² = Delta*(D²−Delta*c²) = Delta,
```

so the normalized strong factor is 1. Since R is 3 modulo 4, put

```
V=chi_S(R)/S,  y=psi_S(R).
```

The reviewed odd-index Chebyshev congruences give `V=−c mod f²` and
`V=−R mod c`: use `S²=−Delta mod f²` and `c|S`. Also `f²=1 mod c`.
Thus `T=(V+c+f²*R)/(c*f²)` is a positive integer, the literal V equation
holds, and the auxiliary norm equals 1. All five normalized factors are 1,
so the 64-gate candidate vanishes.

For the same other coordinates, an original positive zero would require
its normalized strong factor to be 1: after cancelling positive Delta all
factors are integer units, and the strong norm cannot be −1 modulo 4. With
`f=D` and the main norm this would give `i²*c⁴=c²`, hence `i*c=1`,
impossible because `c>1`. This rules out a same-other-coordinates repair;
it does not establish unrestricted existential nonequivalence.

The checker verifies graph/source pin and liveness, all finite scalar
identities and residue checks. It does not expand the Pell/binomial witness
or independently establish the unbounded recurrence/floor arguments.

```
python3 -I -S -B research/current14-carrier64-free-s-toy-zero/check.py > /tmp/free-s-toy.json
cmp /tmp/free-s-toy.json research/current14-carrier64-free-s-toy-zero/result.json
```

Independent external review is recorded in
`../../reviews/current14-carrier64-free-s-toy-zero-independent/`.
