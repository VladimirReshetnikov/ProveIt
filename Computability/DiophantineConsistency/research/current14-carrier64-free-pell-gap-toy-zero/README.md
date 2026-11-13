# A toy-port obstruction after freeing the auxiliary Pell gap

At a positive zero of the maintained equation, the reviewed
`../current14-carrier65-positive-v/` lemma gives `V>0` and in fact `V>1`.
The auxiliary unit equation

```
S²*(V²−y²)+y²=1
```

then implies `y²>V²`, so `t=y²−V²` is a positive integer. Replacing the
positive input y by a positive input t and the auxiliary factor by

```
Na' = V² − (S²−1)*t
```

maps every maintained zero forward and saves one live binary gate: 64 versus
65. A reverse map needs `V²+t` to be a square. The construction below gives
a symbolic positive candidate zero at the toy ports
`beta=31,K=9,MC=14,MF=46` for which it is not a square. It rules out the
natural same-other-coordinates repair, not unrestricted existential
nonequivalence. These are not the current ports; no Lean/PDF result is
claimed. This proof is submitted for independent review.

## Scalar, first and main factors

Use the scalar and first/main Pell coordinates from
`../current14-carrier64-free-s-toy-zero/`: `q=32`, `J=1`, `F=1`,
`alpha=14`, `C=17`, `gap=975`, `R=998911`, `X=2^R`,
`w=2^(R−5)`, and

```
N=(R−1)/2,
Y=(1/2)*sum_{j=0}^N binom(2N,j)*X^(N−j),
s=Y/q³, E=X*Y, h=E*Y, a=E+Y, A=a+2,
Delta=A²−1, H=4*a+3,
k=2*psi_(2h+1)(N+1), tau=chi_(2h+1)(N+1),
c=psi_A(R), D=chi_A(R),
eta=c−Y*k, zeta=k−eta, n=(tau−k+R)/E,
gamma=(D−X−a*c)/H,
z=1+((K+w)*C−F)/31.
```

The independently reviewed scalar and binomial/Pell arguments in that
packet prove all these coordinates positive integers, with first, main and
transport factors 1. Here the trace recurrence convention is
`(u+sqrt(u²−1))^j=chi_u(j)+psi_u(j)*sqrt(u²−1)`.

Choose an **even** positive power `f+L*sqrt(Delta)` of
`D+c*sqrt(Delta)` whose ordinate L is divisible by c². A positive unit order
in the finite quadratic ring modulo c², doubled if necessary, supplies one.
Put `i=L/c²>0` and `S=Delta*L`. The strong norm is 1. As `D=chi_A(R)`
and R is odd, this is an even-index power of `A+sqrt(Delta)`; hence
`f=±1 mod A` and `gcd(A,f)=1`. Also `f²=1 mod c` and
`S²=−Delta mod f²`.

## CRT selection and the nonsquare

Let `Daux=S²−1`. The three positive moduli `Daux`, `c`, and `f²` are
pairwise coprime: `c|S`, `f²=1 mod c`, and
`Daux=−(Delta+1)=−A² mod f²`, while `gcd(A,f)=1`. CRT therefore gives an
infinite arithmetic progression of positive V satisfying

```
V = 1 mod Daux,   V = −R mod c,   V = −c mod f².
```

Choose V>1 in this progression and set

```
t=(V²−1)/Daux,
T=(V+c+f²*R)/(c*f²).
```

Both are positive integers, the literal `V=f²*(c*T−R)−c` holds, and
`Na'=1`. The strong, first, main and transport factors are also 1, giving a
candidate zero.

There is a choice in that progression for which `V²+t` is not a square.
Indeed if `V²+t=y²`, then `(S*V)²−(S²−1)y²=1`. The positive solutions
are powers of `S+sqrt(S²−1)`, so the number of their V coordinates below a
bound grows only logarithmically; the CRT progression has positive linear
density. Choose the least sufficiently positive progression element not
among those Pell coordinates. This defines V and t without expanding the
enormous values. At the resulting candidate zero no positive original y
with the other coordinates fixed can have `y²=V²+t`.

The finite checker pins the original source, verifies the one-gate edit,
port scalar/valuation data, and an independent small even-Pell-power
gcd/divisibility control. It does not enumerate the huge symbolic witness,
prove the unbounded density argument, invoke Lean or establish a current-port
result.

```
python3 -I -S -B research/current14-carrier64-free-pell-gap-toy-zero/check.py > /tmp/free-pell-gap-toy.json
cmp /tmp/free-pell-gap-toy.json research/current14-carrier64-free-pell-gap-toy-zero/result.json
```

Independent external review is recorded in
`../../reviews/current14-carrier64-free-pell-gap-toy-zero-independent/`.
That review reconstructs the exact pre-status-edit bytes of the inherited
free-S README when checking its earlier audit pin.
