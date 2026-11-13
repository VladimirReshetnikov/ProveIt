# A toy-port zero after freeing U=cT−R

On every positive maintained-equation zero, the reviewed
`../current14-carrier65-positive-v/` argument gives `c>2R` and
`f²>c`. Since `V=f²*(c*T−R)−c>0`, it follows that `U=c*T−R` is a
positive integer. Replacing the positive input T by a positive input U and
setting `V=f²*U−c` therefore maps maintained zeros forward, deleting the
`cT` and `cTminusR` gates: **63 live gates instead of 65**.

The reverse map requires `c | U+R`. The symbolic construction below gives a
full positive zero of the 63-gate candidate with `c ∤ U+R` at the toy ports

```
beta=31, K=9, MC=14, MF=46.
```

They meet `beta>=31`, `K>0` and `0<MC<beta<MF<2beta`, but differ from the
current four ports. It rules out restoring a positive original T with the
other coordinates fixed; it does not prove unrestricted existential
nonequivalence or a current-port zero. All huge Pell values are symbolic and
unexpanded. This construction is submitted for independent review; no Lean
or PDF binding is claimed.

## Scalars and first/main Pell units

Use the scalar, binomial and first/main Pell coordinates of the reviewed
`../current14-carrier64-free-s-toy-zero/` packet:

```
q=32, J=1, F=1, alpha=14, C=17, gap=975,
R=998911, X=2^R, w=2^(R−5), N=(R−1)/2,
Y=(1/2)*sum_{j=0}^N binom(2N,j)*X^(N−j),
s=Y/q³, E=X*Y, h=E*Y, a=E+Y, A=a+2,
H=4*a+3, Delta=A²−1,
k=2*psi_(2h+1)(N+1), tau=chi_(2h+1)(N+1),
c=psi_A(R), D=chi_A(R),
eta=c−Y*k, zeta=k−eta, n=(tau−k+R)/E,
gamma=(D−X−a*c)/H,
z=1+((K+w)*C−F)/31.
```

The inherited proof supplies all these as positive integers, first/main and
transport factors 1 and `R=3 mod 4`. The elementary recurrence with
`A>=3` and `R>=3` gives `c=psi_A(R)>2R`. Its source/audit provenance
and later status-only README edit remain as recorded in the independent
review. Here `(u+sqrt(u²−1))^j=chi_u(j)+psi_u(j)*sqrt(u²−1)`.

Set the positive strong unit to the c-th power of the main unit:

```
f+L*sqrt(Delta) = (D+c*sqrt(Delta))^c,
i=L/c²,  S=Delta*L,  m=R*c,  Q=f/D.
```

The binomial expansion gives `c²|L`; f and L are positive and the strong
norm equals 1. Since A is even and R is odd, D is even and c is odd. An odd
Chebyshev trace is divisible by its even base with odd quotient, so Q is a
positive odd integer. Also `f=chi_A(m)` and `L=psi_A(m)`.

## Auxiliary anti-period and the missing divisibility

Put

```
t=2*m*Q−R,  j=(t−1)/2,
V=chi_S(t)/S,  y=psi_S(t),  U=(V+c)/f².
```

The index t is positive and `t=3 mod 4`; V and y are positive integers.
The auxiliary Pell factor is 1. We prove U integral, while `U+R` is not
multiple of c.

Let `u=A+sqrt(Delta)`. Modulo f², the strong unit identity gives

```
u^(2m) = −1 + 2*f*L*sqrt(Delta).
```

As Q is odd, raising to Q and multiplying by `u^(−R)=D−c*sqrt(Delta)`
shows

```
psi_A(t) = c + 2*Q*f*L*D = c mod f²,
```

because `Q*D=f`. Since `S²=−Delta mod f²`, the reviewed odd-Chebyshev
identity gives `V=(-1)^j*psi_A(t)=−c mod f²`. Thus U is a positive
integer and the candidate's literal value is exactly `f²*U−c=V`.

On the other hand `c|S`, so `V=(-1)^j*t=−t mod c`; because `m=R*c`,
`t=−R mod c`. Hence

```
V=R mod c,  U=R mod c,  U+R=2R mod c.
```

The second congruence uses `f²=1 mod c`. Since `0<2R<c`, the last residue
is nonzero. All five normalized factors are 1, so the 63-gate candidate
vanishes. If an original zero with the other coordinates fixed existed, its
auxiliary unit equation and the fixed y,S would give `V_old²=V²`. The
reviewed maintained-zero lemma gives `V_old>0`, and the constructed V is
positive, so `V_old=V`. Then `c*T−R=U`, contradicting the nondivisibility.
Thus neither sign of the original trace permits a same-other-coordinates
repair.

The checker pins the source, verifies both deleted gates and 63-gate
liveness, reproduces the finite toy scalar data, and independently tests
the anti-period congruences using `A=4,R=3,c=63` via exact modular matrix
exponentiation. It does not expand the enormous full witness or prove the
inherited unbounded Pell/floor facts.

```
python3 -I -S -B research/current14-carrier63-free-u-toy-zero/check.py > /tmp/free-u-toy.json
cmp /tmp/free-u-toy.json research/current14-carrier63-free-u-toy-zero/result.json
```

Independent external review is recorded in
`../../reviews/current14-carrier63-free-u-toy-zero-independent/`. It
reconstructs the earlier status-only README bytes when checking inherited
review pins; the same-coordinate conclusion above uses the separately
audited maintained-zero positive-V lemma.
