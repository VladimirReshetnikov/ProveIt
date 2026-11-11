# A shifted-carrier obstruction in the 13-variable family

This note investigates a **different fixed-port family**, the independently
reviewed 13-positive-variable, 69-operation equation at the complete 2471
tuple. It is not the maintained 2011-port 65-operation equation. Replacing
`m−V²*G` by a new positive input `mu` removes two gates, producing a 67-gate
candidate. The symbolic construction below is an independently reviewed positive zero of
that candidate with `G<0`. It invalidates the natural reverse map to
the 69-gate equation, whose proof establishes `G>=0` at every positive zero.
It does not establish unrestricted existential nonequivalence or a Lean
result. Huge integers below are symbolic; the finite checker does not expand
the witness or establish the unbounded Pell claims.

The 69-gate source defines `G=(K+w)*C−F`, `b=beta*J`, and

```
y = 1 + 4 * (b * (m−V²*G) − G).
```

Delete `LB=V²*G` and `mLB=m−LB`, and replace the use of `mLB` by positive
`mu`. The remaining `V²` gate stays live. The shifted candidate has
`y=1+4*(b*mu−G)`, 13 positive inputs and 67 live operations. If `G>=0`,
`m=mu+V²*G` is positive and restores the old formula; the issue is whether
`G>=0` must hold. The old proof uses the original `V²*G` term to prove it,
so it does not directly apply to the shifted candidate.

## Fixed scalar data

Use the exact 2471 bytes pinned by `polynomial69.json`. Put

```
b = beta = 2^B−1,  B=116137,  J=1,  q=b+1,
M = MC + q*MF,  gap=M+1,  R=gap*q²−1,
N=(R−1)/2,  w=2^(R−B).
```

The finite check proves `R=gap*(q²−1)+M`, `R=3 mod 4`, and
`popcount(N)−1=3B`. Let `e=(R−B) mod B` and
`mbar=(K+2^e) mod b`. The checker finds `e=40107` and
`gcd(mbar+1,b)=1`. Define the least nonnegative residue

```
F = mbar*(1−gap)*inverse(mbar+1) mod b,
```

using `F=b` if that residue is 0. Set

```
C=q*(q−F)−gap,  alpha=q−F−C,
G=(K+w)*C−F.
```

Since `MF>beta`, `gap>q²`; hence `C<0`, `G<0`, and `alpha>0`.
The modular equation gives `b|G`. The checker verifies the exact fixed-port
arithmetic and the full small symbolic scalar relations without expanding
`w`. The positive residue F has 116134 bits and SHA-256
`3c062801d0cc3672ac9c9e68569fb5bfe5a9140d35e06c5c7a4db8c67b4687fc`
in minimal unsigned big-endian form.

## Symbolic Pell completion

The following invokes the previously independently reviewed general
first/main Pell construction, not a newly kernel-checked result. Set

```
X=2^R,
Y=(1/2)*sum_{j=0}^N binom(2N,j)*X^(N−j),
s=Y/q³, E=X*Y, h=E*Y, a=E+Y, H=4*a+3,
Delta=a²+H,
k=2*psi_(2h+1)(N+1), tau=chi_(2h+1)(N+1),
c=psi_(a+2)(R), D=chi_(a+2)(R),
eta=c−Y*k, zeta=k−eta, n=(tau−k+R)/E,
gamma=(D−X−a*c)/H.
```

Here `(u+sqrt(u²−1))^j=chi_u(j)+psi_u(j)*sqrt(u²−1)`.
The reviewed binomial valuation gives `v2(Y)=popcount(N)−1=3B`, so
`s` is a positive integer. The general floor and Pell congruence arguments
in `../current14-carrier64-current-full-zero/` give positive `eta,zeta,n,
gamma`, and first/main factors `N0=N1=1`. Those arguments use the displayed
`X,Y,R` and do not require the 2011 port tuple.

For the strong factor, let `f+L*sqrt(Delta)` be a positive power of
`D+c*sqrt(Delta)` whose ordinate `L` is divisible by `b*c²`. Such a power
exists because this norm-one element is invertible in the finite ring modulo
`b*c²`. Put `i=L/(b*c²)>0` and `S=b*i*Delta*c²=Delta*L`.
Then the strong factor equals 1 and `f²=1 mod c`.

Choose the order `h0` of the norm-one unit
`S+sqrt(S²−1)` in the finite quadratic ring modulo `S*c*f²`. For an
arbitrarily large positive integer `j` put

```
t=4*j*h0−R,  y=psi_S(t),  V=chi_S(t)/S.
```

Take j large enough that t is positive. Since R is 3 mod 4, t is 1 mod 4;
the odd-index Pell congruence gives `y=1 mod 4*S²`. The unit-order choice
gives `chi_S(t)=chi_S(R) mod S*c*f²`. For R=3 mod 4, the reviewed
Chebyshev identities give `V=−R mod c` and `V=−c mod f²`; the first uses
`c|S`, and the second uses `S²=−Delta mod f²` and
`psi_(a+2)(R)=c`. As `f²=1 mod c`,

```
T=(V+c+f²*R)/(c*f²)
```

is a positive integer and the literal V definition holds. The auxiliary
factor is 1 by the Pell identity. Finally set

```
mu=(y−1+4*G)/(4*b).
```

This is an integer because `y−1` is divisible by `4*S²`, `b|S`, and `b|G`.
As j grows, positive y grows without bound while G is fixed, so choose j
large enough that `mu>0`. The shifted literal y is exactly the chosen y.
All four normalized factors are 1, making the shifted 67-gate polynomial
zero while `G<0`.

## Scope and reproducibility

The 69-gate original has no positive zero with this same tuple of other
coordinates, since its reviewed soundness proof forces `G>=0`. The argument
does not decide whether the two equations each have some other zero, and it
does not apply to the maintained 2011-port expression as a proved theorem.
No display, PDF, native kernel or Lean binding is claimed. Independent external review is recorded in
`../../reviews/thirteen-variable67-shifted-m-obstruction-independent/`.

```
python3 -I -S -B research/thirteen-variable67-shifted-m-obstruction/check.py > /tmp/shifted-m-obstruction.json
cmp /tmp/shifted-m-obstruction.json research/thirteen-variable67-shifted-m-obstruction/result.json
```
