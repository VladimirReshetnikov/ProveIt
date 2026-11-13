# A symbolic full zero of the independent-k child at the fixed compact ports

The exact [84-operation independent-k graph](../ordinary13-eta-zeta84-independent-k-candidate/candidate.json) has a **standard natural-number zero with `eta>k` at its fixed symbolic compact ports**. The witness is specified below by finite arithmetic and Pell recurrences; no huge numeral is expanded. This disproves the proposed pointwise forcing `k≥eta` for that graph and tuple. It does **not** determine whether the original parent graph has any zero, or whether a different witness-replacement map could preserve zero existence. No Lean proof, model lifting, iPRA theorem or conclusion about Con(ZFC) is asserted.

## Exact compact fixed point

Let

```
rho=2^67, N=67*8807=590069,
beta=rho^8807-1, q=beta+1=2^N,
K0=rho^42*beta+Kprime,
MC=lowNat, MF=beta+highNat.
```

The exact pinned kernel recipe and the separately checked bound give `0<Kprime<rho^5496=2^368232`. The checker independently evaluates every selector and mask digit **only modulo N**, reading the 943 ordered rows and 41 positions from the pinned Lean sources. It obtains

```
q=273473, beta=273472, Kprime=551654,
MC=428453, MF=347205                         (all modulo N).
```

Set `e=439547`, `F=Kprime+2^e`, `alpha=beta-F`, and

```
G=q²-1-q*F,
R=G*(q²-1)+MC+q*MF.
```

The modular values of `A=((q²-1-q*Kprime)*(q²-1)+MC+q*MF)` and `B=q*(q²-1)` are respectively 365222 and 460162, while `2^e mod N=55048`. Exact modular arithmetic gives

```
R ≡ A-B*2^e ≡ 439547 = e  (mod N).
```

The checker exhausts all e in `0..N-1` and finds this unique fixed point. Since `368232<e`, `e+1<N-1` and `Kprime<2^368232`, we have `0<F<beta`, hence `alpha>0` and `F+alpha=beta`. Also `q≥4N`, `G≥q-1` and the masks are natural, so `R-N>e`.

## Coordinates and first factor

Set

```
J=1, w=2^(R-N), s=1,
X=q*w=2^R, Y=q³, U=Y*q²=q⁵,
C=q-F-alpha=1,
z=(w-2^e)/beta, h=w+rho^42+z.
```

Because `R-N≡e (mod N)` and `R-N>e`, beta divides `w-2^e`, so z is natural and h>0. The actual first carrier is

```
B=C*(X+K0)-F = beta*h.
```

The low mask has `MC≡2 (mod 4)`; q is divisible by four and `G=q*(q-F)-1`, so `R≡3 (mod 4)`. Put `n=(R+1)/2≥14` and `M=X*Y²`. Define Pell pairs for multiplier `A≥2` by `(x₀,y₀)=(1,0)` and

```
x_(j+1)=A*x_j+(A²-1)*y_j,
y_(j+1)=x_j+A*y_j.
```

For `A=2M+1`, let `(tau,yFirst)` be the nth pair and set `k=2*yFirst`. Its norm and congruence yield

```
tau²=1+M*(M+1)*k²,
k=2n+4M*sFirst
```

for a natural `sFirst`. Let `ell=M*k` and define

```
rWitness=tau-ell-k+(k*beta+1)*h.
```

This is natural: `tau>ell`, and `(k*beta+1)*h≥k+1`. The graph's actual first root is exactly `Z=beta*tau`; its first residual A0 is zero.

## Main factor and `eta>k`

Let `a=Y*(X+1)`, `Delta=(a+2)²-1`, `H=3+4a`, and take the Rth Pell pair `(g,c)` for multiplier `a+2`. Define `eta=c-Y*k`. It is natural and exceeds k: for any Pell multiplier A, `y_j≤(2A)^(j-1)` and `y_j≥A^(j-1)` for j≥1. Thus

```
k≤2*(6*X*Y²)^(n-1),
c≥(X*Y)^(2n-2).
```

Since `X≥q`, `Y=q³`, `q≥24` and `n≥14`, the elementary inequality `q^(n-4)>4*6^(n-1)` gives `c>(Y+1)*k`. Hence `eta>k`.

The main Pell recurrence gives `g-a*c≡2^R=X (mod H)` and `g-a*c≥c>X`. Therefore

```
gamma=4*q²*w*sFirst+(g-X-a*c)/H
```

is natural. Here the factor w is essential: `M/U=q²*w`. Because `k-R-1=4M*sFirst`, the graph's literal main root is `Dstar=U*g`, and its main residual A1 is zero.

## Strong and auxiliary factors

The Pell matrix for multiplier `a+2` is invertible modulo `c²`; choose its least positive identity period hStrong, which exists and is at most `c⁸`. Let `(f,v)` be its hStrong-th pair. Then `f≥1`, `v>0`, `c² | v`, and `f²-1=Delta*v²`. Set

```
i=Delta*(v/c²), I=i*c²=Delta*v.
```

Then i>0 and the strong residual `I²-Delta*(f²-1)` is zero. For multiplier I, let `(xAux,yAux)` be the Rth Pell pair and set `V=xAux/I>0`. The odd-index recurrence and `R≡3 (mod 4)` give

```
V≡-c (mod f²),    V≡-R (mod c),    f²≡1 (mod c).
```

The exact odd-Chebyshev induction and CRT are detailed and independently reviewable in the [auxiliary discharge](../ordinary13-independent-k-fixed-slice-auxiliary-discharge/). They show

```
T=(V+f²*R+c)/(f²*c)
```

is a positive integer, and `V=f²*(T*c-R)-c`. The auxiliary Pell norm makes the literal auxiliary factor exactly +1.

In the candidate's 13-input order, the complete natural witness is

```
(1, F-1, alpha-1, f, i-1, T-1, w, 0,
 rWitness, eta, k, yAux, gamma).
```

The first and main residuals and the strong residual are zero, while the auxiliary factor is one. Therefore all four product factors equal +1 and the complete graph output is zero. Every quantity is a finite, explicitly defined natural integer, though the certificate never expands the enormous witness.

## Verification boundary

The checker pins all source bytes, reconstructs the compact residues by modular Horner evaluation and the exact selector formulas, checks the fixed point and the carrier/root/scaling polynomial identities, reproduces the prior kernel and auxiliary receipts, and runs small generalized-X Pell controls. The quantified Pell-growth, finite-matrix period, odd-Chebyshev induction and CRT arguments are the written mathematical proof; finite controls are not a substitute for them. The source recipes, polynomial identities and arithmetic proof still merit independent review. No Lean process, build, axiom audit, provider selection, physical-PDF binding or parent-zero claim is involved.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-independent-k-fixedpoint-full-zero/check.py | cmp - research/ordinary13-independent-k-fixedpoint-full-zero/receipt.json
```
