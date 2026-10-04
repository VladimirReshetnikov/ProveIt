# Prime main indices refute the free-coefficient 83 candidate

**Refuted candidate on its inherited compiler recipe.** The unchanged
[free-coefficient 83 source](complete83_free_coefficient_scout.md), with
46M+37A operations, 18 positive witnesses and exact degree 111, has infinitely
many full positive zeros at every positive ordinary input on every valid
fixed-program slice. This closes its previously open ordinary-input
soundness question. The established universal bound remains 84. No claim is
made about unrelated coefficient recipes or other 83-operation circuits.

The construction preserves the original positive outer slack, makes the
computed input root positive, and gives all six intended unscaled factors
value one. The scaled strong factor is Delta. It therefore does not rely
on the previously observed nonunit divisor cases. The missing divisibility
of the supplied auxiliary coefficient permits a prime main index unrelated
to the packed index. Prime equidistribution is an explicit existence
dependency; finite checks do not establish that theorem or materialize the
astronomical complete zeros.

## 1. The actual source and fixed compiler interface

The complete 83-row source is unchanged. Its free S replaces only the
parent's computed `i*Delta*c^2`. The retained definitions include

```
q=(B-1)J+1, X=w*q, Y=s*q^3, E=X*Y,
k=eta+zeta, c=k*Y+eta,
a=Y*(X+1), A=a+2, Delta=A^2-1, H=4a+3,
C=q-F-Z-alpha-2d*x, W=C-Z,
kappa=2d*x+b+delta*Delta,
Dmain=X+a*c+(rho+sigma)*H,
mu=W+a*kappa+rho*H,
R=(q*(q-F)-Z)*(q^2-1)+(MC+q*MF_source)*J,
Ni=k-h*E-R,
Nt=(K0+w)*C+(q-F)-transport_quotient*(q-1),
V=c*(T*f-1)-R*f^2,
Na=S^2*(V^2-y_aux^2)+y_aux^2,
Ns_scaled=Delta*f^2-S^2.
```

Here A is the mathematical Pell base; the literal source register `A`
means Delta. `K0=DC+B*DR` and `MF_source=MF_native+B-1` are unchanged fixed
compiler numerals. On every inherited slice, d and b are positive powers
of five, B=2^d>=16, MC is positive even, and
`0<MC,MF_native<B-1`. These full compiler constants are fixed before x
or any witness is chosen. The proof changes none of their recipes.

The output is the paid product of first, main, input, auxiliary, index,
transport and scaled-strong factors, minus Delta. All source rows, ports,
counts and degree are inherited from the authenticated complete83 packet;
no multiplication, loader, comparison or finalizer is suppressed here.

## 2. A positive outer tuple with X=q

Fix any x>0 and define the finite integers

```
u=2d*x+b, W=2^u, Z=1, C=W+1, F=(K0+1)*C.
```

The exponent u is odd and at least three. Choose a power of five N so
large that, with Dwidth=d*N and q=B^N,

```
q>F+W+2d*x+2.
```

Now supply

```
J=(q-1)/(B-1), alpha=q-F-W-2d*x-2,
w=1, transport_quotient=1.
```

These are positive integers. The original bound computes exactly C=W+1,
and its original difference computes W. Since X=q, the sheared transport
factor is exactly one: `(K0+1)C=F` and
`Nt=F+q-F-(q-1)=1`.

The packed R is now fixed independently of s and of every Pell index.
It is positive, odd and less than q^4. To verify the upper bound with the
actual shifted mask, write

```
S_pack=q*F,
T_pack=MC*J+1+q*(MF_native*J-1),
R=(q^2-S_pack)*(q^2-1)+T_pack.
```

The mask ranges give `0<T_pack<q^2-1`; also `0<S_pack<q^2` and
`S_pack>=q`. More sharply, the integer bound `T_pack<=q^2-2` gives
`R<=q^4-q^3+q-2`, hence `0<R+1<q^4`. Oddness follows because q is even,
Z=1 and MC is even. Once Y=q^3*s with s>=1 is chosen, E=q^4*s and
`0<R+1<E`; hence n0=(R+1)/2 is strictly between zero and E/2.

## 3. A prime modulus making the main progression reduced

Dwidth is a power of five, so Dwidth=1 modulo four and q=2 modulo five.
It is also odd, so q=-1 modulo three. Consequently

```
Cprime=4*q^3*(q+1)/3
```

is an integer congruent to two modulo five. Restrict s to `s=1+5t`,
`t>=0`, and ask that

```
lprime=Cprime*s+1
```

be a prime greater than three. This is a coprime prime progression:
its first term Cprime+1 is coprime to Cprime and is three modulo five,
so it is coprime to the difference 5*Cprime. Dirichlet's theorem gives
arbitrarily large suitable primes. Fix any such s and lprime. Set

```
Y=q^3*s, a=Y*(q+1), A=a+2,
Delta=A^2-1, H=4a+3=3*lprime,
L=2*(lprime-1), m_progress=4*L.
```

Euler's theorem gives `2^L=1 (mod H)`. Moreover lprime=3 modulo five,
so five does not divide L. Since Dwidth is a power of five,

```
gcd(Dwidth,m_progress)=1.
```

Thus `p=Dwidth (mod m_progress)` is a reduced prime progression, not a
progression in which every term has an inherited common divisor. Every p
in it is one modulo four and obeys `2^p=q (mod H)`.

## 4. Positive input and main coordinates

For an integer base Bp>=2 use the exact Pell notation

```
chi_Bp(v)+psi_Bp(v)*sqrt(Bp^2-1)
    =(Bp+sqrt(Bp^2-1))^v.
```

Let `E_A(v)=chi_A(v)-(A-2)*psi_A(v)`. The elementary recurrence gives

```
E_A(v)=2^v+H*gamma_v,
gamma_0=gamma_1=0, gamma_2=1,
gamma_(v+1)=2A*gamma_v-gamma_(v-1)+2^(v-1).
```

For v>=2 the gamma sequence is positive and increasing, by induction.
Since u is odd and u>=3, choose

```
kappa=psi_A(u), delta=(kappa-u)/Delta, rho=gamma_u.
```

The odd-index binomial identity modulo Delta proves integrality of delta;
strict Pell growth proves delta>0. The literal computed input root is
`W+a*kappa+rho*H=chi_A(u)>0`, so its norm is one.

For a prime p in the reduced progression of Section 3, set

```
c=psi_A(p),
gamma=(chi_A(p)-a*c-q)/H,
sigma=gamma-rho.
```

The recurrence identity modulo H proves gamma integral. Since E_A(p)
grows without bound, sigma is positive on a sufficiently late tail.
The computed main root is then chi_A(p), and its norm is one. The main
c is odd because A is even and p is odd. We will additionally discard
the finitely many primes p<=max(Delta,R).

## 5. Prime equidistribution supplies the strict first/main ratio

Put P=2X*Y^2+1 with X=q, and define

```
lambda_A=A+sqrt(A^2-1), lambda_P=P+sqrt(P^2-1),
theta=log(lambda_A)/log(lambda_P),
beta=log(sqrt(P^2-1)/(2Y*sqrt(A^2-1)))/log(lambda_P),
h_ratio=log((Y+1)/Y)/log(lambda_P),
N0=E/2, n0=(R+1)/2.
```

As in the pinned outer-family proof, A<P<2A^2-1 gives
`1/2<theta<1`, and `0<h_ratio<1`. The number theta is irrational.
Indeed Delta is odd while

```
v2(P^2-1)=Dwidth+2*v2(Y)+2
```

is odd. The two discriminants therefore have distinct square classes.
If the logarithmic ratio were rational, a nontrivial positive power of
a displayed Pell unit would lie in both distinct quadratic fields and
hence in Q. Its conjugate is its inverse, so a positive rational power
with norm one would have to be one, a contradiction.

We use the classical Vinogradov theorem: for every irrational alpha,
alpha*p modulo one is uniformly distributed as p ranges over primes.
A precise modern primary-paper statement is the d=1 case of
[Caragea and Lee, Proposition 7](https://link.springer.com/article/10.1007/s43670-022-00031-9).
Only this qualitative theorem is needed, with no effective error bound.

For completeness, its extension to a fixed reduced prime progression
follows from a finite Fourier filter and the prime number theorem in
arithmetic progressions. For a fixed nonzero integer h,

```
sum_(prime p<=z, p=r mod m) exp(2pi*i*h*alpha*p)
 = (1/m) sum_(j=0..m-1) exp(-2pi*i*j*r/m)
        sum_(prime p<=z) exp(2pi*i*(h*alpha+j/m)*p).
```

Every h*alpha+j/m is irrational. Each inner sum is o(pi(z)) by
Vinogradov and Weyl's criterion. Since pi(z;m,r) is asymptotic to
pi(z)/phi(m) for fixed coprime r,m, dividing by the progression's prime
count gives zero. Weyl's criterion then proves uniform distribution
along that progression. The Fourier filter and the prime-count
normalization also appear in [Bhakta, Loughran, Rydin Myerson and
Nakahara, Section 3.5](https://arxiv.org/abs/2109.03746), specifically the
proof of Lemma 3.16 and the Siegel–Walfisz count on printed page 15.
Their additional elliptic-curve hypotheses and quantitative estimates are
not invoked here.

Apply this qualitative result to alpha=theta/N0 and the fixed reduced
progression p=Dwidth modulo m_progress. Infinitely many arbitrarily large
primes satisfy

```
p*theta+beta modulo N0
    in (n0+h_ratio/3, n0+2*h_ratio/3).
```

For each sufficiently late hit put n=floor(p*theta+beta). Then
`n=n0 (mod N0)`, n>0 and n<p<2n. With k=2psi_P(n), the exact identity

```
c/k = [sqrt(P^2-1)/(2sqrt(A^2-1))]
       *lambda_A^p/lambda_P^n
       *(1-lambda_A^(-2p))/(1-lambda_P^(-2n))
```

and the strict interior third of the interval give `kY<c<k(Y+1)` on a
sufficiently late tail. This is the pinned exact conjugate-error argument:
take both conjugate terms below 1/[12(Y+1)]. The new prime theorem
supplies the hits; the old error estimate supplies the strict inequalities.
An ordinary irrational-rotation argument alone would not justify hits
restricted to primes.

Supply

```
eta=c-kY, zeta=k*(Y+1)-c,
tau_root=chi_P(n), h=(k-R-1)/E.
```

They are positive on the chosen tail. Since P=1 modulo E,
`k=2n=R+1 (mod E)`, so h is integral and the index factor is one.
The first norm is one because
`(XY^2*k)*(XY^2*k+k)=(P^2-1)*psi_P(n)^2`.
All five retained outer factors are now one on the original positive
domain, with main index p>R.

## 6. Prime main index and the current auxiliary CRT

For any odd prime p not dividing Delta, the binomial theorem in
`F_p[t]/(t^2-Delta)` gives

```
(A+t)^p = A+Delta^((p-1)/2)*t,
psi_A(p)=Delta^((p-1)/2)=+1 or -1 modulo p.
```

Our p>Delta guarantees p does not divide Delta. Thus gcd(p,c)=1.
As c is odd, also gcd(c,8p)=1. This is exactly the compatibility missing
from a generic wrong-index family; it is proved here, not assumed.

Since p=1 modulo four, take the same strong data as the second branch
of the frozen free-coefficient construction:

```
f=chi_A(2p), bstrong=psi_A(2p)=2*chi_A(p)*c,
S=Delta*bstrong.
```

Then `Delta*f^2-S^2=Delta`, and f^2=1 modulo c. Choose the unique
positive representative ell_aux modulo 8pc satisfying

```
ell_aux=R modulo c, ell_aux=3p modulo 8p.
```

It exists by the just-proved coprimality and is three modulo four.
Define

```
V=chi_S(ell_aux)/S, y_aux=psi_S(ell_aux).
```

The quotient is a positive integer. The frozen odd quotient-polynomial
identity, with sign minus because ell_aux=3 modulo four, gives
`V=-ell_aux=-R (mod c)`, since c divides S. Modulo f, the Pell state
returns at index 8p, and
`psi_A(3p)=(2f+1)*c`. Since S^2=1-A^2 modulo f, the other quotient
identity gives `V=-c (mod f)`. The norm also gives gcd(c,f)=1.
Consequently

```
T=(V+c+R*f^2)/(c*f)
```

is a positive integer: the numerator vanishes modulo both coprime
factors c and f, and every summand is positive. This T is exactly the
supplied current `auxiliary_quotient`, since its literal V expression
recovers V. The auxiliary Pell norm is one.

All 18 supplied coordinates are now positive integers. In actual source
order the seven factors are `(1,1,1,1,1,1,Delta)`, and their complete
product minus Delta is zero. Infinitely many prime main-index hits give
infinitely many distinct tuples. The argument applies to every x>0 on
every unchanged valid compiler slice. In particular, the pinned
[empty-language compiler](complete75_weakened86_rejecting_compiler.md)
has false positive solutions at every positive input.

This conclusion is stronger than a failure of the literal inverse.
For clarity that inverse still fails: restoring the parent coordinate
would require `i=S/(Delta*c^2)=2*chi_A(p)/c`, which is not an integer
because c>1 is odd and coprime to chi_A(p). No positive parent-zero
theorem is applied to that nonintegral inverse.

## 7. Evidence and remaining boundaries

The accompanying [fresh helper](free_coefficient83_prime_outer_collapse.py)
and [receipt](free_coefficient83_prime_outer_collapse.json) read nine pinned
source/proof artifacts as data and execute no predecessor or archived
Python. The complete parent packet, including its historical open-soundness
metadata, is copied unchanged and explicitly labeled as historical. This
report supplies the new theorem; it changes no gate or coordinate domain.

The checker follows all 83 actual rows under the formal rational
specialization of Sections 1–2 and 6. Thirty-seven coefficient cuts prove
the outer ports, main/input roots, auxiliary quotient, all seven factors
and full output identity. Formal denominators are q^3, H, Delta, qY and cf;
they are nonzero in the positive construction above. Integrality and
positivity follow from that construction, not from formal cancellation.
The independently extracted seven-row finalizer is the product of the
seven factors minus Delta and vanishes at `(1,1,1,1,1,1,Delta)`. Every row
and supplied port is live; the recounted ledger is 46M+37A. The exact degree
111 is inherited from the identical pinned source certificate.

A small diagnostic outer host uses d=b=x=K0=1, q=32 and deliberately
noncompiler masks. It checks the original positive slack and transport
factor one. With s=6, its modulus prime is lprime=8,650,753. Exact trial
division also certifies the main prime p=42,095,320,498,181, which exceeds
Delta and R and belongs to the required reduced progression. Modular Pell
arithmetic checks the exponent return, Frobenius residue and auxiliary
CRT coprimality; its input Pell component is materialized. No strict
first/main ratio is claimed for this sampled p. This host is not a
materialized valid compiler instance or a full zero.

Separate bounded evidence checks 84 gamma-recurrence states, 43 Frobenius
cases and twelve auxiliary CRT cases. In the last group the main Pell
coordinates and scaled strong factor are exact, while the huge auxiliary
quotient is reduced modulo cf by computing chi_S(ell_aux) modulo Scf and
dividing the divisible representative by S. This retains both required
congruences without claiming to print V, y_aux, T or a complete source
zero. The auxiliary norm is checked modulo cf in these finite cases;
the exact norm-one theorem follows from the Pell definition above.

From any working directory, with only Python's standard library:

```sh
python3 /absolute/path/free_coefficient83_prime_outer_collapse.py \
  --root /absolute/path/native-stream-queue \
  --expect /absolute/path/free_coefficient83_prime_outer_collapse.json
```

The mutually exclusive `--output FILE` writes a receipt. Checks use
explicit exceptions and receipt comparison is recursively type-exact.
Fresh normal and optimized exact replays from `/` pass. These bounded
checks do not simulate prime equidistribution, substitute a finite prime
search for Dirichlet, or certify arbitrary compiler numerals from a small
diagnostic example. The infinite-existence dependencies remain explicit
in Section 5 and in the receipt.

The full source remains 83=46M+37A, 18 positive witnesses, exact degree111.
The new result refutes its intended compiler representation. It supplies
no lower arithmetic complexity and does not alter the sound84 theorem.
