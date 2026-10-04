# The 82-operation square/product chart accepts every positive input

**Refuted candidate.** The unchanged [82-operation source](complete82_auxiliary_square_product_chart.md) has infinitely many full positive zeros at every positive ordinary input on every inherited valid fixed-program slice. This is a counterexample to that proposed universal representation, not merely a failure of its witness inverse. Its complete cost remains 82=45M+37A, with 18 positive witnesses and exact degree 185. The established universal bound remains 84.

The construction uses the original positive outer slack and has positive computed input root. All five retained factors are +1. It completes them with the proved positive auxiliary extension of the actual82 chart. No old weakened-bound tuple or negative-root construction is inserted into this source. The ordinary input and compiler numerals are never changed.

The [companion helper](complete82_all_input_outer_collapse.py) and [receipt](complete82_all_input_outer_collapse.json) save the entire unchanged source and bounded exact component evidence. They execute no predecessor or archived Python. The unbounded conclusion below is an existence proof, not a claim to materialize a full astronomical zero.

## 1. A fixed outer tuple for each ordinary input

Fix an inherited valid compiler and any integer x>0. Its six supplied numerals have their original meanings

```
B=2^d, ell=2d, b=inner_bits, K=DC+B*DR,
MC, MF_source=MF_native+B-1.
```

In particular d and b are positive powers of five, B>=16, MC is positive even, `0<MC,MF_native<B-1`, and `v2(MF_native)=2`. Put

```
u=2dx+b, W=2^u, C=W+1, Z=1, F=(K+1)*C.
```

These are fixed while choosing the period size. Choose an arbitrarily large power of five N such that

```
q=B^N > F+W+2dx+2.
```

Write `Dwidth=dN`, `J=(q-1)/(B-1)` and set the actual positive supplied coordinates

```
alpha=q-F-W-2dx-2,
transport_quotient=(q+1)*C+1,
w=q^2, s=1.
```

The literal original bound gives

```
q-F-Z-alpha-2dx=C=W+1>0,
C-Z=W>0,
X=wq=q^3, Y=sq^3=q^3, E=XY=q^6.
```

Both slacks remain positive; no coordinate is omitted. The actual sheared transport factor is exactly

```
(K+w)*C+(q-F)-transport_quotient*(q-1)=1,
```

because `(K+q²)C-F=(q²-1)C`.

The source's packed index is the fixed integer

```
R=(q*(q-F)-1)*(q^2-1)+(MC+q*MF_source)*J.
```

It is odd: q is even, Z=1, MC is even and J is odd. It is positive and less than q^4. For a direct check with the actual shifted mask convention, put

```
S'=qF,
T'=MC*J+1+q*(MF_native*J-1).
```

Then `0<S'<q²`, `0<T'<q²-1`, and
`R=(q²-S')(q²-1)+T'`. The strict F bound gives positivity, while `S'>=q` gives `R<q^4`. Consequently `0<R+1<E`.

## 2. A positive input norm at the actual input exponent

Put

```
a=Y*(X+1), A=a+2, Delta=A^2-1, H=4a+3=4A-5,
P=2X*Y^2+1.
```

The source register named `A` is Delta; capital A in this proof is the mathematical Pell base. For a base A>1 define

```
chi_A(v)+psi_A(v)*sqrt(Delta)=(A+sqrt(Delta))^v,
E_A(v)=chi_A(v)-a*psi_A(v).
```

The exact recurrence and initial values give `E_A(v)=2^v (mod H)`. A useful stronger form is the integer sequence

```
gamma_0=gamma_1=0, gamma_2=1,
gamma_(v+1)=2A*gamma_v-gamma_(v-1)+2^(v-1),
E_A(v)=2^v+H*gamma_v.
```

Induction makes gamma_v strictly positive and increasing for v>=2. Since u is odd and u>=3, set

```
kappa=psi_A(u),
delta=(kappa-u)/Delta>0,
rho=gamma_u>0.
```

The odd-index Pell binomial formula gives `psi_A(u)=u (mod Delta)`, and strict growth gives `psi_A(u)>u`; thus delta is a positive integer. The literal input-index register is exactly kappa and its computed root is

```
W+a*kappa+rho*H=chi_A(u)>0.
```

The input norm is therefore +1. No large unknown input index or input-period CRT is needed.

## 3. An unbounded main progression and strict first/main ratios

Set `e=3Dwidth`, so X=2^e and e is odd (indeed e=3 modulo4). H is odd; choose any positive return period L with `2^L=1 (mod H)`. Such an L exists by finiteness of the unit group modulo H. Let

```
p=e+4L*r, r=0,1,2,...,
c=psi_A(p),
gamma=(chi_A(p)-a*c-X)/H.
```

Each p is odd, c is odd, and gamma is an integer. Along a sufficiently late tail gamma exceeds the fixed rho: `E_A(p)=2psi_A(p)-psi_A(p-1)` grows without bound. Set the supplied positive integer `sigma=gamma-rho`. Then the actual main root is exactly `chi_A(p)` and its norm is +1.

We now enforce the retained first-index equation without identifying p with R. Put

```
lambda_A=A+sqrt(A^2-1), lambda_P=P+sqrt(P^2-1),
theta=log(lambda_A)/log(lambda_P),
beta=log(sqrt(P^2-1)/(2Y*sqrt(A^2-1)))/log(lambda_P),
h_ratio=log((Y+1)/Y)/log(lambda_P),
N0=E/2, n0=(R+1)/2.
```

Here `0<n0<N0`, `0<h_ratio<1`, and `1/2<theta<1`. The latter follows from `A<P<2A²-1`. The rotation step is irrational: A is even, so `A²-1` is odd, whereas

```
v2(P²-1)=v2(4X*Y²*(XY²+1))=9Dwidth+2
```

is odd. The two nonsquare discriminants have distinct square classes. A rational ratio of their logarithmic units would put a nontrivial positive power of one quadratic unit in the intersection of distinct quadratic fields, namely Q, which is impossible.

Thus along the progression p the values `p*theta+beta` modulo N0 enter the open interval

```
(n0+h_ratio/3, n0+2*h_ratio/3)
```

infinitely often, and arbitrarily late. At each sufficiently late hit take `n=floor(p*theta+beta)`. It is positive, satisfies `n=n0 (mod N0)`, and `n<p<2n` eventually. The exact conjugate-error estimate in the pinned [infinite outer-family proof](complete75_weakened86_infinite_outer_family.md), Section4, applies unchanged to this residue class. Explicitly, for

```
k=2psi_P(n), c=psi_A(p), rY=(Y+1)/Y,
R0=sqrt(P²-1)/(2sqrt(A²-1))*lambda_A^p/lambda_P^n,
```

the hit gives `Y*rY^(1/3)<R0<Y*rY^(2/3)` and

```
c/k=R0*(1-lambda_A^(-2p))/(1-lambda_P^(-2n)).
```

Once the two conjugate terms are less than `1/[12(Y+1)]`, both strict margins survive, proving `kY<c<k(Y+1)`. Irrational rotation visits every open interval in every tail, so the input positivity and error thresholds discard only finitely many hits.

Define the actual positive supplied fields

```
eta=c-kY, zeta=k*(Y+1)-c,
tau_root=chi_P(n), h=(k-R-1)/E.
```

The ratios make eta,zeta positive and recover exactly the source's `k=eta+zeta` and `c=kY+eta`. Since `P=1 (mod E)`, `psi_P(n)=n (mod E)`, so `k=R+1 (mod E)`; h is integral. On a sufficiently late tail k>R+1, hence h>0. The literal index factor is `k-hE-R=1`. Finally

```
(XY²k)*(XY²k+k)=(P²-1)*psi_P(n)²,
```

so the actual first norm is +1. All five retained factors are now +1 on the same positive tuple, with the original bound and correctly typed positive input root. Choose the tail also with p>R; the auxiliary rank conclusion p=R is expressly absent.

## 4. Complete positive auxiliary extension

Apply the exact82 projection theorem with i=1, the odd c above and the positive fixed R. Write

```
F_aux=Delta*c^4+1,
S_aux=Delta*c².
```

Choose a positive integer v_aux satisfying `v_aux=R (mod c)` and `v_aux=3 (mod4)`, possible because c is odd. Set

```
V=chi_(S_aux)(v_aux)/S_aux,
y_aux=psi_(S_aux)(v_aux),
U_aux=(V+R*F_aux)/c+1.
```

For odd v_aux the quotient V is integral. The odd quotient-polynomial constant gives `V=-v_aux=-R (mod c)`, while `F_aux=1 (mod c)`. Thus U_aux is integral and strictly positive, with

```
c*(U_aux-1)-R*F_aux=V.
```

Its Pell equation gives the literal auxiliary norm +1. The scaled strong factor is exactly Delta:

```
Delta*F_aux-(Delta*c²)²=Delta.
```

The source's seven factors are `(1,1,1,1,1,1,Delta)`, so its fully paid product minus Delta is zero. The refreshed witness names are `L16=F_aux` and `auxiliary_Tf=U_aux`; F_aux does not replace or alter the packing witness F.

Every one of the 18 supplied coordinates is positive. Infinitely many main-index hits give distinct c and therefore distinct full positive tuples at the same fixed ordinary x and unchanged compiler numerals. The theorem applies to every inherited valid fixed-program slice. In particular a compiled rejecting program has positive false-input zeros; its actual recipe is the already pinned [rejecting-compiler construction](complete75_weakened86_rejecting_compiler.md). This refutes the current82 representation without any assumption that nonintegral witness inversion implies false membership.

## 5. Scope and bounded verification

The source, counts and exact185 degree are inherited literally from the authenticated82 packet; this report changes no gate, coordinate domain, compiler numeral or polynomial. Its new result is the full all-input extension of one simple original-bound outer family. It proves no impossibility for unrelated82-operation circuits or coefficient recipes, and no conclusion about the free-S83 chart without that chart's separate auxiliary restrictions.

The helper authenticates the immediate82 source/receipt/proof trio and three proof dependencies, plus every dependency in that frozen parent receipt. It reads these files as inert data. It copies the complete82 source, verifies all supplied ports and gates are live, recounts 45M+37A, and retains the inherited exact-degree certificate. Only the new packet's soundness metadata changes.

Exact sparse coefficient checks cover nine actual outer ports, twelve ratio/root/norm/index/auxiliary/finalizer identities, and the input quotient recurrence. In particular the current sheared transport is +1, both scale outputs are q³, all source norm formulas match the stated Pell forms, and the complete seven-factor finalizer returns zero at `(1,1,1,1,1,1,Delta)`.

Five small fixtures at d=5,N=5 check the literal original outer bound, transport, packed R, positive input delta/rho and input norm, a separate positive main-norm component, and the first-index residue by modular Pell exponentiation. Their small K and masks are diagnostic values, not certified fixed-program numerals. They do not join the first/main ratio to the required index and are explicitly not full zeros. Six small even Pell bases independently check finite power returns, the positive quotient recurrence, odd input residues and main progressions. Nine small auxiliary blocks at A=2,3,5 verify the actual positive supplied F_aux,U_aux,y_aux and both auxiliary/strong factors, including CRT adjustment when R is not 3 modulo4.

No full compiler zero or huge rotation-hit index is materialized. The component calculations supplement the unbounded existence proof, rather than replace irrational rotation or its exact conjugate-error estimate. No prime-existence theorem is needed for this82 construction.

Only Python's standard library is needed, from any working directory:

```sh
python3 /absolute/path/complete82_all_input_outer_collapse.py \
  --root /absolute/path/native-stream-queue \
  --expect /absolute/path/complete82_all_input_outer_collapse.json
```

The mutually exclusive `--output FILE` writes a fresh receipt. Parsing rejects duplicate keys and nonfinite JSON values; receipt comparison is recursively type-exact, and all checks use explicit exceptions. This is a bounded research CLI, not a maintained general compiler API. Writer and fresh normal/optimized exact replays from `/` passed. Root read the complete helper and proof, and a separate reviewer challenged Sections1–4, with no requested correction. No repository or frozen predecessor file was changed.
