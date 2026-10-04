# Supplying the first Pell coefficient destroys the current upper ratio bound

The complete source in the [receipt](complete83_upper_ratio_deletion_collapse.json) costs **83=47M+36A**, with **18 positive witnesses and uniform exact degree 187**. It deletes the addition `R10b=eta+zeta` from the actual [scaled-strong84 source](complete84_scaled_strong_output.md) and supplies its value k as a positive coordinate instead of zeta. Every other factor producer and finalizer row is retained.

This candidate is **refuted on every inherited valid fixed-program slice**: every positive ordinary input has a full positive integer zero. The constructed inverse zeta=k−eta is strictly negative. Thus the deleted positivity condition is not implied by the retained factors, even with the original outer slack, normalized strong equation, asymmetric scale, shared input projection and auxiliary quotient present. The established universal bound remains 84.

The mechanism is not new: [the historical first-norm ratio obstruction](complete75_first_norm_ratio_obstruction.md) already proves an all-input collapse after a different gap-root recoding removes the upper ratio. That packet's 87-row source has different scale, strong and auxiliary interfaces. The contribution here is the literal one-row current84 deletion, its complete source identity and a full positive transfer to these current interfaces. The factorial outer construction is adapted from [the current80 first-index deletion proof](complete80_first_index_deletion_collapse.md); unlike that candidate, this one retains the first-index factor and makes it +1. No predecessor program is executed.

## 1. Exact source map and the missing inequality

Use the actual register meanings

```
q=(B−1)J+1, X=wq, Y=sq³, E=XY,
k=R10b=eta+zeta, c=R10a=kY+eta,
a=Y(X+1), A_math=a+2, Delta=A_math²−1,
H=4a+3, D=X+ac+(rho+sigma)H.
```

The source register named `A` is Delta, not A_math. In the parent, zeta has exactly one consumer, `R10b`; eta is consumed by `R10b` and `R10a`. Delete the first of these rows, replace every use of `R10b` by the new supplied `first_pell_coefficient`, and replace zeta by that coordinate in the supplied list. The unchanged multiplication `ksn2=kY` remains paid and is used by both first and main blocks.

All 83 rows and all 25 free ports, including the six fixed numerals and ordinary x, are live. Over every commutative ring,

```
F83(k,eta,others)=F84(zeta=k−eta,eta,others).       (1)
```

The only local identity needed is eta+(k−eta)=k; all other rows match literally after this cut, including all seven factors and the final subtraction of Delta. The inverse homogeneous linear change is k=eta+zeta. It is invertible on the whole polynomial ring and preserves total degree on every fixed numeral slice. Hence the parent's uniform exact degree 187 transfers; the gate-propagated upper bound remains 197. No numerical degree specialization is used to infer uniformity.

On positive tuples the inverse exists exactly when k>eta. Equivalently, the old domain imposes

```
kY<c<k(Y+1),
```

whereas the new domain imposes only c>kY. Every parent positive zero maps forward, but the new positive orthant has additional tuples. The proof below supplies full zeros among those tuples, with genuine unchanged compiler numerals and every positive ordinary input.

## 2. Fixed compiler and a positive outer tuple

Fix an authentic inherited compiler and any positive integer x. Its actual six numeral ports are

```
Bm1=B−1, Kconstant=K, twice_cell_bits=ell=2d,
inner_bits=b, MC, MF=MF0+B−1,
B=2^d, 0<MC,MF0<B−1, MC=2 mod4, b positive odd.
```

All further recipe conditions remain satisfied because no numeral is changed. In particular the native bound applies to MF0, not the shifted source port MF. Put I=ell*x+b and W=2^I; genuine recipes give I≥3.

Choose an integer L≥max(16,d,K,W,ell*x). Define

```
t=L!, q=2^t=B^(t/d), J=(q−1)/(B−1),
t=2^a2*m with m odd, Q=q²−1,
M=(MC+q*MF)J.
```

Here d divides t, t≥64 and a2≥4. The factorial argument gives q=1 modulo m: for every odd prime power r^v dividing t, both r^(v−1) and r−1 divide t and are coprime, so their product phi(r^v) divides t. Euler's theorem at each such prime power proves the congruence. This is an existence construction, not a paid factorial, factorization or exponentiation in the emitted polynomial.

Let e0 be the residue of M modulo m in [0,m). Exactly one of e0,e0+m,e0+2m,e0+3m is 3 modulo 4; call it e. Then

```
3≤e<4m≤t/4.
```

Choose Z to be the least positive residue of e−M modulo 2^a2 and set

```
C=W+Z, F=(K+2^e)C,
alpha=q−F−2Z−W−ell*x,
R=(q²−Z−qF)(q²−1)+M.                            (2)
```

Since J=1 modulo 4, M=2 modulo 4 and Z=1 modulo 4. In particular Z>0; also Z≤t and C≤2t. The exact bound used in the current80 proof applies without its extra divisibility-by-55 requirement:

```
F+2Z+W+ell*x ≤ 2t²+2t*2^(t/4)+4t < 2^t.
```

For t≥64, t≤2^(t/8) bounds the first and last terms together by 2^(t/2), and the middle term by 2^(t/2); their sum is less than 2^t. Therefore alpha>0 and F+Z<q. With G=q²−Z−qF,

```
2q−1≤G≤q²−q−1,   0<M<(q−1)(1+2q),
(2q−1)(q²−1)<R<q⁴−q³.                          (3)
```

Modulo m, q=1 gives R=M=e. Modulo 2^a2, q=0 gives R=Z+M=e. Thus

```
R=e mod t, R=3 mod4, R>q>5t+5, R>I.             (4)
```

This is the actual computed R, not an independent index port. The factorial parameter can be enlarged indefinitely. No decoded accepting history or optional canonical power-of-five padding is assumed: these are counterexample tuples of the relaxed polynomial.

## 3. Retained first and main norms, with the upper ratio violated

Set

```
X=2^R, w=2^(R−t), Y=q³, s=1, E=XY,
a=Y(X+1), A_math=a+2, Delta=A_math²−1, H=4a+3,
P=2XY²+1, n=(R+1)/2,
D=chi_A_math(R), c=psi_A_math(R),
tau_root=chi_P(n), k=2psi_P(n).
```

The Pell sequences are defined by
chi_A(j)+psi_A(j)sqrt(A²−1)=(A+sqrt(A²−1))^j.
These give the actual first and main factors equal to one:

```
tau_root²−XY²(XY²+1)k²=1,
D²−Delta*c²=1.
```

The factor of two in k is retained. Since P=1 modulo E, the recurrence gives psi_P(n)=n modulo E. Therefore

```
h=(k−R−1)/E
```

is an integer. It is strictly positive because psi_P(n)>n for n≥2, so k>R+1. Hence the actual retained index factor k−hE−R is +1.

Define eta=c−kY. To prove its positivity and the failed inverse without using either ratio conclusion, use the elementary Pell bounds

```
psi_A_math(R)≥(2A_math−1)^(R−1),
psi_P(n)≤(2P)^(n−1).
```

The exact identity

```
(2A_math−1)²−2PX
 =4Y²(2X+1)+12Y(X+1)+9−2X >0
```

holds for X,Y≥1. Since R−1=2(n−1),

```
c/k > X^(n−1)/2 ≥ X/2 > Y+1.                   (5)
```

The last inequality follows from R>5t+5, X=2^R and Y=2^(3t). Thus eta>k>0, and the unique restored zeta=k−eta is strictly negative. The supplied k and eta themselves are both positive.

## 4. The actual input and sheared transport

Let g_j=(chi_A_math(j)−a psi_A_math(j)−2^j)/H. Direct recurrence gives

```
g_0=g_1=0, g_2=1,
g_(j+2)=2A_math*g_(j+1)−g_j+2^j.
```

Thus every g_j is an integer, and g_(j+1)>g_j≥0 for j≥1. Since I is odd and 3≤I<R, set

```
kappa=psi_A_math(I), mu=chi_A_math(I),
delta=(kappa−I)/Delta, rho=g_I, sigma=g_R−g_I.
```

The Pell recurrence modulo Delta gives psi_A_math(I)=I modulo Delta for odd I. Growth gives delta>0, and the displayed recurrence gives rho,sigma>0. Consequently the actual source roots are

```
D=X+ac+(rho+sigma)H,
index_rhs=I+delta*Delta=kappa,
exponent_rhs=W+a*kappa+rho*H=mu.
```

The input factor is one. Substitution in the original outer definitions gives `marked_rhs=C` and the computed marker W=2^I; no outer slack was removed or made signed.

By (4), w=2^(R−t)=2^e modulo q−1, with R−t>e. Hence

```
transport_quotient=1+C*(w−2^e)/(q−1)
```

is a positive integer, and the literal current transport factor is

```
(K+w)C+q−F−transport_quotient*(q−1)=1.
```

This uses the paid asymmetric w consumer, not the historical X consumer.

## 5. The retained normalized strong and Bezout auxiliary block

At the new A_math,c,R put

```
m_aux=2cR, f=chi_A_math(m_aux), v=psi_A_math(m_aux),
i=v/c², S=Delta*v,
y_aux=psi_S(R), V=chi_S(R)/S.
```

Expanding (D+c sqrt(Delta))^(2c) proves c² divides v: the linear odd term contains 2c², and all later odd terms contain at least c³. Thus i is a positive integer and S=i Delta c². The Pell identity gives

```
S²=Delta*(f²−1).
```

For odd R=2r+1, the integer odd-quotient polynomial Q_r satisfies

```
chi_S(R)/S=Q_r(S²),
Q_r(0)=(-1)^r R,
Q_r(1−A_math²)=(-1)^r psi_A_math(R).
```

Here r is odd by R=3 modulo 4. Since S is divisible by c, and S²=−Delta modulo f, these identities give

```
V=−R mod c, V=−c mod f.
```

Also f²=1 modulo c, so gcd(c,f)=1. The positive integer numerator V+c+R f² is divisible by c and by f. Supply the positive integer

```
T=(V+c+R f²)/(cf)
```

as `auxiliary_quotient`. Then all literal auxiliary expressions have their intended values:

```
c(Tf−1)−Rf²=V,
aux_coefficient_root=i*Delta*c²=S,
norm_strong=Delta*f²−S²=Delta,
norm_aux=S²(V²−y_aux²)+y_aux²=1.                  (6)
```

No free coefficient, independent product, extra witness or auxiliary sign premise is introduced. These are the current source's normalized and Bezout forms.

## 6. Full zero and evidence boundary

The complete new supplied witness tuple, in source order, is

```
J,F,alpha,transport_quotient,f,h,i,T,s,w,tau_root,
eta,k,y_aux,Z,delta,rho,sigma.
```

All eighteen coordinates are strictly positive integers. The six fixed numerals and original positive x are unchanged. The seven complete factors, in their saved order, are

```
[1,1,1,1,1,1,Delta].
```

Their product minus Delta is zero. This is a full parametric-zero theorem, not only a native subsystem or inverse failure at an accepted input. The input projection is all positive integers for every inherited valid compiler slice. In particular the empty-set compiler has false positives. The valid parent excludes these tuples precisely through the lost upper ratio; no parent theorem is invoked on the negative restored zeta.

The [fresh helper](complete83_upper_ratio_deletion_collapse.py) pins eight source/proof dependencies and emits the full 83-row source. It checks the only deleted producer, every consumer substitution, all port/row liveness, the whole polynomial pullback at 40 signed assignments including 20 rational assignments, and 3,320 retained-row equalities. Ten small main/first/index cases check the strict inverse failure and retained h integrality; seven isolated normalized auxiliary completions materialize all their integers and verify (6); twenty-one factorial congruences check the elementary outer component. These examples are explicitly components, not genuine compiler exports, complete source zeros or computed accepting histories. No astronomical full tuple is materialized. The universal quantifiers follow from Sections 2–6, not from the finite examples.

From any working directory the bounded CLI is

```
python3 complete83_upper_ratio_deletion_collapse.py --root ABS_WIP --expect ABS_JSON
python3 -O complete83_upper_ratio_deletion_collapse.py --root ABS_WIP --expect ABS_JSON
```

Use `--output FILE` only for a new receipt. The helper uses explicit exceptions, authenticates predecessor bytes without executing them, and compares JSON recursively with exact types. Fresh normal and optimized receipt replays from `/` passed. This packet establishes no circuit lower bound and does not resolve the distinct independent-gamma83 chart.
