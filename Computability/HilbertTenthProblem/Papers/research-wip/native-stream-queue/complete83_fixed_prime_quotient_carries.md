# Fixed-prime quotient carries remove the odd-scale hypothesis on subsequences

This note proves an unconditional odd-scale completion theorem for the unchanged shared-projection83 source on every fixed original five-adic compiler slice. On explicit infinite subsequences, sufficiently large parameters admit positive outer and input coordinates with `A³ | Y`, where A is the odd part of q. The binary condition for the enlarged selector z remains open. A complete positive source zero is asserted only conditionally on that separate binary condition; no rejected input or universal83 conclusion follows.

The fixed-prime forcing idea and its aggregate-budget application were proposed by root. The present derivation checks the congruences, quantitative search and positive interval independently. Factorizations, CRT, powers and input searches describe mathematical coordinate choices, not unpaid circuit operations. No source row or supplied port is removed or changed.

## 1. Inherited source and exact linear depths

Fix one authentic original compiler and its fixed integers `B=2^d`, b, K, MC and source MF. In particular d is a positive power of five with d>=25. Retain the source-coupled family and notation

| Shape, selected once by K | q | A=odd(q) | T | ell=2dT | tau_p |
|---|---|---|---|---|---|
| plus, K!=3 modulo5 | Q(Q+1)/2 | Q+1 | n(D−1) | 2D(D−1) | v_p(D−1) |
| minus, K=3 modulo5 | Q(2Q−1) | 2Q−1 | n(D+1) | 2D(D+1) | v_p(D) |

Here `n=1 modulo4`, `D=dn`, `Q=B^n`, and p ranges over odd primes dividing A. The inherited family has `5` not dividing A and

```
Z=C=z, F=Kz, W=0,
A0=q²(q²−1)+(MC+qMF)J,
G0=(1+qK)(q²−1),
R(z)=A0−G0*z, r=(R−1)/2, J=(q−1)/(B−1).
```

Its fixed class `z=zeta modulo m0`, where `m0=4d` in the plus shape and `m0=4d/5` in the minus shape, forces z=1 modulo4 and R=b modulo2d. The same class also preserves the source's R=3 modulo4 property. For `p^a_p || A`, put

```
b_p=a_p+tau_p=v_p(2^ell−1),
g=product_(p|A) p^tau_p.
```

The equality for the period follows from odd-prime lifting applied to `2^(2D)−1` in the plus shape and `2^(D+1)−1` in the minus shape. It includes p=3. In particular `g<=D+1`, G0 is −1 modulo each p|A, and m0 is coprime to A.

We will arrange `v_p(r+1)=b_p` at every p|A, strengthen the quotient carries at a fixed finite subset of these primes, and then choose the ordinary input on its original period.

## 2. Subsequences with a large factor supported on fixed primes

In the plus shape choose

```
n=9^j, j>=1,
S={primes dividing B+1}.
```

Since d is odd, 3 belongs to S. Odd-prime lifting gives, for each p in S,

`a_p=v_p(B+1)+v_p(n)`.

No prime other than3 divides n. Therefore the complete S-supported part of A is exactly

```
A_S=product_(p in S) p^a_p=(B+1)n>Bn.             (1)
```

In the minus shape let `v=phi(d)` and choose

```
m=9^(v*j), j>=1,
n=((d+1)m−1)/d,
S={primes dividing 2B−1}.
```

The congruence m=1 modulo d makes n integral. Also m=1 modulo4 and d is odd, so n=1 modulo4. Here `D+1=(d+1)m` and

`A=2^(D+1)−1=(2B)^m−1`.

Again 3 belongs to S and odd-prime lifting gives

```
A_S=(2B−1)m.                                      (2)
```

We have m<=n. Moreover

`d*((2B−1)m−Bn)=(B(d−1)−d)m+B>0`,

so `A_S>Bn` also in this shape. Both subsequences are unbounded and retain n=1 modulo4. The fixed set S excludes5 in either shape because B=2 modulo5. Uniformly in the chosen shape,

```
Bn<A_S<=(2B−1)n.                                 (3)
```

S is fixed once the compiler and shape are fixed; the exponents a_p grow with the subsequence. No assertion that all primes of A are fixed is made.

## 3. Forcing carries while retaining the exact denominator depths

For p in S define

```
e_p=max(1,3a_p−b_p)=max(1,2a_p−tau_p).
```

Then `1<=e_p<=2a_p`. Impose

```
(r+1)/p^b_p = −1 modulo p^e_p,
equivalently R+1 = −2p^b_p modulo p^(b_p+e_p).    (4)
```

The factor2 in the second congruence is required by `r+1=(R+1)/2`. Equation(4) already forces the exact depth b_p, even if b_p>=3a_p. Once r is positive, its positive quotient `eta_p=(r+1)/p^b_p` has e_p trailing base-p digits equal to p−1. Addition of eta_p to itself therefore generates at least e_p carries.

Write `c_p=v_p(binomial(2r,r))`. For any positive r with r+1=p^b eta and p not dividing eta, the exact identity is

```
c_p=b+v_p(binomial(2eta,eta)).                    (5)
```

For example, it follows by combining the identity

`binomial(2N−2,N−1)=N*binomial(2N,N)/(2(2N−1))`

with `N=p^b eta` and the invariance of central-binomial valuation under multiplying eta by p^b (append zero base-p digits). Thus (4) yields

```
c_p>=b_p+e_p>=3a_p for p in S.                   (6)
```

This supplies extra carries in the quotient; it does not deepen b_p. The earlier obstruction to simultaneously forcing deep denominator resonances at all primes therefore does not apply to this construction.

Put

```
Cextra=product_(p in S) p^e_p <= A_S²,
A_out=A/A_S,
M=m0*A*g*Cextra.
```

Use CRT to choose the least positive z0<=M in the inherited m0 class, subject to (4) at S and `R(z0)+1=0 modulo p^b_p` at all p|A outside S. All primes of A are odd and different from5; G0 is a unit at them, so this CRT system has a unique class modulo M. R is odd in the class, and `Ag` divides `(R+1)/2`.

Along `z=z0+M*j`,

```
eta=(r+1)/(A*g)=eta0−(G0*m0*Cextra/2)*j.          (7)
```

The S congruences are preserved. The slope in(7) is a unit at every prime dividing A_out; it need not be a unit at S, and no such claim is used. Exact depths at the remaining primes are precisely `gcd(eta,A_out)=1`.

For any odd A_out with5 not dividing it, the elementary affine coprime-interval bound provides such a j in

```
0<=j<Lout, Lout=floor(sqrt(3A_out))+1.
```

Indeed inclusion-exclusion counts coprime values in L consecutive j as `L*phi(A_out)/A_out+error` with absolute error less than `2^omega(A_out)`. The prime-power factors give `phi(A_out)/2^omega(A_out)>=sqrt(A_out/3)`: every prime>=7 contributes at least1 after dividing by the square root, and the possible prime3 costs at most `1/sqrt(3)`. The case A_out=1 simply takes j=0. Hence

```
0<z<=Zmax=M*Lout,                                (8)
v_p(r+1)=b_p for every p|A.
```

The initial congruences can use signed R; its positivity is established independently by the following size bound before any positive-quotient carry argument is applied.

## 4. Enlarged representatives still have positive source slack

Using A<2Q, g<=D+1<=(d+1)n, m0<=4d, (3) and Cextra<=A_S², we get

```
Zmax <= 8d(d+1)(2B−1)² n³ Q*(floor(sqrt(6Q))+1)
      = Zbound.                                  (9)
```

Every sufficiently large parameter in the relevant subsequence satisfies the explicit finite inequality

```
(K+2)*Zbound+2d*(5n+T)<q/2.                       (10)
```

Indeed its left side is `O(n³ Q^(3/2))+O(n²)` for a fixed compiler, whereas `q>=Q²/2`. Exponential growth of Q=B^n proves eventual validity even on the sparse minus subsequence. The upper bound uses only integer arithmetic and an integer square root; it provides a terminating search for a parameter satisfying(10). Eventual validity follows from the dominance argument, not from treating the first passing parameter as an independently certified threshold. This is not a circuit cost assertion.

Choose z as in(8), and take x0 in `[5n,5n+T−1]` representing `(R−b)/(2d)` modulo T. Define

```
S0=q−(K+2)z−2dx0,
x(k)=x0+kT, u(k)=2dx(k)+b,
alpha(k)=S0−ell*k.
```

By(10), S0>q/2. The exact positive interval is `0<=k<=floor((S0−1)/ell)`. All members have the original literal outer/source relations, positive x and alpha, and the unchanged packing satisfies

```
3q+1<R<q^4−q^3, 0<u(k)<2q<R, u(k)>=10D+b,
R−u(k)=0 modulo ell,
X(k)=2^R−2^u(k)>0, q(q−1)|X(k).
```

These are the larger-z bounds proved in the accepted source-coupled theorem. For clarity, its lower index estimate uses the identity

`q²−z−qF=q*(2z+alpha+2dx)−z>3q`;

the upper estimate uses positive F,z and the fixed authentic mask bounds, not z<=4d. Thus neither the index domain nor positivity is being borrowed from the old small-z construction. The transport witness stays `1+z*(X(k)/q)/(q−1)>0`. Now R and r are positive, so (5)–(6) apply.

## 5. The entire remaining odd-scale CRT fits

At every p|A outside S, the exact depth and(5) at least give `c_p>=b_p>=a_p`; at S we have (6). Consequently the exact required input modulus obeys

```
Hreq=product_(p|A) p^max(3a_p−c_p,0)
     <= A_out²=A²/A_S².                         (11)
```

For d>=25, `B²=4^d>12d(d+1)`. One elementary proof starts at d=5, where1024>360, and observes that multiplication by4 dominates the consecutive polynomial ratio `(d+2)/d`. In both shapes and for n>=1,

```
ell<=2d(d+1)n²,
A_S²>B²n²>12d(d+1)n²>=6ell.                     (12)
```

Both q shapes satisfy q>=A²/3 for A>=3. Therefore

```
ell*Hreq <= ell*A²/A_S² < A²/6 <= q/2 < S0.     (13)
```

All representatives `0<=k<Hreq` fit the positive interval.

The accepted aggregate lifting lemma can now be applied without any unproved carry hypothesis. To recall its local mechanism, if c_p<3a_p, put `lambda_p=3a_p−c_p` and `eta_p=(r+1)/p^b_p`. The normalized polynomial

`eta_p*(r+2)+r*(r+2)*y+r*(r−1)*p^b_p*y²`

is eta_p−y modulo p and has a unique unit root modulo every p-power. The source map `y_p(k)=X(k)/p^b_p` is an isometry on p-adic residue classes, since

`v_p(y_p(k)−y_p(k'))=v_p(k−k')`.

It therefore realizes that root in exactly one class modulo p^lambda_p, for arbitrarily large lambda_p. At primes with c_p>=3a_p no condition is needed. CRT gives k0 in `[0,Hreq−1]`; (13) makes its source slack positive. The three-term odd-prime identity then proves

```
A³ | Y(k0), Y(k)=M_r(X(k))/2.                    (14)
```

Thus (14), all outer constraints, exact transport, and positive input/slack hold for every sufficiently large member of the indicated subsequence on each fixed authentic compiler. The ordinary input is constructed; it is not a prescribed arbitrary input. No uniform bound independent of the compiler is asserted.

## 6. The binary boundary is unchanged and open

The source-coupled binary criterion remains independent of k:

```
popcount(R)>=3v2(q)+2.                           (15)
```

If the selected z also satisfies(15), then (14) and the binary criterion give q³|Y, and the accepted conditional Pell completion supplies all18 positive witnesses of the unchanged83 source. This is the only full-zero claim, and it is conditional.

The published small-z two-primary results assume z<=4d. Equation(8) allows a much larger z and does not preserve that hypothesis. No argument here proves(15) for any chosen large-z family member. The theorem therefore closes the aggregate odd-scale condition on subsequences while leaving the binary condition, actual completed source zeros, rejected-input examples and the universal83 question open.

## 7. Dependencies and evidence status

The fresh companion authenticates these exact inherited inputs as inert bytes:

| File | SHA256 |
|---|---|
| complete83_source_coupled_input_lifting.md | 822d192578f379e1e81a00caafbb3612db24989902411748f35ee23343d5934f |
| complete83_aggregate_input_budget.md | 803c6d47b503d611a641b456da3887a46a300c55023dfd1e2a7120de5299903f |
| review_complete83_aggregate_input_budget.md | 00c080ae861b0cc176d070340119b031263ae3c6240cb3699d7b48f4d0954e32 |
| complete83_odd_primary_carry_budget.md | 4b884c4d9cc6fd7100c67b98caee4ec9f968653e7a03c3d41558dc0d5cbc5f95 |
| complete83_odd_prime_boundary.md | 59fb701504a8cab48a4c29b8167ffe459c049feed00dc6a821003747e8a856da |
| complete83_nondyadic_outer_family.md | 42281ee2c1cf99851d4fe67fcfe6f61322fd721d8ebd8ec539983a6edcc44d23 |
| complete83_shared_projection_scout.json | dd9e105d295bf2fb3e3b0246234bb68cb78487ee919405bc052f2b67a9def34c |

Their full native/Pell/compiler ancestors remain inherited at their accepted scopes. This note's new claims are the fixed-prime subsequences, quotient-carry CRT, polynomial enlargement estimate and unconditional odd input budget. The full source-coupled and aggregate proofs were reread, including the all-precision input map and exact positive interval. Twenty-three literal actual83 rows bind the input, slack, selector, packed index and transport; the whole83 array is authenticated but is not evaluated.

Fresh finite corroboration checks48 LTE/subsequence cases using modular exponentiation, without constructing the potentially enormous A. These include relaxed d=1 and d=5; the minus lower bound A_S>Bn is deliberately not asserted at d=1, outside its proved range. Another96 synthetic affine CRT cases check288 exact depths and144 forced S-carry conclusions, with the carry values computed independently through factorial valuations. Their constant A0 is chosen for synthetic positivity, rather than obtained from compiler masks, so they are not actual source instances. An additional10,192 scalar cases and3,456 positive-endpoint cases corroborate the explicit gain and interval bounds.

No predecessor program, saved source array or copied builder is executed or imported. No actual compiler example, huge half-binomial/Pell tuple, binary success or complete positive source zero is materialized. Root and Tesla independently challenged the full mathematical draft without a finding; a separately pinned review remains a distinct artifact.

Fresh writer, normal and optimized-Python exact receipt replays passed from `/` before freeze.

Final helper SHA256: `210506dc2ff70393a975d1768bea748a733f5f6c9b3b7790052c73336315912c`.

Final receipt SHA256: `59ef0669c6708c820c67332667b288ac71c27d362e9793847dc7accd3d3b07d6`.
