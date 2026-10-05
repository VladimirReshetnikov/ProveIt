# The exact positive input budget for source-coupled odd-prime lifting

The source-coupled lifting theorem can use the entire positive interval of ordinary inputs, rather than stopping after A representatives. This replaces its separate hypotheses `c_p>=2a` by an exact aggregate condition. The new condition is still unproved for the constructed actual-compiler family; the binary population condition also remains separate when z has been enlarged. No full source zero or language counterexample is asserted.

The polynomial, all fixed numerals, and all18 supplied witnesses remain unchanged. Roots, gcds and CRT representatives below are mathematical existence constructions, not free operations in a circuit.

## 1. Fixed source data and its exact positive interval

Retain the frozen source-coupled family. In particular `D=dn`, `Q=B^n`, `n=1 mod4`, `A=odd(q)`, and

```
plus:  A=Q+1,   q=A(A−1)/2,  T=n(D−1),
minus: A=2Q−1,  q=A(A+1)/2,  T=n(D+1),
ell=2dT.
```

Fix a positive resonance representative z from that theorem, so `z=1 mod4`, `R=b mod2d`, and, for every odd `p^a || A`,

```
b_p=a+tau_p=v_p(r+1),    r=(R−1)/2,
tau_p=v_p(D−1) (plus), or v_p(D) (minus).
```

The source has `C=Z=z`, `F=Kz`, `W=0`, and its packed index R depends only on q,z and the fixed masks. Let x0 be the representative in `[5n,5n+T−1]` of `(R−b)/(2d)` modulo T. Put

```
u0=2dx0+b,
S0=q−(K+2)z−2dx0,
x(k)=x0+kT,
u(k)=u0+ell*k,
alpha(k)=S0−ell*k.                              (1)
```

Assume S0>0. For nonnegative integer k the exact positive interval is

```
0<=k<=Kmax=floor((S0−1)/ell).
```

It contains exactly

```
Npositive=Kmax+1=ceil(S0/ell)                     (2)
```

representatives. This follows directly from the literal paid slack; it does not assume R changes with x. Every such k has positive x and alpha, `u>=10D+b`, and `u<q+b<2q<R`. The same outer proofs give `R=3 mod4`, `3q+1<R<q^4−q^3`, and `q(q−1)|X(k)`, where `X(k)=2^R−2^u(k)>0`. The source's transport coordinate remains `1+z(X(k)/q)/(q−1)>0`.

## 2. Arbitrarily deep local precision is available

Write

```
c_p=v_p(binomial(2r,r)),
h_p=(r+1)/p^b_p,
e_p=v_p(binomial(2h_p,h_p)).
```

The accepted exact carry identity gives

```
c_p=a+tau_p+e_p.                                 (3)
```

Define the required local precision by

```
lambda_p=max(3a−c_p,0).
```

When lambda_p=0 there is no local input restriction. Otherwise use the normalized simple-root polynomial

```
f_p(y)=h_p*(r+2)+r*(r+2)*y+r*(r−1)*p^b_p*y².
```

Its reduction is `h_p−y` modulo p, so its root is a unit and its derivative is a unit. It has a unique root modulo `p^lambda_p`. The source map `y_p(k)=X(k)/p^b_p` satisfies, for distinct nonnegative k,k',

```
v_p(y_p(k)−y_p(k'))=v_p(k−k').                   (4)
```

Indeed the source period has `v_p(2^ell−1)=b_p`; the difference of two powers and odd-prime lifting give (4). Consequently the map on residues modulo p^h is a bijection for every h>=1, not only h<=a. This argument uses the integer continuation of X(k), which can be negative outside the positive interval; only the final chosen representative must lie in (2).

Composing the unique polynomial root with that bijection imposes one residue class on k modulo `p^lambda_p`. It forces the exact valuation `v_p(X(k))=b_p` and the odd-prime cube condition. Primes with lambda_p=0 already satisfy that condition for every input in the progression, since each relevant weighted binomial term has valuation at least c_p. All periods and the transport congruence remain fixed.

CRT therefore determines a unique class

```
k=k0 mod Hreq,
0<=k0<Hreq,
Hreq=product_(p|A) p^max(3a−c_p,0).              (5)
```

Empty CRT data have Hreq=1 and k0=0. No upper bound on lambda_p by a is needed for this step.

## 3. Exact capped carry budget

Equation(3) makes the modulus in(5) exactly

```
Hreq=A²/(Gcap*Ecap),
Gcap=product_(p|A) p^min(tau_p,2a),
Ecap=product_(p|A) p^min(e_p,max(2a−tau_p,0)).     (6)
```

At each prime this is the elementary equality

`2a−min(tau_p,2a)−min(e_p,max(2a−tau_p,0))=max(2a−tau_p−e_p,0)`.

The caps are essential; dividing by an uncapped product can overstate the available gain when some central valuations already exceed3a. Equivalently, if `C0=binomial(2r,r)`, then A divides C0 and

```
Gcap*Ecap=gcd(A²,C0/A),
Hreq=A³/gcd(A³,C0).                              (7)
```

For the fixed local roots, the **exact** condition for some nonnegative representative in their CRT class to have positive slack is

```
k0<=Kmax.                                        (8)
```

Any other nonnegative representative is k0+jHreq with j>=0 and is no smaller. A convenient sufficient condition that works for every possible CRT residue is

```
Hreq<=Npositive
iff ell*(Hreq−1)<S0.                             (9)
```

Condition(9) is not necessary for the particular class in(8). It is the exact condition that all residues0 through Hreq−1 fit in the available interval.

This extends the prior theorem. That theorem's `c_p>=2a` conditions imply Hreq<=A, and its interval bound ensures A<=Npositive. Neither individual restriction is needed once (8), or the stronger uniform guarantee(9), is checked.

## 4. A sufficient aggregate requirement of polynomial size

For all sufficiently large n in the original family class, the resonance construction can be made with

```
S0>q/2.                                         (10)
```

This follows uniformly for every constructed z from the explicit bounds `z<=Zmax` and `x0<5n+T`. One may require the decidable finite inequality

```
(K+2)*Zmax+2d*(5n+T)<q/2.
```

The inherited estimate `Zmax=O(n Q^(3/2))` and `T=O(n²)`, with fixed compiler constants, proves that all sufficiently large n satisfy it. This is a stronger positivity margin only; it supplies no new carry claim.

Both shapes have `q>=A²/3` for A>=3. Thus (10), together with

```
Gcap*Ecap>=6ell=12dT,                            (11)
```

implies

`ell*Hreq<=A²/6<=q/2<S0`,

and hence(9). The required aggregate factor is therefore only of order D², while A grows exponentially in D. The earlier per-prime sufficient conditions instead give `Gcap*Ecap>=A`. This comparison is a strict relaxation of the numerical sufficient condition for large A; it is not an existence assertion about carries on the actual source.

## 5. Conditional full completion and unresolved conditions

If (8) holds, its k0 passes every odd-primary cube condition and has positive outer slack. If in addition

```
popcount(R)>=3v2(q)+2,                           (12)
```

the accepted input-invariant binary theorem gives the full `q³|Y`, and the accepted source-coupled converse supplies all18 positive witnesses. This remains a conditional actual-compiler completion theorem on the unchanged source.

The n>=5 sparse two-primary theorem applies to the original representatives `z<=4d`. It does not establish (12) for the larger CRT resonance representatives used here. Nor do the source divisibility obstruction or the exact carry decomposition prove(11). Simultaneously forcing deep denominator resonances at all odd primes remains obstructed, while additional carries in the quotient h_p could still provide the aggregate factor. The note does not prove automatic odd carries, automatic binary population, any completed actual-compiler member, or any rejected ordinary input.

## 6. Local illustration and evidence boundary

A local arithmetic example suggested by root has `r=503`, `R=1007`, `ell=6`, `A=21`, and `u0=5`. Its depths are `b_3=2`, `b_7=1`; its central valuations are `c_3=4`, `c_7=1`. Hence `Hreq=49>A`, and the unique local root class has least representative k0=25, giving u=155. The7-adic precision2 exceeds a7=1, demonstrating the need to permit deeper input residue maps. Fresh direct checks also show `M_503(2^1007−2^155)=0 mod(2*42³)`.

This example is **not** a source-slack example at q=42: `ell*k0=150>q`, so positive actual slack at that q is impossible. It illustrates local reachability and divisibility only. It has no supplied compiler constants, actual history, or complete positive source tuple. Its usefulness does not discharge(8) on the actual family.

The fresh companion authenticates eight frozen proof/source/evidence files as inert bytes, with exact hashes in its receipt. Twenty-three literal actual83 rows bind the ordinary input, positive slack, unchanged packed index and transport unit. The full source-coupled input-lifting proof and odd-primary carry-budget proof were read; their input map, normalized root and quotient-carry arguments are restated above. The full prior native/Pell/half-binomial proofs and circuit audits remain inherited at their accepted scope.

Fresh checks cover110,592 positive-interval/CRT-modulus combinations,2,984 capped exponent cases (including tau>2a),1,092 exact finite binomial/carry/gcd comparisons, and96 source-coordinate identities under relaxed scalar assignments. Of the finite binomial cases,584 have Hreq>A; they are not actual source histories. The coordinate cases test constant C,W,R and the transport unit but use chosen transport multiples, not exponential w values. The local r503 check independently enumerates the full49-element normalized residue permutation and all504 terms of M modulo2*42³. It retains the explicit slack failure noted above.

No predecessor program, copied builder, or frozen helper is executed or imported. The actual83 array is authenticated and its interface rows compared as data, not run as a program. No actual compiler, huge Pell tuple, or complete source zero is materialized. Finite evidence corroborates the algebra and preserves all remaining quantified conditions.

Fresh writer, normal and optimized-Python exact receipt replays passed from `/` before freeze. Root independently challenged the full proof with no finding. A separate independent review by Pascal remains a distinct artifact.

Final helper SHA256: `07c7acb10810b43f7198a63b2bc465c3a59b5dfde38aa9123eb31d016999c8d7`.

Final receipt SHA256: `19b5f15b30f99cd6913214eff22366d3417ab4251aa509a018f662e0a5104602`.
