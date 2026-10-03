# Signed first-index bootstrap for the complete74 nonlinear projection

The missing inverse positivity is **still unresolved**, but the ordinary auxiliary rank theorem can be recovered without it. For the actual raw30 and positive22 projections, every positive zero has an even q and its restored index is exactly **r=p or r=−p**, where p is the positive main Pell index. A remaining negative zero would satisfy an explicit short family of first-index representatives. The auxiliary subsystem itself admits a parametric positive-witness construction with r=−p, including at arbitrarily large p. Thus its rank and sign equations alone cannot eliminate the negative branch.

This is a successor to the [nonlinear index scout](complete74_nonlinear_index_projection_scout.md), not a claim that its candidate positive zero sets are sound. The [independent helper](review_complete74_nonlinear_index_bootstrap.py) authenticates all three actual sources and the cited proof notes; its [receipt](review_complete74_nonlinear_index_bootstrap.json) contains bounded exact corroboration. It runs no author or historical Python and emits no new arithmetic compiler.

## 1. Actual interfaces and uniform preliminary facts

Use the original symmetric scale in the three literal74 packets:

```
q=(B−1)J+1, X=wq³, Y=sq³, E=XY,
a=Y(X+1), A=a+2, Delta=A²−1, H=4a+3,
c=kY+eta, k=eta+zeta,
r=k−hE−1, U=jc−r, T=i*c².
```

In raw30, the equalities defining a,c,k and the positive main root D are retained comparisons. In positive22 and signed20 they are computed graph definitions. The actual raw k remains the supplied coordinate until its retained comparison is used. The main root is

```
D=X+ac+gamma*H,
```

where gamma is positive ga in raw30/positive22 and the positive sum rho+sigma in signed20. The supplied first root tau is positive in all three modes. No omitted input coordinate, signed input root, typed word, dyadic q, or parent soundness theorem is assumed here.

Every source retains the main, ordinary strong and auxiliary equations

```
D²−Delta*c²=1,
T²=Delta*(f²−1),
T²*(U²−y²)=1−y²,
U=of−c.
```

On admissible fixed compiler slices, B=2^d≥16 and the actual fixed mask port is MF0+B−1. Set

```
S'=Z+qF−1,
T'=MC*J+1+q*(MF0*J−1).
```

The literal packing equality is

```
r=(q²−S')*(q²−1)+T',   0<T'<q²−1.
```

Since F,Z>0, S'≥q. Consequently **r<q⁴ and r≠0 in all three modes**, regardless of its sign. A lower bound on r has not been assumed.

## 2. Main index and ordinary rank without r positivity

The positive main norm gives

```
c=psi_A(p), D=chi_A(p), p≥1.
```

The recurrence for `chi_A(t)−a*psi_A(t)` has initial values 1,2 and is congruent modulo H to 2^t. Thus the actual main-root definition gives

```
X ≡ 2^p (mod H).
```

Now X≥q³≥4096, a=Y(X+1)>q⁶≥2²⁴, and 0<X<a. If p≤11, both X and 2^p lie strictly between 0 and a<H, so the congruence forces X=2^p≤2048, a contradiction. Therefore **p≥12** before any auxiliary equation or positivity of r is used.

Pell growth now gives

```
c≥(2A−1)^(p−1)>A⁵>A*Delta²,   c>2p,   c>q⁴.
```

These are the actual size hypotheses of the generic rank argument in [the relaxed auxiliary proof](../../1980/PELL_RELAXED_AUXILIARY_PROOF.md). Its historical A=a+4 specialization is irrelevant to that argument; here A=a+2 and precisely the required inequalities have been established. Applying it to the **ordinary** retained equation `T²=Delta*(f²−1)`, with T=i*c²>0, yields

```
f=chi_A(m), p|m, c|m, m≥c>2p,
T=Delta*psi_A(m).
```

In particular f>2c. No normalized strong norm is substituted for the ordinary equation.

The auxiliary argument U is also positive in all three sources. If r≤0 this is immediate from j,c>0. If r>0, the already proved upper bound gives r<q⁴<c, hence U=jc−r>0. Thus the normalized auxiliary Pell root T*U is positive and has an odd index ell:

```
T*U=chi_T(ell), y=psi_T(ell), ell odd.
```

The exact odd-index quotient polynomial and the strengthened plus-sign step-down in [the fixed-minus parity proof](../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md) apply with 0<2p<m. They give

```
ell=epsilon*p+2m*t, epsilon∈{1,−1}, t∈Z,
r ≡ p or −p (mod c).
```

In particular p is odd; combined with p≥12, this improves to p≥13. These conclusions hold for all three projected sources. They do not require W>0 or positivity of the computed signed20 input root.

## 3. Raw30/positive22: the two exact signs and even q

These two interfaces still have C=Z+W, with C,Z,W positive, and retain the raw bound. Hence 0<Z<C<q. The transport equation gives

```
0<F<(K+X)C<(K+X)q,   K=DC+B*DR.
```

The compiler bound used here is genuine fixed-source provenance: [complete78, Section2, equation(8)](../../1980/FIXED_RAW_UNIVERSAL_78_PROOF.md) states 0<DC,DR<B. The [complete76 change](../../1980/FIXED_RAW_UNIVERSAL_76_PROOF.md) places its extra monomial strictly below L and increases the coefficient margin; the [modified75 compiler](complete75_half_binomial_compiler.md) further strengthens the no-carry margin. Thus these modified coefficients still satisfy

```
K≤(B−1)+B(B−1)=B²−1<q².
```

This is not a bound asserted for arbitrary numerical evaluator ports.

In the original packing formula, `(q²−Z)(q²−1)` and the mask term are positive. Therefore

```
r>−qF(q²−1)>−q⁴(K+X).
```

Together with r<q⁴ this yields `|r|<q⁴(K+X)`. Since X≥q³, a>Xq³ and c>A⁵,

```
2q⁴(K+X)<4q⁴X<(Xq³)⁵<c.
```

Consequently |r|<c/2. Since 0<p<c/2, the auxiliary congruence now restores the exact alternatives **r=p or r=−p**. It does not select the positive one.

These sources also force q even. If q were odd, J would be even because B−1 is odd. Both terms of the actual packing formula would then be even, making r even. But r=±p and the preceding step proves p odd. This contradiction uses no prior power-of-two typing.

The analogous absolute bound is not available in signed20: its computed W may be negative, so C=Z+W does not bound Z. That interface retains only the rank/congruence conclusions of Section2 at this stage.

## 4. The remaining negative first-index representatives

The first norm has its usual classification independent of r:

```
P=2XY²+1, k=2*psi_P(n), n≥1.
```

The interval `Y<c/k<Y+1` and P>A give n<p. In the other direction set Q=2A²−1. Then Q>P and

```
psi_A(2n)=2A*psi_Q(n).
```

If p≥2n, monotonicity would imply

```
c/k ≥ A*psi_Q(n)/psi_P(n) ≥ A > Y+1,
```

a contradiction. Thus **n<p<2n**, without a positive packed index.

For the raw30/positive22 negative branch r=−p, the restored defining equation gives `k=1−p+hE`. Since P=1 modulo E, the psi recurrence gives `k≡2n modulo E`. Therefore

```
2n+p−1=vE
```

for a positive integer v. Since p is odd and n<p<2n,

```
2p≤vE≤3p−3,   vE/3<p≤vE/2.
```

The earlier absolute bound also gives

```
p<q⁴(X+q²)<(q+1)XY=(q+1)E,
```

using Y≥q³ and X≥q³. Thus `1≤v≤3q+2`. This is a bounded family of representatives for each q, not a global finite enumeration or a contradiction. The former positive-index inference `2n=p+1` is unavailable here.

## 5. A parametric positive auxiliary realization of r=−p

The remaining auxiliary signs cannot themselves refute the negative branch, even under arbitrarily strong rank bounds. Fix any A≥2 and odd p≥3 with `c=psi_A(p)>2p`. Choose

```
m=cp   if p=3 modulo4,
m=2cp  if p=1 modulo4,
f=chi_A(m), T=Delta*psi_A(m), i=T/c²,
ell=p+2m, U=chi_T(ell)/T, y=psi_T(ell),
r=−p, j=(U−p)/c, o=(U+c)/f.
```

All divisions are exact. For i, put m=p*t with t=c or2c and expand `(chi_A(p)+c*sqrt(Delta))^t`. Its sqrt coefficient is `t*c*chi_A(p)^(t−1)` plus terms divisible by c³. Since c|t, c² divides psi_A(m), and i is a positive integer. The ordinary Pell identity gives `T²=Delta*(f²−1)`.

Since ell is odd, chi_T(ell) is divisible by T. Writing h_aux=(ell−1)/2, the choice of m makes h_aux even. The quotient-polynomial identities yield

```
U ≡ ell ≡ p (mod c),
U ≡ psi_A(ell) ≡ −psi_A(p)=−c (mod f).
```

The second step uses `psi_A(z+2m)≡−psi_A(z) modulo chi_A(m)`. Thus j and o are integers. Since T≥c² and ell≥3, U≥4T²−3>p, giving j>0; U+c>0 gives o>0. The normalized Pell identity supplies

```
T²*(U²−y²)=1−y²,
U=jc−r=of−c.
```

Every supplied auxiliary witness i,j,o,f,y is strictly positive. Taking p arbitrarily large, for example p≥13, also gives c>A*Delta² and every rank size condition used above. The construction therefore survives those size hypotheses, not merely a small parity example.

For comparison with the necessity signs, writing ell=epsilon*p+2m*t gives

```
U≡(−1)^((p−1)/2+mt)*p (mod c),
U≡(−1)^((p−1)/2+(m+1)t)*c (mod f).
```

On r=−p the original comparisons require the first sign positive and the second negative. They force t odd and `(p−1)/2+m` even. The displayed construction takes epsilon=1,t=1 and exactly satisfies these requirements. Applying the old equal-sign fixed-minus parity conclusion here would incorrectly discard this mixed-sign possibility.

This is a full construction for the **ordinary strong/auxiliary subsystem**, not a zero of the entire nonlinear projection. It does not supply compatible first-norm indices, packing, transport or input witnesses. In particular it does not establish false acceptance, unsoundness, or impossibility of a different full-system positivity proof.

## 6. Bounded corroboration and remaining obligation

The helper authenticates 12 source/proof files, checks the literal premise ports in all three candidates, and records 264 small-index projection checks, 384 exact outer-bound fixtures including 192 odd-q parity cases, 108 doubled-index identities, and 7,114 finite integer representative cases. These corroborate the general proofs rather than replacing them. Five exact modular constructions check both p-mod4 branches.

One entire auxiliary-only tuple is materialized at A=3,p=3,c=35,m=105,ell=213,r=−3. It has positive i,j,o,f,y and exactly satisfies all four strong/auxiliary equations. U has 56,928 bits; the receipt stores a digest and the checker reconstructs and verifies the actual integers. This small example is outside the large-index bootstrap; the preceding parametric proof separately covers its large-index range. No full compiler zero is materialized or claimed.

The unresolved full inverse is now more specific. Raw30/positive22 must eliminate or realize the r=−p branch together with its bounded first-index representatives and the retained input/outer equations. Signed20 additionally needs to bound the negative representatives and recover its computed input-root sign without assuming the old r>0 packing bound. No operation, witness or universal-language bound is promoted by this note.

Replay uses only standard-library Python:

```
python3 review_complete74_nonlinear_index_bootstrap.py \
  --root /path/to/native-stream-queue \
  --expect review_complete74_nonlinear_index_bootstrap.json
```

All dependencies are strict current-byte pins. There is no Git fallback, historical suite, or maintained public-packet API. The compiler coefficient bound and doubled-index simplification were separately checked by root; this note retains those concrete source conditions explicitly.
