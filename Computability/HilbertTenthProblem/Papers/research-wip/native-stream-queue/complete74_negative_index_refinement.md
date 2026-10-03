# Three further restrictions on the negative first-index branch

The nonlinear first-index projection still has **no proved full positive inverse and no full positive counterexample**. This note proves three additional restrictions for the actual `raw30` and `positive22` sources on valid fixed compiler slices:

- The input Pell index is exactly `e=u` or `e=uA`.
- On the remaining branch `r=−p`, the odd defect `d=2n−p` satisfies `4^d>X≥q³`. In particular `d≥7`; the canonical defect `d=1` and also `d=3,5` are impossible.
- For fixed `q,X,Y` and a fixed bounded representative `v`, at most one main index `p` can satisfy the retained first/main ratio interval.

These results restrict the actual first, main, and input equations. They do not appeal to the original positive-`r` soundness theorem, and they do not use an auxiliary sign argument to discard the negative branch. They establish no new circuit, operation bound, witness bound, or universal-language claim.

The [helper](complete74_negative_index_refinement.py) and [receipt](complete74_negative_index_refinement.json) authenticate the actual projection and preceding bootstrap artifacts. The general proofs below are separate from the finite exact checks. No historical Python module is imported or executed, and no search for full zeros is performed.

## 1. Precise source and inherited premises

The immediate source is the [nonlinear first-index projection](complete74_nonlinear_index_projection_scout.md). We use the original symmetric scale and the source notation of the [signed first-index bootstrap](review_complete74_nonlinear_index_bootstrap.md):

```
q=(B−1)J+1, X=wq³, Y=sq³, E=XY,
a=Y(X+1), A=a+2, Delta=A²−1, H=4a+3,
P=2XY²+1, k=eta+zeta, c=kY+eta,
r=k−hE−1, D=X+ac+gamma*H,
u=2d_cell*x+b.
```

Here `d_cell` is the fixed compiler cell size; the defect `d` introduced below is a different mathematical index, not a source port. The fixed compiler contract includes `B=2^d_cell≥16`, positive odd `b<B`, and the coefficient and mask bounds cited by the preceding bootstrap. The actual raw `k` remains a supplied positive coordinate until its retained equality `k=eta+zeta` is imposed. Likewise the raw definitions of `a,c,D,kappa,mu` are retained equations; in `positive22` the corresponding positive graph expressions are computed.

At a positive zero of either of these two packets, the retained raw bound and marker give

```
C+alpha+2d_cell*x=q, C=Z+W,
0<W,C,Z<q, 0<u<2q, u odd.
```

The preceding bootstrap proves, before any original parent theorem,

```
q≥16 and q even,
p≥13 and p odd,
c=psi_A(p), D=chi_A(p), X≡2^p (mod H),
k=2*psi_P(n), n<p<2n,
r=p or r=−p,
p<(q+1)E.
```

Its sign-free rank argument and actual compiler bound are inherited, not re-proved by a numerical sample here. On `r=−p` it further proves

```
2n+p−1=vE,
1≤v≤3q+2,
2p≤vE≤3p−3.
```

The current helper checks the actual first-norm, main-root, discriminant, input-index and input-gap ports in the authenticated saved JSON. The mathematical constant `Delta` is the source port named `A`; the mathematical Pell base `A=a+2` is an abbreviation, not an uncharged source operation.

**Domain limitation.** The new conclusions are stated for `raw30` and `positive22`. In `signed20`, the positive input gap and the positive input root are not yet available on a negative-index zero, and the preceding proof has not reduced its auxiliary congruence to `r=±p` with the same absolute bound. This note does not apply those missing premises to that interface. Its source is inspected only to confirm this distinction.

## 2. The input index has two exact possibilities

Both included packets retain a positive input Pell root and coefficient with a positive gap:

```
mu²−Delta*kappa²=1,
kappa=u+delta*Delta,
c=kappa+phi,   phi>0.
```

The ordinary positive Pell classification therefore gives

```
kappa=psi_A(e), mu=chi_A(e), 0<e<p.
```

The upper bound inherited above is enough to choose exact discriminant representatives, even though it does not establish the old bound `p<A−1`. Indeed `A>q⁶`, so

```
e<p<(q+1)E<(q+1)A<Delta,
0<uA<2qA<Delta.
```

The discriminant congruence holds for every nonnegative integer index:

```
psi_A(e)≡e       (mod Delta), e odd,
psi_A(e)≡e*A     (mod Delta), e even.
```

For completeness, reduce the recurrence modulo `A²−1`. If the consecutive residues are `2t*A` and `2t+1`, the next two are `(2t+2)*A` and `2t+3`. The initial residues are 0 and1, proving the formula by induction; no index-size assumption is part of this recurrence identity.

For odd `e`, the source gives `e≡u mod Delta`. Both values lie strictly between0 and `Delta`, hence **e=u**. For even `e`, multiply `eA≡u mod Delta` by `A`, using `A²≡1`. Then `e≡uA mod Delta`, and the same strict representative window gives **e=uA**.

Since `q` is even, `Y` and `A` are even. Thus `uA` is genuinely an even alternative; parity does not exclude it. The two cases are distinct because `A>1`. The source projection also yields the necessary residues

```
W≡2^u   (mod H), if e=u,
W≡2^(uA) (mod H), if e=uA,
```

with `0<W<q`. This note does not replace either congruence by an integer equality: it has not proved the needed upper bound for the corresponding exponential. The second alternative remains a real proof obligation.

The receipt includes an arithmetic window diagnostic at `q=16,X=Y=4096,u=9`: both `u` and `uA` are below the inherited coarse main-index upper bound `(q+1)E`. This verifies that this coarse window alone does not remove the even alternative. It is not a full zero or a claimed compiler instance.

## 3. A defect lower bound from the exact first/main ratio

Assume now `r=−p` and put

```
d=2n−p.
```

Since `n<p<2n` and `p` is odd, `d` is a positive odd integer. The literal ratio slacks give

```
Y<c/k<Y+1.
```

We prove a lower growth estimate without assuming that `p/a` is small, without asserting `p=2n−1`, and without interpreting the main exponent congruence prematurely.

For every integer base `Q≥2`, the Pell recurrence implies

```
psi_Q(j)>(2Q−1)^(j−1),  j≥2,
psi_Q(j)≤(2Q)^(j−1),   j≥1.
```

The lower bound follows from strict increase and `psi_Q(j+1)>(2Q−1)psi_Q(j)` for `j≥1`; the upper bound follows by dropping the nonnegative subtracted term in the recurrence. Consequently

```
c/k > (2A−1)^(p−1) / [2*(2P)^(n−1)].
```

Use the literal coefficients

```
2A−1 = 2Y(X+1)*(1+3/(2a)),
2P   = 4XY²*(1+1/(2XY²)).
```

Since `3XY²>a=Y(X+1)` and `p>n`,

```
(1+3/(2a))^(p−1) / (1+1/(2XY²))^(n−1) > 1.
```

This yields the exact lower comparison

```
c/k > 2^(−d)*Y^(1−d)*(X+1)^(p−1)/X^(n−1).
```

Combining it with `c/k<Y+1` and using `p+d=2n`,

```
a^d > (X+1)^(2n−1) / [2^d*(1+1/Y)*X^(n−1)]
    > X^n / [2^d*(1+1/Y)]
    > X^n / 3^d.
```

The last strict inequality uses `Y≥4096` and `d≥1`, so `1+1/Y<(3/2)^d`. Equivalently,

```
a > X^((p+d)/(2d))/3.                         (1)
```

Suppose `X≥4^d`. Since `X≥4096>9`, (1) implies

```
a > (X^(1/(2d)))^p * sqrt(X)/3 > 2^p.
```

An entirely integer formulation is `3^(2d)*a^(2d)>X^(p+d)`, while `X^(p+d)>3^(2d)*2^(2dp)` under these same assumptions. Thus no approximation or floating-point logarithm is involved.

Now `0<X<a` and `0<2^p<a`, so the retained congruence `X≡2^p mod H`, with `H=4a+3`, forces `X=2^p`. But the negative representative gives

```
E≤vE≤3p−3<2^p=X≤E,
```

a contradiction; `2^p>3p−3` holds for every `p≥13`. Therefore every negative zero must satisfy

```
4^d>X≥q³.                                     (2)
```

Since `4^6=4096≤X`, this gives `d≥7`. Substitution into `vE=2p+d−1` also strengthens the lower representative bound to

```
2p+6≤vE≤3p−3.                                 (3)
```

This excludes all negative zeros whose first/main indices have a small defect; it does not establish an upper bound on `d` that contradicts (2).

## 4. At most one main index per representative

Fix positive `q,X,Y` with the preceding source constraints, so `A,P,E` are fixed, and fix `v` in `1,…,3q+2`. The representative equation determines

```
n=(vE+1−p)/2.
```

As an odd candidate `p` increases by2, `n` decreases by1. Suppose two distinct admissible odd indices `p<p'` both satisfied the retained ratio, with their associated positive indices `n>n'`. Strict Pell growth gives

```
psi_A(p') > (2A−1)^2*psi_A(p),
psi_P(n') < psi_P(n).
```

It follows that

```
psi_A(p')/[2psi_P(n')]
  > (2A−1)^2 * psi_A(p)/[2psi_P(n)]
  > (2A−1)^2*Y
  > Y+1.
```

The final inequality holds since `A=Y(X+1)+2>Y≥1`. This contradicts the second candidate's upper ratio bound. Thus **at most one p per fixed v** is possible. The conclusion is about native index pairs at fixed `q,X,Y`; it is not uniqueness of a full witness tuple, and it is not a global finite search because these three parameters remain unbounded. The actual positive integers `c,k,tau,D` would then be fixed by their Pell indices, while auxiliary witnesses and other fields have not been classified.

## 5. Supplementary exact checks and unresolved boundary

The checker authenticates eight current-byte dependencies before use. It verifies the literal premise ports in all three saved source interfaces, including the absent gap in `signed20`. Its finite checks comprise160 exact discriminant-recurrence instances,36 input residue-window cases,50 exact first/main ratio lower bounds,48 ratio-jump inequalities, and54 integer exponent-exclusion comparisons. They check the displayed algebra and inequalities on fixed fixtures; they neither search for complete zeros nor replace the general proofs.

The second input-index alternative and the high-defect first/main branches survive these deductions. No compatible full positive tuple on `r=−p` has been constructed, and no contradiction excludes all such tuples. The positive inverse of the nonlinear projection therefore remains unresolved, with the established universal bounds unchanged.

The standard-library CLI is a bounded proof corroborator, not a maintained compiler or general packet API:

```
python3 complete74_negative_index_refinement.py \
  --root /path/to/native-stream-queue \
  --expect complete74_negative_index_refinement.json
```

Dependencies are strict current-byte pins; there is no Git fallback. `--output` writes the deterministic receipt and `--expect` compares types and values after a JSON roundtrip. The source-specific bootstrap, including its coefficient bound and both-sign auxiliary analysis, remains the cited dependency rather than a historical suite rerun.
