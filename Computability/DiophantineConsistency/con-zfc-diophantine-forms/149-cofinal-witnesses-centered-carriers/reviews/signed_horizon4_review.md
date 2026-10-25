# Independent ordinary review: signed common-remainder horizon 4

Reviewer: separate baseline/review agent, 25 October 2026. Verdict: **PASS**, with the explicitly supplied small-horizon factorial lemma below. This changes the semantic horizon restriction; it is not a claim of equality or arbitrary-witness bijection with the old t≥16 source. The earlier odd-square/common composition review remains applicable with the replaced threshold arguments.

## Exact literal delta

Compared `quartic/sources/common_remainders250_odd.json` with `quartic/sources/common_remainders250_odd_horizon4.json`: both have250 unrestricted integer variables and182 quadratic residuals. The intended edit is solely zero-based row161, label `cofinal.horizon`:

- old: `−16+x0−x219²`;
- new: `−4+x0−x219²`.

Here x0 is the **actual semantic horizon t**, not the old unshifted t0 coordinate. Thus the new condition is t=4+h²≥4. All other arithmetic, frame, anchor, power requests, floor/ceiling bounds, three ratios, normalized digits, common norm, and beta residual remain unchanged. In particular actual beta base y is still constrained by `y=V(V−1)`, not merely chosen that way during completeness.

The new horizon set is cofinal: for any finite bound T choose h with4+h²≥T. The proof-tree length, local parameters, complete label sums and truth-padding tuple can therefore all be dominated before F or pending-state products are defined.

## 1. Frame, orientation and early bootstrap at the new minimum

The square frame still is W=2+sum(atom²), includes t, and gives W≥18, every |atom|<W, and every requested |index|<W. The source has14 independent principal pairs; even the inherited conservative count15 is sufficient. For W≥18,

`15W²+15<W³`, so `4mW²+4m<4W³` for m≤15.

The bounded signed orientation proof therefore remains valid. The odd Pell frame still supplies |A|>W^W and |A−1|>4W³; at W≥18 the numerical estimate is much stronger than needed. The signed anchor classification and its squared-cap completeness use only W>m, not t≥16 itself. No comparison/seed equation or occurrence has been removed.

Following `odd_common_review.md`, first interpret V=(F²+1)^t at the canonical positive t index, including the base1 case. The two untouched factorial ceiling signs yield F≥1,B>F≥1 and V<B². At t≥4, V≥16 and y=V(V−1)≥240; moreover y>F+2 for every F≥1. For example V≥(F²+1)²>F+3, and y≥V−1>F+2. The exact request N=B^x (or, after representative recovery, q=(BH0)^x) excludes x<0. The unchanged endpoints then force

`x≥2+(t+1)y≥1202`.

Thus x≥8, the only early numerical threshold used by the Common pre-factorial tail estimate. The odd-square row gives q≥1; q+1≥2 orients all actual representatives, then q=(BH0)^x≥B²>B restores the deleted output slack. All modulus/divisor and normalized-remainder steps occur only after this stage. Common's pre-factorial bound V<B² and q≥B^x gives the exact factorial low digit without knowing F=t!.

## 2. The rising square-radius fixed point, including t=4 and5

The inherited rising lemma was stated for t≥6; blindly citing it at t4/5 would leave a genuine gap. Define

`H_t(F)=(F²+1)^t/binom(F²+t,t)=t! ∏_{i=1}^t (F²+1)/(F²+i)`.

For every positive F, H_t(F)≤t!, so a fixed point F=ceil(H_t(F)) satisfies F≤t!. `factorial_small_horizons.json` exhausts all24 cases F=1..24 at t4 and all120 cases F=1..120 at t5, checking the exact equivalent inequalities `(F−1)B<V≤FB`. It gives onlyF24/F120. Every integer B and V is independently recomputed by a consecutive-product/factorial route, separate from math.comb. This is a complete finite proof because the universal bound proves that no untested positive F is possible; it is not sampled numerical evidence.

A compact ordinary proof avoiding a144-row printed table is also available. Each factor in H_t(F) is nondecreasing with F. The following exact lower bounds exceed the upper endpoint of the associated interval:

| t | F interval | exact H at its left endpoint | strictly greater than |
|---|---|---|---:|
|4|1..3|16/5|3|
|4|4..17|4913/285|17|
|4|18..23|34328125/1456894|23|
|5|1..5|16/3|5|
|5|6..92|1874161/20254|92|
|5|93..119|27992032531250000/233536719655001|119|

Consequently H_t(F)>F at every F<t!, excluding fixed points. At F=T=t!, the elementary product estimate gives H_t(T)>T−t(t−1)/(2T)>T−1, while H_t(T)≤T, proving the fixed point. For t≥6 the retained proof applies unchanged. Hence the rising lemma is now established for **every t≥4**, including all values4+h².

## 3. Amplification and label bounds after factoriality

Now F=t!≥24 and

`V=(F²+1)^t≥577^4>2^36`.

Thus V−1≥2^36 and `y=V(V−1)>2^72` (the weaker >2^71 also suffices), so x>2^73. Both t and F are smaller than y, and the endpoints give R=2+t+x+y+F<2x.

For E=2^23, the inherited elementary estimate `(2x)^E<2^x` applies as soon as x≥2^32; the new bound is much stronger. The local polynomial ledger itself depends only on the bounded source variables and R, not on an independent t≥16 assumption. Hence all local values remain strictly below2^x, ensuring prime-power residues identify their actual values.

For ell=2^22, y>ell and x>(t+1)y give `ell(t+1)<x` directly. This replaces the old use of ell(t+1)<2F, which is false at t4 and must **not** be copied. After factoriality the rising CRT product B=∏(1+F²/i)>F²+1, so the encoded index representative is nonzero and H0≥2. The repaired zero-representative majorant h≤H0^ell then supplies every derived-label coefficient bound. Ordinary representatives use max(1,a), so zero actual representatives cause no missing constant coefficient.

Every denominator exponent t,t+1,y+1,x is≤x. Reciprocal CRT factors remain integral, positive and pairwise coprime, with no prime factor≤t. Amplified precision2x loses at mostk−1<x in a k! denominator. All range, local-label, beta overlap and Horn-flow soundness therefore retains its stated premises.

## 4. Complete cofinal construction and pending-state bounds

Start with a finite calibrated refutation, expand its proof DAG to a finite proof tree, and choose t=4+h² above its number of rule occurrences, every local parameter and full label sum, and the truth-padding tuple's label sum. This choice is independent of F and pending products. Set F=t!,V=(F²+1)^t,y=V(V−1).

At every backward-expansion stage, each pending nontruth occurrence roots a distinct not-yet-expanded subtree. There are at mostt such occurrences. Each positive label j≤t has weight1+jF≤1+tF. Since F=t!>t for t≥4,

`1+tF<F²+1`, so every pending product is `≤(1+tF)^t<V≤y`.

Truth leaves/padding have weight1 and do not increase this bound. Also y≥F+1. Because V≡1 modF, F|V−1 and hence F|y. Thus every beta modulus1+(i+1)y is pairwise coprime by the standard index-difference argument. Actual prescribed pending-state residues, including initialF+1 and final1, have a common natural beta code x; choose a sufficiently large representative. All canonical local/endpoint quotients are natural and the strict u,v<x ranges hold.

The inherited odd-square requirement is compatible: y=V(V−1) is even, hence beta moduli and their common period are odd. Choose x even in that CRT class. Every `F²/i` is even, so each rising factor1+F²/i, B and N² is odd. Choose a,b with the opposite parities needed by the even dominant semantic anchor and an independent third representative parity making H0 odd. These choices preserve all congruences and the bounds a<4N²,others≤2N². Then q=(BH0)^x is an odd square. Fixed front indices are belowN² and h≥2a²≥8N⁴ dominates all requested indices, so the complete signed cap and odd auxiliary construction still have witnesses.

Finally set each common ratio v_i=M/L_i and normalized residue R_i=v_i r_i^0. The existing `<L_i/32` margin follows from the newly proved bounds; hence `4sum R_i²<(11/256)M²`, furnishing the single ternary norm slack. All untouched power, digit, frame and calibrated source rows have their canonical witnesses.

## Conclusion and finite boundary

The smaller signed horizon is sound and complete relative to the same ordinary C222/ZF/ZFC calibration. Its two nontrivial repairs are: extend the rising fixed-point lemma to t4/5; replace the old factorial-based ell-budget by the much larger actual cofinal y. Every source/padding/CRT requirement has been checked, not only asymptotic size inequalities.

Exact endpoint dimensions/support/heights and subsequent row/coordinate transforms remain the responsibility of their finite certificates. The Macaulay high-degree matrix is unchanged by a pure residual-constant edit before identical transforms, because the ignored low-degree part contains every constant contribution; any transferred rank claim should nevertheless bind its exact displayed source/certificate.

## Exact byte pins

- `quartic/sources/common_remainders250_odd.json`  
  SHA256 `22a809f871edd08b1c311b037cf64e1f5231ccc827198ec7ab8ce278af5d0416`.

- `quartic/sources/common_remainders250_odd_horizon4.json`  
  SHA256 `d13a9d2a765df17f9e4fbcb24413ec080cafe3ca58800de92af751c6d175f76a`.

- `factorial_small_horizons.json`  
  SHA256 `5a44fbb2eb3e634bac09533aec4f9b4d70251320e27ebb32cb63e69d005ea9e9`.

- `factorial_small_horizons.py`  
  SHA256 `06f57156d657dfb290cf6d944d9dd96c024f58864a10b078687c3f0f15a33157`.

- `intake/conzfc_common_remainders_20261025/direct/upstream/round17/architecture/proofs/INHERITED_MODULAR_FACTORIAL_PROOF.md`  
  SHA256 `054e8ba6a55d30b4ad8d8e394cbaaf24d85377119f88f5afae81d109e4fd00f5`.

- `intake/conzfc_common_remainders_20261025/direct/upstream/round17/direct/STRICT_BUDGET_PROOF.md`  
  SHA256 `71294e9a6771a06a51e7ea48fcf7e78755159695c9e67cfbd1fc61aeb2654ee0`.

Literal delta comparison: PASS; identical variables and181 untouched residuals, with exactly row161 changing its constant−16 to−4.
