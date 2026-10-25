# Independent ordinary review: common normalized remainders plus odd-square radix

Reviewer: separate baseline/review agent, 25 October 2026. Scope: the new *raw-system composition*, before the four further affine projections. Verdict: **ordinary arithmetic composition PASS**, conditional only on retaining the exact inherited frame/power/calibration interface described below and on checking the literal edit/projection certificates. This review does not yet accept a newly emitted 246-variable polynomial whose bytes have not been presented here.

## Authenticated source and literal edit boundary

Base `intake/conzfc_common_remainders_20261025/direct/data/guarded.json` has 556 listed coordinates and 388 residuals. Its transformation certificate is `direct/data/remainder_transformation.json`; its ordinary proof is `direct/proofs/NORMALIZED_REMAINDERS_PROOF.md`. The signed frame theorem is retained in `direct/upstream/round17/direct/ORIENTATION_FIRST_PROOF.md`, and its K=x modification in `STRICT_BUDGET_PROOF.md`.

In the actual normalized guarded source, zero-based coordinates are:

- `5 = choose0.output = B`; `6 = pow0.output = V0`;
- `7 = fact0.remainder = r`; `8 = fact0.slack = s`;
- `26 = pow1.output = N`; `179 = pow2.output = q`;
- `185 = choose0.oslack = o`;
- `547,548,549 = new_guard2.a,b,c`.

The literal occurrence census gives exactly:

- row165 `choose0.digit_bound`: `q-B-o-1=0`;
- row385 `domain_guard.2`: `o-a²-b²-c(c+1)=0`;
- o occurs in those two rows only; a,b,c occur in row385 only.

Rows383/384 are the separate retained guards on **fact0.remainder** and **fact0.slack**. These are not the normalized low **choose0.remainder**, and must not be removed. The normalized low-remainder budget, ratio definitions, and every power request remain unchanged.

One exact permitted edit removes rows165/385 and their four now-private coordinates, adds one unrestricted z and the quadratic row `q-(2z+1)²=0`. An equivalent edit keeps row165 and o as an unrestricted monic wire, replaces only row385 by the odd-square row, and later eliminates o. No guard is silently retained on z; every integer z gives an odd square q≥1. This is an existence equivalence, not a bijection on ternary guard witnesses.

## Acyclic soundness

1. **Frame and both coordinate orientations first.** The signed square frame, squared semantic anchor and pooled errors are unchanged. They bound every requested base/exponent/output atom by W, orient every principal Pell pair at its signed nominal index, and yield the signed exact-power lemma without using the q-output guard or any normalized digit remainder. Squares, not prior semantic signs, establish these bounds. This dependency is explicit in the retained orientation-first proof and the independently supplied odd-square proof.
2. **Initial factorial power without q>1.** The horizon `t=16+h0²` is positive. Apply its already canonical pair to base `F²+1≥1`; the signed-power theorem includes base1 at a known nonnegative exponent. Hence `V0=(F²+1)^t≥1`. No q-power is needed for this step, even if provisionally q=1.
3. **Retained ceiling signs recover B and F.** The two untouched ternary guards give r,s≥0. The raw ceiling rows yield `B=r+s+1≥1` and `FB=V0+s`. Thus F≥1 and `FB≥F²+1`, so B>F and B≥2. Also `V0≤FB<B²`; `y=V0(V0-1)>F+2` follows from t≥16.
4. **The B-power establishes x before a q-base is used.** The exact original request `N=B^x` is retained with K=x. Since B≥2, the signed power lemma excludes x<0 independently of q and gives N=B^x. The first endpoint `x=F+1+(y+1)u0` rules out u0≤−1 because then x≤F−y<0. Hence x≥F+1≥2. The last endpoint `x=1+[1+(t+1)y]ut` forces ut≥1 and x≥2+(t+1)y. This is stronger than x≥8.
5. **Representatives before the self-sized radix.** The new odd-square row gives q≥1, so q+1≥2. Every actual representative is an exponent in a retained power request at q+1, and is therefore nonnegative. The same applies to the derived label; its nonzero anchor excludes zero. Thus `H0=1+sum(nine representatives)≥1`. This is about actual representatives (stored shifted coordinates plus1), not a false claim that every stored coordinate is nonnegative.
6. **Recover q>B, then all denominator powers.** The unchanged request with base BH0≥2 and exponent x gives `q=(BH0)^x≥B²>B`. This excludes q=1 and restores o=q−B−1≥0 and its ternary representation. Every remaining q-power now has positive base≥2; all existing canonical denominator and numerator interpretations follow exactly as before.
7. **Normalized common remainders have every required premise.** Let M=q^x; other moduli are q^t,q^(t+1),q^(y+1). The endpoint inequality proves their exponents≤x, so all are positive divisors of M. The three retained ratio rows force exactly v_i=M/L_i>0. Each scaled digit gives v_i|R_i, recovering the integral r_i=R_i/v_i. The single unchanged norm gives |R_i|<M/2 and hence |r_i|<L_i/2. The Common proof's pre-factorial estimate uses V0<B², q≥B^x and x≥8; all have now been established without the deleted guard. It recovers the factorial remainder first, then F=t!, then the other canonical tails (<L_i/32). Thus every original interval and range meaning is restored. The unchanged ordinary C222→ZF→ZFC refutation calibration applies.

The central dependency check is that neither the q-base exponent argument nor the normalized modulus division is invoked before Step6. Recovering `N=B^x` at Step4 avoids that circularity entirely.

## Constructive completeness and parity compatibility

Start with a finite refutation and the Common source's canonical cofinal witnesses, with horizon t≥16. Choose the semantic beta code x in its CRT class **even** and sufficiently large. Its period is odd: `y=V0(V0−1)` is even, so every beta modulus `1+(i+1)y`, including the endpoint moduli, is odd. Adding an odd period toggles parity while retaining all required residues; arbitrarily large allowed representatives remain available.

At F=t!, every `F²/i=F(F/i)` is even for 1≤i≤t, so each reciprocal CRT factor `1+F²/i` is odd. Therefore B and N²=B^(2x) are odd. Shifting any actual representative by N² preserves its source congruences and toggles parity. As in the supplied odd-square proof, choose dominant a in `[2N²,4N²)` and b with opposite parity, preserving the even semantic anchor and its dominance. Independently prescribe one of the other seven representatives' parity (e.g. c) so that their total sum is even, giving H0 odd. The remaining representatives can stay in `(0,2N²]`; all original precision and cap bounds survive.

Now BH0 is odd and x even. Set `W=(BH0)^(x/2)` and `z=(W−1)/2`; q=W²=(2z+1)². Construct the same positive canonical Pell data. The Common scaling introduces no parity restriction: set v_i=M/L_i and R_i=v_i r_i^0. The unchanged canonical estimates give every R_i<M/32. With eleven entries, `4 sum R_i² < (11/256)M² < M²`; the integral nonnegative gap `M²−1−4sum R_i²` has the usual ternary representation. Thus the single common norm has witnesses under the new parity choices.

The fresh parity choices may change private witnesses; the theorem needs existential maps, not identity of all old witnesses. Every restored coordinate is integral, and no restriction is imposed on the unrestricted integer domain beyond the stated equations.

## Quantitative and provenance boundary

The raw source substitution removes3 coordinates and1 row. Because the old q-output relation could be used in monic projection while the new q is quadratic in z, the final projected saving is not determined from raw counts alone. Prior odd-square siblings save2 projected variables, but the exact new250/246 claims require the new literal projector outputs and restoration certificates. The four affine projections are an additional reversible algebraic transformation; this ordinary proof composes with them only after their exact zero-set certificates pass.

The independent supplied odd-square antecedents are:

- `intake/ConZFC_Shared_Certificates_Round18_2026-10-25/signed/PROOF.md`, §7;
- `intake/ConZFC_Centered_Residues_2026-10-25/arithmetic/ODD_SQUARE_AND_WEIGHTED_PROOF.md`, §1.

This composition is not already an emitted endpoint in Common. It combines two credited incoming mechanisms. It proves an ordinary arithmetic reduction relative to inherited calibration; it is not a consistency proof or a new formal-kernel verification.

## Exact source hashes

- `intake/conzfc_common_remainders_20261025/direct/data/guarded.json`  
  SHA256 `24ec75ebe002fdc8b2cd0b7e2112fbf254f66fbbb96af44b217c9af3247bdc5a`.

- `intake/conzfc_common_remainders_20261025/direct/data/remainder_transformation.json`  
  SHA256 `95f16a9b1a7a4a3b811d85459ecac03c2f249f24ee154264d047a1056cf1fb39`.

- `intake/conzfc_common_remainders_20261025/direct/proofs/NORMALIZED_REMAINDERS_PROOF.md`  
  SHA256 `0b1b623effab4bc71dbdb7dbd2b7c3a32d1139fc94ddafa6a02fc7a9433765ec`.

- `intake/conzfc_common_remainders_20261025/direct/upstream/round17/direct/ORIENTATION_FIRST_PROOF.md`  
  SHA256 `e29327e70f0f7d8fa816cef8302ea88cf5a672465c0038f451a7574b3224117a`.

- `intake/conzfc_common_remainders_20261025/direct/upstream/round17/direct/STRICT_BUDGET_PROOF.md`  
  SHA256 `71294e9a6771a06a51e7ea48fcf7e78755159695c9e67cfbd1fc61aeb2654ee0`.

- `intake/ConZFC_Shared_Certificates_Round18_2026-10-25/signed/PROOF.md`  
  SHA256 `575489c0938691e812333a6bb5274b100684d810f348229dc1fbac9f39df1f23`.

- `intake/ConZFC_Centered_Residues_2026-10-25/arithmetic/ODD_SQUARE_AND_WEIGHTED_PROOF.md`  
  SHA256 `25c0a01dc4090662a35286df2a5fe61cec8392a3b18730c8e228d6728954ba7b`.
