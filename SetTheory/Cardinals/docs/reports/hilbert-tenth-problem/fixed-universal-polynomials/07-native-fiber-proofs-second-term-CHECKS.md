# Supporting checks for the two-term count

Date: 2026-10-03. Status: PASS. These finite checks support, but do not prove, the analytic theorem. The proof is in THEOREM.md; an independent boundary decomposition and tied-height inversion are in INDEPENDENT-COUNT-REVIEW.md.

## What was checked

1. Twenty-four integer-exact threshold tests immediately below, at, and above eight Pell heights. Direct enumeration and an inverse-estimate method agree; the latter corrects and verifies every proposed endpoint with integer Pell comparisons, so floating-point proposals never decide membership. The largest tested height has 113,319 bits.
2. Six hundred twelve exact generalized-divisor hyperbola identities using sign-specific exact row cutoffs. Every intersection rectangle is subtracted exactly.
3. Two targeted negative checks: omitting the intersection rectangle changes 592 test answers; dropping the bounded parity phase changes 40 test answers. These demonstrate that the tests exercise both bookkeeping issues rather than assuming the perturbations cannot affect floors.
4. Eight integer-exact large model counts, up to X=10^10, with numerical normalized residuals. The models are:
   - Quadratic energies Eσ(l,k)=l²k for each of two separately labeled arms. Leading coefficient 2ζ(2); secondary coefficient 2ζ(1/2)
   - Perturbed energies Eσ(l,k)=(l²+3l)k+(2σ−1)l+(k mod 2), σ∈{−1,+1}. Leading coefficient 2Σ_l1/[l(l+3)]=11/9; secondary coefficient again 2ζ(1/2)

The bounded parity phase is deliberately retained in every exact count. It can change individual floors. The perturbed model demonstrates the need to keep exact slopes in the leading series: replacing l²+3l by l² would change the leading coefficient, even though the secondary coefficient remains the same.

## Representative numerical results

The predicted normalized secondary coefficient in both models is 2ζ(1/2)≈−2.92070901761917. With R(X)=count−κX−2ζ(1/2)√X:

| Model | X | Exact count | (count−κX)/√X | R(X)/X^(1/3) |
|---|---:|---:|---:|---:|
| Quadratic | 10^4 | 32,614 | −2.84681336965 | 0.34299321449 |
| Quadratic | 10^6 | 3,286,988 | −2.88013369645 | 0.40575321166 |
| Quadratic | 10^8 | 328,957,640 | −2.91733696453 | 0.07264868155 |
| Quadratic | 10^10 | 32,898,389,298 | −2.92038964529 | 0.01482395049 |
| Perturbed | 10^4 | 11,938 | −2.84222222222 | 0.36430343310 |
| Perturbed | 10^6 | 1,219,311 | −2.91122222222 | 0.09486795397 |
| Perturbed | 10^8 | 122,193,015 | −2.92072222222 | −0.00028448455 |
| Perturbed | 10^10 | 12,221,930,206 | −2.92016222222 | 0.02537999409 |

These sampled normalized residuals do not themselves establish a limit, a universal bound, an optimal error exponent, or an arithmetic claim about the native source.

## Pell-model scope

The exact boundary fixtures use A=3,p=3:

- M=8 is a small analytic Pell-count model with M>2p; it is not the native progression M0
- M=105 equals pc/gcd(c,Δ) for these auxiliary data, since Δ=8 and c=ψ_3(3)=35

Neither fixture is asserted to be a complete valid padded native port instance. They test the exact two-index height/count formulas. The analytic native theorem depends on the earlier classification and coordinate-domination proof, not on small examples.

## Replay and numerical details

Run `python ../../check_second_term.py` or `python -O ../../check_second_term.py` from any working directory. Python 3 standard library only is needed. Both modes recompute and compare the committed receipt without writing. Explicit checks remain active under `-O`; no correctness check uses a removable assert. `--write` is the only receipt-update mode.

Pell pairs are computed by exact integer binary exponentiation. Endpoint bracketing and final membership decisions use exact integer inequalities. Ordinary real logarithms are used only to propose candidates, which are corrected and verified before counting. Displayed asymptotic residuals use standard-library Decimal with 60-digit precision and precomputed zeta values. The zeta constants affect only the displayed residuals, never any integer count.

Normal and optimized replay pass. A copied packet was replayed from an unrelated working directory, and its source/receipt hashes and modification times were unchanged. No author repository code was imported or executed. Earlier reports and frozen source files were not modified.
