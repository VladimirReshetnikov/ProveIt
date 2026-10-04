# Verified POWER reductions

This is a separate continuation, not a modification of Reports 65/66 or earlier packets.

## Mathematical outcome

The root's proposed four nonnegative quotients are valid for every positive solution and every b>=2. `PROOF.md` supplies all inequalities, both positive-adapter witness maps, all equations, the exact dependency, and the generic infinite-fiber proof.

Further elimination variants are proved in `ELIMINATION_VARIANTS.md`:

- 22 positive leaves including output, 15 residuals, degree 12
- 16 positive leaves including output, 9 residuals, degree 12
- 14 positive leaves including output, 7 residuals, degree 16
- 13 positive leaves including output, 6 residuals, degree 16 for fixed base b>=2; degree 20 for variable b=B+1

The last formula's rational alpha has integer square by the auxiliary Pell equation, hence alpha is integral. Positivity recovers every removed positive leaf. The 22-to-16-to-14-to-13 eliminations are bijective on solution sets; the earlier 26-to-22 normalization removes only common-shift redundancy.

For the three-gap compressed bounded family, the four variants give respectively 49/38, 37/26, 33/22, 31/20 positive-witness/residual-slot counts. Three external positive gaps are excluded from those witness counts. Fixed-base module degrees are respectively 12,12,16,16; the composed degree is max(module degree, compressed degree). There is no fixed-polynomial unbounded-horizon or universal-polynomial claim.

All nonempty complete fibers remain infinite. The retained q_b changes by u*k along beta_k=beta_0+4yu*k, even when beta itself is eliminated. The fully explicit C=1 family is polynomially checked in its free parameter.

## Fresh evidence

Only the freshly authored and inspected `check_reduction.py` was executed. It uses the standard library, imports no prior checker, and runs no upstream source, Lean, counter interpreter, physical simulator, or saved schedule.

Passed: two complete baseline sparse-polynomial expansions; six variant expansions; 15 baseline embedding identities; 31 further generic elimination identities; 25 full baseline family assignments; 75 old common-shift assignments; 110 single-leaf perturbations rejected; 15 identities for the explicit infinite family; symbolic Pell identities for indices 0 through 8; seven 49-witness compressed compositions; and 63 full variant assignments. Exact source and checker hashes are in the receipts.

The all-exponent theorem still depends on the exact pinned mathlib constructive theorem pair. Finite checks are not described as a replacement for that theorem or as a new Lean build. No external independent review of this new packet is claimed.
