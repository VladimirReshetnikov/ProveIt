# Signed comparison-base lift: 78-guard integer quartics

This separate candidate keeps the literal 667-coordinate/585-row body
and 78 guards. It removes only the raw657/CV303 q4minus1 guard from
the frozen 79-guard family. Every stored polynomial is the sum of
squares of its complete quadratic residual list, over unrestricted
integers. Full collected coefficients and signed inverses are included.

| Variant | Integer variables | Quadratic rows | Quartic terms | Coefficient height |
|---|---:|---:|---:|---:|
| unprojected | 901 | 663 | 4737 | 63905862 |
| support4 | 642 | 404 | 5565 | 63905891 |
| support8 | 616 | 378 | 8582 | 2445790974704 |
| support16 | 614 | 376 | 8677 | 2445790974704 |
| support32 | 613 | 375 | 10013 | 2445790974704 |

All five complete equations have exact degree 4. Each profile saves
three integer variables, one quadratic row and 15 collected monomials
against its matched frozen 79-guard profile, at the same height.

The source-zero equivalence is **nonpointwise**. After reversing the
entire signed projection and restoring all 592 raw wires over Z, use
the signed-B index/residue proof to orient the main roots and moduli.
Then lift q4 and the comparison witnesses using the existing U,V,
fixing every one of the 78 guarded values. Supply three fresh Legendre
witnesses for the *new* positive q4 value to obtain a literal zero of
the frozen 904 equation. Only then apply its pointwise 21-sign theorem
and fresh 63 witnesses to reach the frozen 967 equation. The original
q4 value need not be nonnegative; no old q4 triple is copied.

BRIDGE904.json specifies the 62 free-witness recipes, all read from
the original tuple; its complete 141-gate/46-constraint use ledger;
the 78 copied triples; and the three precise fresh q4 witness slots.
PROOF.md supplies the ordinary argument, with the accepted signed-B
theorem and existing-unit lift pinned in SOURCE_PINS.json. The
independent checker verifies the entire original source boundary,
all coefficients, all inverse identities and every guard position.
The authenticated optimizer is used only by build.py.

```sh
python -B Computability/DiophantineConsistency/candidates/projected-radius-comparison-base/build.py --check
python -B Computability/DiophantineConsistency/candidates/projected-radius-comparison-base/check.py
python -B -O Computability/DiophantineConsistency/candidates/projected-radius-comparison-base/build.py --check
python -B -O Computability/DiophantineConsistency/candidates/projected-radius-comparison-base/check.py
```

The four receipts and closed MANIFEST.json are included. Existing
families and the canonical page remain unchanged. These are ordinary
source-zero and full finite algebra certificates; no new Lean or
internal-ZFC theorem is claimed.
