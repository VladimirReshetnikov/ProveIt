# Retained-coefficient quartics with a signed comparison base

This separate raw sibling retains all 1259 original variables and all
1177 quadratic source rows verbatim, adding the same 78 guards as the
compact signed-comparison-base candidate. Every equation is the sum
of squares of its entire quadratic residual list over unrestricted
integers. Full collected polynomials and signed inverse certificates
are included.

| Variant | Integer variables | Quadratic rows | Quartic terms | Coefficient height |
|---|---:|---:|---:|---:|
| retained | 1493 | 1255 | 4981 | 427 |
| support2_affine1 | 846 | 608 | 3813 | 4750 |
| support2_affine2 | 701 | 463 | 5575 | 737653 |
| support4_affine2 | 637 | 399 | 8925 | 737653 |
| support8_affine2 | 623 | 385 | 8889 | 938261 |

All complete equations have exact degree 4. The 623-variable endpoint
saves three integer variables and one row against the matched frozen
626-variable profile, at the same height 938261. The 637-variable
profile has height 737653. Previous candidates remain unchanged.

BRIDGE901.json is a literal integer-zero bijection into the compact
901 equation: restrict to the 667 retained raw values and copy all
78 guard triples; reverse the 592 unique affine integer recipes.
No new witness, sign assumption or body normalization is required
for that first map.

LIFT904.json specifies the subsequent **nonpointwise** reconstruction.
At the complete 78-guard source, signed-B index recovery orients the
main pairs. Lift q4 and comparison witnesses with the existing U,V,
then reevaluate the 141 affected gates. All 78 guarded values remain
fixed, so their old triples are copied. Three fresh witnesses guard
the *new* positive q4 in the literal frozen 904 equation. Only after
that zero exists is its pointwise 21-sign theorem used to supply
63 additional witnesses into literal 967. The original q4 value may
be negative; the comparison lift does change body values.

The independent checker verifies every original/restored row, all
guard positions, the complete snapshot recipes/use ledger, all
collected coefficients and every signed inverse. The full compact
checker, including signed-B author/independent peer and frozen904
checks, is rerun in each mode. Only the producer imports the pinned
optimizer.

```sh
python -B Computability/DiophantineConsistency/candidates/retained-radius-comparison-base/build.py --check
python -B Computability/DiophantineConsistency/candidates/retained-radius-comparison-base/check.py
python -B -O Computability/DiophantineConsistency/candidates/retained-radius-comparison-base/build.py --check
python -B -O Computability/DiophantineConsistency/candidates/retained-radius-comparison-base/check.py
```

PROOF.md states the exact map order. All four receipts and the closed
MANIFEST.json are included. These are ordinary mathematical/source
and full finite algebra certificates. No new Lean/internal-ZFC result
or change to the canonical page is claimed.
