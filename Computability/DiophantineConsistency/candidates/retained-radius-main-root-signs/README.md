# Retained-coefficient 79-guard integer quartics

This separate low-height sibling keeps all 1259 original raw variables
and all 1177 quadratic source rows, coefficient for coefficient. It
adds exactly the same 79 guards as the compact 904-variable sibling.
Each stored equation is the sum of squares of its complete quadratic
residual list, over unrestricted integers. Every expanded polynomial
is included in full.

| Variant | Integer variables | Quadratic rows | Quartic terms | Coefficient height |
|---|---:|---:|---:|---:|
| retained | 1496 | 1256 | 4995 | 427 |
| support2_affine1 | 849 | 609 | 3827 | 4750 |
| support2_affine2 | 704 | 464 | 5590 | 737653 |
| support4_affine2 | 640 | 400 | 8940 | 737653 |
| support8_affine2 | 626 | 386 | 8904 | 938261 |

All five complete equations have exact degree 4. The 626-variable
endpoint has fewer integer variables than the older retained 689
profile, while keeping its coefficient height 938261. The 640-variable
profile has smaller height 737653. The older packets remain unchanged.

The raw 1496 equation and the compact 904 equation have an exact
integer-zero bijection: restrict the raw body to its 667 retained
coordinates and copy all 79 triples. Reverse all 592 unique affine
integer recipes to recover the raw body, and copy the same triples.
No new witness or sign proof is needed for that bijection. Only after
reaching a literal 904 zero does the frozen pointwise 21-sign theorem
supply 63 fresh Legendre witnesses into the literal frozen 967 equation.
No body normalization occurs in either of these two maps.

BRIDGE904.json records the complete retained-coordinate selection and
the entire 1256-row partition. BRIDGE967.json records the composed map,
all copied guard triples and the exact 63 fresh target slots. check.py
independently verifies all original/restored rows, the complete domain
ledger, all guard identities and every coefficient and signed inverse.
The authenticated optimizer is used only by build.py. The full compact
checker, including its pointwise-sign and frozen967 checks, runs in each
independent mode as well.

```sh
python -B Computability/DiophantineConsistency/candidates/retained-radius-main-root-signs/build.py --check
python -B Computability/DiophantineConsistency/candidates/retained-radius-main-root-signs/check.py
python -B -O Computability/DiophantineConsistency/candidates/retained-radius-main-root-signs/build.py --check
python -B -O Computability/DiophantineConsistency/candidates/retained-radius-main-root-signs/check.py
```

PROOF.md states the integer maps and their dependency order. All
normal/optimized regeneration and independent verification receipts
are included. MANIFEST.json seals the complete packet. These are
ordinary mathematics and full finite algebra checks; no new Lean or
internal-ZFC result is asserted. The canonical page is unchanged.
