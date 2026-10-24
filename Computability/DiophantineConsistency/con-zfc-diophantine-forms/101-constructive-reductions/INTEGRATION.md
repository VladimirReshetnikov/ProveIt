# Integration notes for ProveIt

## Suggested treatment

Add this packet as a new proposal or construction entry. Do not silently overwrite its immediate predecessors: they retain useful advantages in other measures. Keep the seven final polynomials and their domains separate in the index.

The primary integer formula is `integer14/crt14_degree540.json`. The direct `integer977` equation is the strongest new small-coefficient quartic in this packet. The nine-variable entry should retain both the 420-operation original31 form and the 428-operation compact54 form because their coefficient costs differ materially.

## Comparison rows

| Branch | Immediate inspected predecessor | New endpoint |
|---|---|---|
| Original31 simple, positive domain | 9 variables; degree 1,474,688; 449 operations | 9 variables; degree 1,472,168; 420 operations |
| Original31 complete radical, positive domain | 9 variables; degree 999,518; 1,086 operations | 9 variables; degree 997,810; 1,057 operations |
| Compact54 simple, positive domain | 9 variables; degree 1,628,768; 434 operations | 9 variables; degree 1,626,248; 428 operations |
| Fourteen-integer centered norm | degree 696; 150 operations | degree 568; 147 operations |
| Fourteen-integer lower degree | degree 652; 230 operations | degree 540; 160 operations |
| Synchronized direct, nonnegative domain | 522 variables; degree 4; 20,225 monomials; height 83,900,628 | 495 variables; degree 4; 15,377 monomials; height 83,867,632 |
| Synchronized direct, unrestricted integers | 2,088 variables; degree 4; 26,791 monomials; height 83,901,150 | 977 variables; degree 4; 24,632 monomials; height 83,869,250 |

The other inspected fourteen-integer norm at degree 792 and 137 operations remains smaller by operation count. Smaller-variable unrestricted-integer constructions also remain distinct alternatives. No comparison in this packet proves an absolute lower bound.

## Proof status wording

Suggested description:

> Explicit ordinary polynomial with a compositional ordinary proof, formalizable in ZFC, that its unsolvability in the stated domain is equivalent to Con(ZFC). The new reductions are accompanied by exact finite algebraic certificates and reconstructible coefficient data. Named inherited semantic calibrations are retained. No new end-to-end Lean/Rocq theorem or encoded object-language ZFC derivation is supplied.

Do not shorten that to “fully formally verified polynomial.” Python verification, a mathematical existence proof, and a proof object checked in a foundational kernel are different deliverables.

## Files and dependencies

The main TeX source includes `../integer14/report_section.tex`, `../nine/report_section.tex`, and `../direct/report_section.tex`. Preserve that relative structure or update the three input paths if merging into another report. No external image or bibliography download is needed to compile.

All Python checks use the standard library. `verify_all.py` runs in a disposable copy and rebuilds the final artifacts. Component builders may generate useful intermediate variants; these are not additional claimed final equations. The new natural quartic is retained under `equations_v3/cap64` for compatibility with the source certificate paths.

The older archived calibration pins are intentionally preserved. The main comparison snapshot identifies which proposals were inspected; it does not silently rebase every inherited theorem to that commit. Any later replacement of a calibration source should be reviewed as its own dependency change.

## Remaining formalization work

The packet identifies tractable next statements: the uniform coefficient-layout translation, the position-zero mask, the four-root separation with both exceptional branches, exact norm degree certificates, the 170-guard domain theorem, and the final C222-to-polynomial composition. A future formal endpoint must bind actual polynomial coefficients and domains, rather than certify only a generic construction schema or a successful script run.
