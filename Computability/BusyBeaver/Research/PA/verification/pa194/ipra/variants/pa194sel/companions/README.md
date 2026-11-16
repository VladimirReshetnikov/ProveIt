# Companion selector tables

The [row generator](generate-rows.py) pins the delivered parent tables,
native labels, and ten archived selector overlays. These overlays combine
the existing selector transformation with PA194AD, PA194B, PA194HX,
PA194LC, PA194LC_C, and their timing variants. The proofs use the blank
start inherited from each parent at native control 74 and the terminal
control 254, represented in Lean by dense controls 0 and 194.

[`PA194GuardedSelectors.sameHalt`](PA194GuardedSelectors.lean) compares
the two exact tables at arbitrary model-valued clocks in `IΣ₁`. A
checked certificate identifies the unchanged rows, incoming history bits,
and selector exits. Each step of the parent matches one or three steps of
the selector machine.

From the repository root, use the recorded row provider for the chosen
parent and the checked [primary selector stage](../README.md). This example
checks the LC_C table and its selector overlay.

```sh
variants=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants
companions="$variants/pa194sel/companions"
bash "$companions/check-rows.sh" LCC /dev/shm/pa194lcc-controller /dev/shm/pa194sel-replay /dev/shm/pa194lcc-selector-rows
```

## Native iPRA derivations

The [native generator](generate-native.py) composes each checked selector
comparison with its parent's iPRA theorem. All ten exact overlays
have passed the full replay.

| Parent | Native SHA-256 | Lean theorem |
| --- | --- | --- |
| AD | `c16787eab6a8ec39d0964e2ccc1c052b4f2f5210b54720530463a295d3ab1fb6` | `PA194ADSELFinal.consistency_iff_literal_nonhalt` |
| AD_fast | `fc959c310d118ecbbe2fa76be58f85c7adb9b179fb264b0dea5fa7b450ba7c7f` | `PA194ADFastSELFinal.consistency_iff_literal_nonhalt` |
| B | `da905776f4ee249c5a0f695d53d57f6ba77a009c117639b7b110f8358982dcc9` | `PA194BSELFinal.consistency_iff_literal_nonhalt` |
| B_fast | `359e581cb13b0ccc40ff6fb4de0b849e065b9c1ee18f39a38d2a6356b02e16f9` | `PA194BFastSELFinal.consistency_iff_literal_nonhalt` |
| HX | `5d360c04ea9023cb9894cacc163959016c3927cccfa41cff16c239ea7db452e5` | `PA194HXSELFinal.consistency_iff_literal_nonhalt` |
| HX_fast | `a3957dbab299a65bb3a2f0d27cda9e28d57c218ea3c1121b522b38d3fa323008` | `PA194HXFastSELFinal.consistency_iff_literal_nonhalt` |
| LC | `eed3f48e464b2ac3bbf17260732d1bac0dce0e086da6ea6eb6a5143d528b4c51` | `PA194LCSELFinal.consistency_iff_literal_nonhalt` |
| LC_fast | `c5b776372d8535aef2382b1a51d68ca529bbc0c05be75e5575fa43fbc7e48ac3` | `PA194LCFastSELFinal.consistency_iff_literal_nonhalt` |
| LC_C | `cba995e86e6e3efee5c74bca2ade7b98adcc8be052d728c69484f4a01a23e9a6` | `PA194LCCSELFinal.consistency_iff_literal_nonhalt` |
| LC_C_fast | `786a71dd5ff25030ec243035b35f9f61eac466139180767c90d2ef4bd9feadba` | `PA194LCCFastSELFinal.consistency_iff_literal_nonhalt` |

Build the [shared machine transfer](../../../../../shared/isigma1-machine/ConPAMachineRelative.lean)
from a checked model stage such as [PA1944L](../../pa1944l/README.md).
Then run the native composition with the previously checked rows and the
parent theorem. The example uses the
[LC_C coverage and final stage](../../pa194lcc/README.md).

```sh
transfer=Computability/BusyBeaver/Research/PA/verification/shared/isigma1-machine
bridge=/dev/shm/pa194-machine-relative
bash "$transfer/check-relative.sh" /dev/shm/pa1944l-model "$bridge"
bash "$companions/check-native.sh" LCC /dev/shm/pa194lcc-selector-rows /dev/shm/pa194lcc-coverage "$bridge" /dev/shm/pa194lcc-selector
```
