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
