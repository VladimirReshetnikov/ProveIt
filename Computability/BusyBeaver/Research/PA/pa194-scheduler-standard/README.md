# Standard PA194 scheduler binding

`PA194SchedulerStandard.lean` proves `advance_standard`: for arbitrary finite
input codes evaluated on natural-number arguments, the modeled scheduler's
fetch, triangular command decoding, continuation and all register updates
reproduce `PA194CommandRun.advance` exactly. The equality includes SHIFT's
halting branch, both MP branches, AX, and the candidate counter. The proof
uses the separately checked standard bindings for AX and SHIFT/MP and proves
the fetch/parser component equations.

This is an equality for standard natural inputs. It does **not** identify the
modeled scheduler's nonstandard iteration with a literal PA194 controller or
machine trace. It also does not identify target provability with internal PA
provability or prove a PA194/Con(PA) implication.

Run from the repository root with the matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-scheduler-standard/check.sh
```

The final module was rebuilt against freshly checked standard command and
scheduler-code objects and previously checked prerequisites. A full nested
replay of this wrapper has not yet been completed. Its printed axiom
dependencies contain no `sorryAx`.
