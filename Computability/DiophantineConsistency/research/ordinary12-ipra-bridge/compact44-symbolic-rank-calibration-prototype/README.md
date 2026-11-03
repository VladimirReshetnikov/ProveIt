# Symbolic compact44 controller calibration

`CompactActualRankCalibration.symbolic_rank_calibration` combines the proved
model-level unit for the actual symbolic `paramKernel rho` with the compact
controller-choice argument. For model `m,e,R0`, it explicitly assumes

```
2 * (590069 * 581197) < 581197^m
581197^e ≤ 581197^m.
```

It obtains a model-definable Boolean selector `δ` supported at positive
positions where the one-step and `581197^e`-step translates stay below
`581197^(m+1)`, and it gives the stated calibration congruence for any
`R0`. The model, exponents, selector and witness are internal to IΣ₁; the
theorem does not assert a standard external halting event.

This support is **abstract controller support**. The theorem does not prove
that these positions are safe dummy cells in a packed tableau, that the
symbolic `Gamma` is the actual packed-rank variation, that the selector can
be applied to the same compact word, or that any graph zero exists. It also
does not identify the retained K bytes or displayed coefficient or establish
an iPRA theorem. The two size/stride assumptions are not discharged here.

## Provider and source transformation

The earlier compact controller imports the full
`BusyBeaver.ZFC.ArithmeticCantor` package, but its source uses only `triangle`,
`triangle_succ`, and `le_triangle` from that namespace. The bounded
same-provider build extracts these definitions and their needed proof
`triangle_double` into `CompactControllerTriangle.lean`, and changes only the
import and namespace of the earlier controller-choice source. This avoids the
unrelated `Code254` dependency; it does not establish a global minimum
dependency closure. `check_extraction.py` verifies the exact source
transformation and text of the four extracted declarations; it is an external
source comparison, not a second Lean proof.

All four Lean stages actually exited 0 on the earlier symbolic-unit overlay.
The extracted triangle, alias calibration and exact-symbolic calibration
stages were warning-free. The mechanically adapted controller-choice source
emitted the two previously documented unused-section-variable and
unused-variable linter warnings, with no other warnings. The final theorem's
printed axioms are `propext`, `Classical.choice`, and `Quot.sound`, without
`sorryAx`. Exact source hashes, compiler commands, dependency lists, logs,
object hashes and terminal observations are retained under `observations/`.
The runner checks the four prior symbolic-unit stage objects before building.

This is an incremental single-author result on the existing symbolic-unit
provider, not a paired replay or a fresh authenticated project/package
closure. Package, transitive and dynamic ancestry, and between-check
mutations, remain inherited. The previously documented controller-data
warning is also inherited from the parent build.
