# Actual C222 internal equality core: author validation

Author: `controller_certificate`. This is an author receipt, not an independent
review. I also authored the CProv222, actual constructor/history/row/template
dependencies. Their independent root/peer reviews remain separate. Only the
two new sources, private replay outputs and this packet's receipts were
written; accepted sources, shared objects and Git were unchanged.

The frozen main has 127 lines and the focused checks have 48. The complete
sources, finite Nat guide `KEqCodes222`, generic `Kalmar` source and execution
drivers were read before execution. Both new sources were reread afterward.

| File | SHA256 |
|---|---|
| `ValidatorEqualityCore222.lean` | `caa7d6c534c5f7a31ec6e5d314be364c57dcefe8d577b0eba86db0eaea4af9ce` |
| `ValidatorEqualityCore222Checks.lean` | `88439cf53e43f7d7bbc074eed0c34c1097ae72c5e476cb990f68252397cf79d8` |
| `validator-equality-core222-replay.json` | `95ea506509731f5fb3f698b929414c0d1a840883e6e1c8692953be9ebdd42893` |

All theorems range over an arbitrary `ORingStructure V` model of IΣ₁,
using the actual represented `ValidatorProvability222.CProv`. The five
public endpoints establish:

1. Equality reflexivity, `CProv (weq x x)`.
2. The helper, `CProv (wim (weq a b) (wal (wel a b) (weq a b)))`.
3. Specialization at that exact helper binder, in the reverse direction.
4. `CProv (ArithmeticTemplates254.rho7 a b c)`, derived from growG.
5. Membership vacuity, `CProv (ArithmeticSeedTemplates222.vrel a b c)`,
   under exactly `c≠a` and `c≠b`.

The first four have no extra positivity or freshness premises. In
particular zero and equal labels are legal. The fifth retains the actual
seed gates, permitting `a=b` and `c=0` whenever both gates hold. The name
`ArithmeticTemplates254.rho7` denotes the unchanged formula constructor;
its new C222 derivability is proved here, not assumed as a checker row.

The existing Nat proof is used only as a finite derivation pattern.
`KEqCodes222` is neither imported nor called. The implementation instantiates
generic `Kalmar.Der`, `deduction` and `sound` with the already checked
`cProv_classical` witness interface. Every MP application uses the new
major-first order. The small contraposition and existential-monotonicity
certificates use fixed finite hypothesis lists, not an external syntax or
model-completeness argument.

For reflexivity, growG at `r=wel x x` and rho1 yield the represented
existential of `∀r (x=x)`; actual rho6 then yields `x=x`. The helper follows
from growG and reflexivity. Quantified K, rho1, existential monotonicity of
the helper and rho6 supply helper specialization. Applying it to growG
derives rho7. Finally the fixed certificate `¬(A→B)→A` projects membership
vacuity from the actual helper-free seed witness. No interpretation or
truth of the seed matrix is a premise.

Focused checks expose every full formula, zero reflexivity, simultaneous
equal labels and zero in rho7, both legal seed edge cases, and the expanded
membership formula. A final Nat example recovers the actual `KCode222.C222`
rho7 theorem through the new internal endpoint and frozen `cProv_nat_iff`;
it does not invoke the prior Nat equality proof.

Only `ZFCinPA.ValidatorProvability222` is imported. The private overlay is
`/tmp/equality222-controller-0bdkt7ff`. Before and after execution the driver
reauthenticated 123 custom sources (95 Foundation), 408 recorded object
companions, 38 explicit external package/toolchain roots, and the exact
compiler/manifest. The input inventory hash is
`689b53312074117698b0b2510b1ba4e429f9e25725b5e556cc0c6c6fcab0754e`;
the recorded source snapshot is
`fa4d69613c35076c15f8746dc2efb145418c3bc3`.
Cached dependencies and the external boundary retain the accepted parent
receipt's scope; no fresh Foundation or whole-dependency replay is claimed.

The first fresh main/check pair passed using the exact 4.32.0 compiler with
`-M6000 -j1 -DElab.async=false`, in 3.03 and 2.01 seconds. Maximum RSS was
1,820,668 KiB. The main log is empty; all eight intended axiom reports list
only `propext`, `Classical.choice` and `Quot.sound`. There was no failed run
or source correction. Final free space was 1,156,788,224 bytes, above the
512 MiB reserve.

| Private object | SHA256 |
|---|---|
| main | `5d441ac53e6542bc55ebe8ee79971c1cd581536edf42fc19961044867ee48d52` |
| checks | `bbb59ac3362b2075ff2cf4f7ac7b6741e669b48a4192904ce37ae9dc8d272c99` |

The JSON preserves every prerequisite pin, source snapshot, command, log,
timing and output hash. This packet derives finite proof witnesses inside
the actual C222 checker. It establishes neither semantic seed validity nor
an internal equivalence between calculi, machine runtime, or the requested
HA equivalence. No HA inference rule was added.
