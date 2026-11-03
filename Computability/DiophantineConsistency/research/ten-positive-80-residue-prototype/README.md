# Signed residue of a square multiple

`Direct80Residue.square_multiple_residue` proves in every IΣ₁ model that, for natural `F,c,u` and arbitrary elements `w,x` of the model's difference ring, `F>0`, `x=F²w-c` and `x²=u²` imply `SignMod F u c`. The proof represents the possibly signed factor by a pair of natural numbers, uses the magnitude of the resulting difference, and derives the modular statement without assuming either sign.

This is a conditional algebra lemma, not yet a binding to the 80-row graph, a folding theorem, a halt theorem, or a proof inside iPRA. The exact graph shape and common choice of magnitude must be connected separately.

The guarded author check in `observations/attempt03/` succeeded without diagnostics, producing `/tmp/tenpositive-80residue-wmjxeubh/Direct80Residue.olean` with SHA-256 `89439c2c076fa9b652dce331652e13bdb6ad3a896cadf82a4d445dbb4288ccf4`. Attempts 01 and 02 failed and remain recorded. Printed Lean axioms are `propext`, `Classical.choice`, and `Quot.sound`. The runner pins its listed prototype objects and one direct inherited provider; it does not inventory all inherited project, package, dynamic or source-to-object inputs. Resource monitoring is sampled and no paired replay is claimed.
