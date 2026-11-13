# 95-gate Lean equivalence draft: numeral-evaluation preparation

This uncompiled source keeps all declarations and theorem statements from the independently reviewed original draft. It adds `Expr.evalRing_ofNat` and `Nat.cast_one` to the two algebraic simplifiers, prompted by the separate readable shared07 proof failing on unreduced `Expr.evalRing v 1`. No Lean guard or theorem is claimed; this tactic-only source change requires independent review and a guarded run. The external 95-gate JSON/file, degree and iPRA endpoint bindings remain separate.
