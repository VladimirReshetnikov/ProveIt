# Direct conditional exact Carrier65 degree

Outer session 24682 exited 1: imports were compatible and the upper replay
compiled, but the final proof left a function/`axisVars` mismatch. No final
object or postflight exists. The [independent failure audit](../../reviews/current14-carrier65-degree-direct-failure-independent/)
passed. This two-stage client replays the audited multivariate upper bound in the
audited whole-diagonal provider context, then proposes to transport the
all-equal diagonal lower bound directly through a polynomial evaluation ring
homomorphism and `Carrier65.value_map`. Its intended result is
`(Carrier65.polynomial p).totalDegree = 150` when p0 is nonzero.

The client avoids the combined current-expression import that was present in
both independently audited `Matrix.map` collision failures. It does not
claim the precise source of that collision is known. It does not yet assert a
current-port specialization, expression theorem, or TeX/PDF semantics. The
audited upper replay, diagonal point object, prior failures, historical point
providers and inherited equal-byte overlay qualification are guarded. The
no-Lean preflight and [independent prelaunch review](../../reviews/current14-carrier65-degree-direct-prelaunch-independent/)
passed.
