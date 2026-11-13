# Signed free-J residual transport in arbitrary arithmetic models

`FreeJSignedTransport.lean` ties the exact 95-row free-J residual to a
universal ring identity. For any integer four-port tuple `p`, any model `V` of
IΣ₁ and any model-coordinate assignment `v`, its
`actual_unpolarized_zero` derives the following equation in the difference
ring from `InternalZero (literal p) v`:

```
w = n + z, r = 1 − q, h = r*w² + q*z² − 1
b = 2*r*w, A = d*h + q*r
A² − d*q*b² = 0.
```

Here `q`, `d`, `z` and `n` are the exact evaluated graph expressions selected
by `parts`, not new assumed variables: respectively the graph's strong norm
coefficient, `c⁴`, its signed residual variable and the actual coordinate n.
`graph_residual_shape` checks the graph-to-polarized-expression identity by
reflexivity; `polarized_eval` preserves signed evaluation; the existing
universal `polarization_identity` supplies the final implication. No β bound,
rank bound, port calibration, quotient or divisibility premise is inserted.
The theorem does not give denominator integrality, descent termination, a
fixed-port checker bridge or an internal iPRA proof.

The bounded paired replay's actual outer session 94351 exited 0; each Lean
child and each `--deps` invocation also exited 0, both objects and the three
axiom reports matched, and neither reported `sorryAx` nor warnings. The
[receipt and actual terminal observation](../../../reviews/free-j-signed-transport-replay/)
retain exact source, compiler, provider-state and artifact hashes. The
[70-source parent](../../../reviews/ordinary12-coexistence-pair-independent-audit/CHECK.json)
had a separate successful complete artifact audit. The replay compares that
parent before and after, but does not independently rerun the parent's full
artifact audit. The Foundation build wrapper's outer exit was not captured;
package-transitive and dynamic ancestry remain inherited.

The first exploratory run, session 77592, actually exited 1: generic
`evalRing` simplification left an unsolved composite-expression goal, and a
rewrite failed on an associated ring expression. Its source is retained in
the review packet; the tool response was truncated and the full output was
not saved. The second attempt, session 95717, actually exited 1; its complete
source and log are retained. Session 57415 then actually exited 0 with two
style warnings, retained in `attempt03.log`. The final paired source removes
those style warnings without changing the theorem statement. The receipt is
for the final source, not any failed attempt.
