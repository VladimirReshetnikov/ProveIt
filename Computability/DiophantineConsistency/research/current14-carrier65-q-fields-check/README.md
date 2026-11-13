# Actual Carrier65 Q input fields

Outer session 5265 exited 0; the arbitrary-ring evaluation equalities and
actual polynomial degree bounds compiled, and the [independent terminal
audit](../../reviews/current14-carrier65-q-fields-terminal-independent/)
passed. This client proves evaluation equalities between the
audited standalone input syntax and the actual `Carrier65.core` fields `X`,
`c`, `a`, and `H`, followed by multivariate degree upper bounds 2, 5, 6,
and 6 at arbitrary integer ports. The generic syntax-weight provider and its
earlier failed attempt are independently audited and pinned; the `Carrier65`
object is a historical point pin. The no-Lean preflight and [independent
prelaunch review](../../reviews/current14-carrier65-q-fields-prelaunch-independent/)
passed.

This is not yet a Q-factor or whole-expression degree result. Binding these
four field bounds and the gamma variable bound to the generic degree-18
theorem and the audited cancellation identity remains a separate client.
