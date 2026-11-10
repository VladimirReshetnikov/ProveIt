# Carrier65 graph-to-current-expression composition

Outer session 31915 exited 1: the client omitted the direct import defining
`Expr.evalRing`, so its semantic statements did not compile and no object or
postflight exists. The [independent failure review](../../reviews/current14-carrier65-dag-expression-failure-independent/)
passed. Its no-Lean
preflight and [independent prelaunch review](../../reviews/current14-carrier65-dag-expression-prelaunch-independent/)
passed. It replays the existing
`ObjectCurrentEquation2011.evalRing_expressionAt` proof from source in this
provider context, then composes it with the independently audited arbitrary-ring
graph-to-`Carrier65.value` equality. The final proposed theorem packages that
expression equality together with topology, 65 live binary operations, and
the 16 addition / 12 subtraction / 37 multiplication split.

The immediate semantic provider is an audited successful attempt. Its graph
and count provider consists of successful compiled children of an earlier
failed outer attempt; that failure and its independent review remain pinned.
The current-expression syntax object and underlying `Carrier65` are historical
point-pinned providers; this is not a full transitive import trace. The theorem
would establish a circuit upper bound in the specified integer-leaf metric,
not a minimality or degree result, and not Lean interpretation of TeX/PDF.
