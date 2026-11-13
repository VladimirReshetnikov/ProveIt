# Conditional positive squared-parent to trace75 zero

`Trace75OldTracePositiveMap.positive_parent_zero` is Lean checked in every
IΣ₁ model. For arbitrary difference-ring ports, a positive natural valuation
of the explicitly defined squared-trace parent, natural representatives
`c,f,d,rank` matching the actual registers, `c,f>0`, a positive signed old V
and oldValue zero, it constructs a positive valuation making actual trace75
value zero. It derives `f=1+c*d` from the register identity and updates only
the T slot using the checked natural trace shift. No positivity premise is
added for d or rank.

This is conditional on an explicitly defined parent value and representatives;
it does not bind an existing selected graph or show halt supplies the premises.
It does not establish a halt iff or iPRA theorem. Accepted author check
`observations/positive-attempt02/` produced
`/tmp/trace75-oldtracepositive-7tv2174p/Trace75OldTracePositiveMap.olean`
SHA-256 `3827f85c28655115020d07835f6b58144b6c056c3fb6194f817b08f59e4e97d0`.
Attempt01's Lean proof compiled but the strict runner rejected an unused-simp
warning; source and diagnostics are retained. Direct provider objects were
pinned; transitive, package and dynamic ancestry remain inherited.
An independent source and receipt audit passed; no Lean replay was performed.
