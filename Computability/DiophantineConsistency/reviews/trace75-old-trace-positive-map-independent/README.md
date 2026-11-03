# Independent review: positive defined-parent to trace75 map

**PASS.** In an IΣ₁ model, p is an arbitrary difference-ring-valued port
tuple, and v,c,f,d,r are model naturals. The theorem assumes every v slot is
positive, c>0 and f>0, exact casts of c,f,r to the actual trace75 registers,
and an exact cast of d to `2*Delta*(ι(v 3))²*c³*E`. It also assumes strictly
positive signed `oldV` and zero `oldValue` for the explicitly defined parent.
No separate positivity assumption on d or r is added.

The proof derives `f=1+c*d` from the actual register identity and obtains a
positive model-natural T from the natural trace-shift theorem. Internally it
updates only slot 4, proves the cast of that updated valuation is the ring
shift, and applies the full-output ring identity. The theorem exports existence
of a positive valuation with actual `value75` zero at the same p; it does not
export the internal coordinate equality. It does not bind the defined parent
to a selected old graph or show that halting supplies the hypotheses, and it
does not establish a halt iff or iPRA result.

The accepted `research/trace75-old-trace-positive-map-prototype/observations/positive-attempt02/`
terminal SHA-256 is `f6d7ed97af49e206bfd301debac28f06157cef8f3dc9f3c0a21ccf0103ba40e4`;
its regular object `/tmp/trace75-oldtracepositive-7tv2174p/Trace75OldTracePositiveMap.olean`
has SHA-256 `3827f85c28655115020d07835f6b58144b6c056c3fb6194f817b08f59e4e97d0`.
Source, copied source, runner, exact axiom report, twelve input hashes, the
first selected objects for both direct imports and resource samples were
checked. Attempt01's Lean process exited 0 and produced an object, but the
strict runner rejected its unused-simp warning; that attempt is excluded. The
accepted source removes only the unused simp argument. Tool exit 0 is
author-reported; no separate outer receipt or independent Lean replay is
claimed. Full transitive, package, historical and dynamic ancestry remains
outside this review.

`check.py` SHA-256 `66f5a40816979cf1fa09c618a3f41542df8c93db184ce4b6d067b2518ac7097c`;
`result.txt` SHA-256 `57c2de6cafd5ed4eb08b710fc4323b75d02e4bcc6fc021f86cbd7f2256d16ab6`.
