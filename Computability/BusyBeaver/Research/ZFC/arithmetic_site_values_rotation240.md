# Exact numeric meanings of Rotation240 instruction frames

[`ArithmeticSiteValuesRotation240`](../../Lean/BusyBeaver/ZFC/ArithmeticSiteValuesRotation240.lean)
evaluates the actual `SiteRotation240.start` and `target` syntax as complete
numeric tapes in every IΣ₁ model. It identifies the start with the canonical
entry frame, transports physical register writes, and rebases outgoing
targets to the checked catalogue's next control.

The identities retain state code 85, the 64-bit pointer margin and the
`167+extra` spare invariant. Increment changes one field and adds one spare;
positive decrement changes one field and adds one pointer-padding cell.
The latter preserves the spare count. Register values, extra spares and gaps
remain arbitrary internal values.

The [actual check](results/arithmetic-site-values-rotation240-verification.json)
passes 12 axiom probes and 14 typed callers with zero warnings and only
standard axioms. Source and audit took 3.019 and 2.573 seconds at default
proof limits, sharing 120 seconds with one thread and 4,096 MiB. The existing
Step and DispatchRebase objects supply the exact prerequisites; no dependency
family is rebuilt.

The [history](arithmetic-site-values-rotation240/history.json.gz) preserves
the first failed attempt and its narrow repair. An explicit equality for
the finite dispatch state's value lets the natural-number cast simplify
to state code 85. The theorem statements and proof limits are unchanged.
The [publication record](results/arithmetic-site-values-rotation240-publication.json)
binds the accepted source, audit, raw logs and direct guard.

This unit interprets instruction frames. Actual checker acceptance and the
concrete runtime theorem must still be composed with these identities to
obtain every instruction's binary endpoint. Attribution remains with
Mira-Cult, Jeff Ketchersid, Andrew James Wade and ProveIt.
