# Independent terminal review of each-slot extraction

The author-recorded first outer session **12176 exited 1**. Its dependency scan
passed, but Lean reported an unknown constant for the expression
`internalZero_iff.mp`; no object was produced. The retry changed only this
proof application to `(internalZero_iff _ _).mp`, preserving the exact
original theorem statement. Its author-recorded session **32937 exited 0**;
both dependency and compile records have exit 0, with an empty compile log
and no warnings or axiom report.

The checked theorem says that in a model of IΣ₁, a zero of the 38-witness
seed at distinguished input 1 makes the literal residual at **each index in
Fin 29** evaluate to zero in the model difference ring. It is generic in the
four integer ports and needs no model-natural port-cast hypothesis. It does
not by itself establish static gate equations, five norms, a graph/source
bridge or an iPRA endpoint.

`check.py` independently compares the theorem statement with the original
draft, verifies the one-line proof delta, source snapshots, both sets of logs,
the successful object, the shared compiled `Norm38SlotsBase` provider, 100
direct guard slots and 1,076 overlay links per attempt. The first failed run
did not reach a successful post-compile guard check; this review checked its
recorded guards against current files. The successful run's output object
remains in the temporary provider, SHA-256
`2e3d38650deab38173769dc3a5e75e0c4ce992d647868bab04ac74c8855879da`.

Both outer receipts are post-hoc author records, not raw transcripts or
independently observed historical exits. No Lean process was run by this
review. Inherited provider ancestry, between-observation changes and sampled
resource limitations remain.
