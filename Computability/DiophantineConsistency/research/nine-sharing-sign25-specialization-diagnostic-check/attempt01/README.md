# Sign25 typed specialization diagnostic: partial failure

The author observed outer session `13751` exit **1**. The first generic
theorem, the typed sentence/equality and the typed-sentence-plus-bridge
import-only stage each compiled with child exit 0 and object hashes recorded in
the state. The fourth module passed dependency inspection but exited -6 with
an interpreter memory exception under `-M2800` while compiling the module
containing `#check` of the typed standard assertion and local attributes. The
specialized proof `#check` and final postflight were not attempted.

The successful prefix is evidence for those diagnostic modules only, pending
independent audit; it does not establish the endpoint. The failure occurred
before proof-term specialization in this run, but does not isolate the exact
failing command from the preceding module setup or rule out import/resource
variation. Point-time guards, sampled memory monitoring, inherited provider
ancestry and earlier successful-child qualifications apply. No Lean degree,
external JSON or PDF binding follows. Copied state and logs are retained here;
`outer-result.json` separately records numeric outer exit. The [independent
partial terminal audit](../../../reviews/nine-sharing-sign25-specialization-diagnostic-terminal-independent/README.md)
checks those results and their qualifications.
