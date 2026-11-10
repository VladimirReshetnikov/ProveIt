# Sign25 no-alias opacity retry: first-stage failure

Author-observed outer runner session `12392` exited **1**. The native source
was byte-identical to the successful child in the prior no-alias attempt, but
this run's native dependency scan exited 0 and its compile exited -6 with an
interpreter memory exception under `-M2800`. No object, subsequent wrapper
stage or final postflight was produced. The sampled monitor reported no stop
reason or errors; those observations do not rule out transient spikes.

The earlier native child remains a separately audited partial result, not a
success for this runner. The precise cause of this run's exception is unknown.
Provider point observations and the inherited ancestry qualifications remain;
there is no standard or translated endpoint, Lean degree, external JSON or PDF
result. Captured logs and state come from the isolated attempt and numeric
outer exit is recorded separately.
The [independent terminal audit](../../../reviews/nine-sharing-sign25-endpoint-no-alias-retry-terminal-independent/README.md)
checks the retained failure evidence.
