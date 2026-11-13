# Sign24 conditional bridge retry, attempt 01: partial success, outer failure

The author observed numeric outer session `97690` exit 1. Stage one,
`Sign24BridgeConditional`, compiled successfully with an axiom report listing
`propext`, `Classical.choice` and `Quot.sound`. Its conclusion assumes the
sign25 PolynomialBridge; it is not an unconditional sign24 bridge.

Stage two, `Sign24BridgeStaged`, passed dependency inspection but compilation
exited -6 with a Lean interpreter `memory_exception` under `-M2800`. No final
object or postflight was produced. Sampled peak RSS was 2,939,056,128 bytes
and minimum host availability 19,475,480,576 bytes; these point samples may
miss spikes. The precise cause of the interpreter exception is unknown.

The state, logs, and author-observed outer exit are frozen here. Independent
terminal audit requested. The reported Lean metatheory axioms are not iPRA
axioms. Inherited provider and point-observation qualifications remain.
