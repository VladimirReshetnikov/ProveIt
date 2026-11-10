# Sign24 bypass bridge, attempt 01: failure

The author observed numeric outer session `33816` exit 1. Dependency
inspection succeeded but compiling `Sign24BypassPolynomialBridge` exited -6
with a Lean interpreter `memory_exception` under `-M2800`. No bridge object
or final postflight was produced. The sampled monitor recorded no stop reason,
peak session RSS 2,937,835,520 bytes and minimum host availability
19,481,739,264 bytes; transient spikes may be missed. The precise cause is
unknown. The state, logs and separately observed outer exit are frozen here.
Independent failure audit requested; provider point-observation and inherited
ancestry qualifications remain.
