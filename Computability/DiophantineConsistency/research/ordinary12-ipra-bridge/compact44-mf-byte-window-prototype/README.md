# Byte windows of the once-shifted symbolic high port

`CompactShiftedHighByteWindow.byteAt` is a closed local-window function of
the checked 8,808-digit `shiftedDigits` list. `byteAt_eq` proves, for every
natural `j`, that it equals
`((CompactFixedBeta.betaNat + CompactSymbolicPorts.highNat) / 256^j) % 256`.
`bytes` maps that function over `List.range 73759`; the checked length,
lookup and `bytes_windows` theorems give the matching window for every
in-range index. The underlying shifted-digit theorem includes the beta
shift **once**. No equality to a retained file or gzip stream is stated.

The bounded mixed-provider author run `observations/attempt02` exited 0 in
2.244 seconds without warnings or `sorryAx`; direct dependency/companion
guards and the separately inventoried generic byte provider were unchanged.
Source SHA-256:
`851c763f5b6e4ea48ffea96fba6d03e71e676a83bfe6857e37b4b254c0c5f082`;
object SHA-256:
`ccd3c89e8c4ae8eb573e0484fd5df7bee36601dbadd53493e8a5d2231b052fd6`.
Named reports `[propext, Classical.choice, Quot.sound]` are Lean metatheory
dependencies, not iPRA axioms. Attempt01 failed at recursion depth when a
broad simplifier unfolded the byte function; its source/log/receipt are
retained. Attempt02 uses only the required list-index simplifications.

This author-side result inherits shifted-digit, symbolic, package and
dynamic ancestry; it is not a paired replay or complete ancestry audit.
The separate upper bound and generic reconstruction are needed for a
byte-list decoding theorem. File/Lean transcription, gzip, parent-to-
supplement, PDF and iPRA correspondence remain outside this theorem.
