# Sign17 corrected-axis root binding: partial failure

Author-observed outer session `66650` exited 1. Four ingredient stages passed;
the binding stage failed because polynomial constants and integer casts were
not normalized together, and the expanded ring proof hit Lean's memory limit.
No binding object or postflight exists and no binding theorem is claimed.
The [independent failure audit](../../../reviews/nine-sharing-sign17-axis-root-binding-corrected-failure-independent/README.md) passed; the packet is frozen.
