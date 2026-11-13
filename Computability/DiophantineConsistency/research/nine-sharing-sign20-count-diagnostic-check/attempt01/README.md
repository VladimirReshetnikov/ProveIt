# Sign20 count diagnostic: boolean conversion failure

Author-observed outer session `59172` exited 1. `beq_iff_eq` converted the
boolean tests to proposition equalities, but simp left comparisons of distinct
p-dependent expression constructors unsolved. Both count reports contain
`sorryAx`; no diagnostic object or postflight is claimed. The provider parent
was itself failed; its five earlier successful child objects were used.
The [independent failure audit](../../../reviews/nine-sharing-sign20-count-diagnostic-failure-independent/README.md) passed; the packet is frozen.
