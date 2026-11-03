# Held displayed low-mask specialization

All three retained attempts failed: `attempt01` directly specializes `CompactConcreteMask.concrete_recipe`, while `attempt02` specializes the checked variable-radix `BFSDisplayedLowGeneric.low_recipe`. A third uses the symbolic radix to factor the proof. In each case Lean hit the 3-GiB kernel memory cap when elaborating/checking the fixed low-mask equality. Any axiom reports mentioning the resulting `low_eq` reflect an incomplete proof and are not accepted iPRA results. Exact sources, runners, diagnostics and sampled resources are retained in the corresponding observation directories.

This is not a proof that the displayed low-mask sum equals `CompactSymbolicPorts.lowNat`. The [generic variable-radix identity](../ten-positive-80-bfs-low-generic/README.md) does pass; a sufficiently opaque fixed-radix application or a different small composition remains to be checked. PDF/TeX/JSON file semantics remain external.
