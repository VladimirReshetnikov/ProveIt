# PRA nonzero-bit recursion: independent replay

29 October 2026. I read the complete pair and checked the actual terms and
binders. The candidate PRA proves `nonzero(0)=0` and
`nonzero(succ x)=1` for its designated code, using the defining recursion
and composition equations in arbitrary equality models, followed by
completeness. This is a prerequisite for the missing Q order clause.

A fresh independent Lean 4.32 build with `-M6000 -j1 -DElab.async=false`
matched both author objects and complete logs; six axiom reports contain
only `propext`, `Classical.choice`, and `Quot.sound`. The [evidence](pra-nonzero-root-replay/)
retains author and independent outputs and earlier scratch attempts; an
admitted scratch probe is not part of the final source. Current-source PRA
parents and inherited Foundation/Mathlib objects were reused without a full
transitive rebuild. The order clause and conservation remain open.
