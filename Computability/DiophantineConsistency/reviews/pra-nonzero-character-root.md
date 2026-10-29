# PRA nonzero characterization: independent replay

29 October 2026. I read the theorem pair and checked that its closed sentence
states the actual code's `nonzero(x)=1 ↔ x≠0`. The proof uses predecessor
exhaustion, successor nonzero and the nonzero recursion in arbitrary equality
models of the candidate PRA, then completeness. It therefore covers
nonstandard elements and does not infer derivability from natural-model truth.

An independent Lean 4.32 build under `-M6000 -j1 -DElab.async=false` matched
both author objects and complete logs. Four axiom reports use only `propext`,
`Classical.choice`, and `Quot.sound`. The [evidence](pra-nonzero-character-root-replay/)
preserves the current-source exhaustion refresh, final pair, earlier scratch
attempts and independent driver, state and logs; admitted scratch probes are
not part of the final source. Earlier PRA and inherited Foundation/Mathlib
objects were reused without a full transitive rebuild. Additive witness
cancellation, the Q order clause and PRA conservation remain open.
