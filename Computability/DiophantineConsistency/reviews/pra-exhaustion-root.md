# PRA predecessor exhaustion: independent replay

29 October 2026. `PRAExhaustion.PRA_proves_exhaustion` produces a closed
Foundation derivation in the candidate PRA theory that every element is zero
or the successor of its coded predecessor. The proof uses the actual
primitive-recursion equation and quantifier-free induction in arbitrary
equality models, then completeness. It is not a standard-model-only argument.

I read the pair and independently rebuilt it using Lean 4.32 with
`-M6000 -j1 -DElab.async=false`. Both objects and complete logs match the
author build; all five axiom reports use only `propext`, `Classical.choice`,
and `Quot.sound`. The [replay evidence](pra-exhaustion-root-replay/) preserves
the driver, state, logs and all author attempts, including admitted scratch
probes 1 and 9–10 which are not in the final source. Checked project parent
objects and the existing Foundation/Mathlib cache were reused, not fully
rebuilt. Compatibility with standard PRA and conservation remain open.
