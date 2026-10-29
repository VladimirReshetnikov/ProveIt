# PRA successor and addition: independent replay

29 October 2026. `PRAAddOne.PRA_proves_addOne` is a closed Foundation proof
that the candidate PRA theory derives the universal equation between its
literal addition-by-one term and its primitive successor. The proof derives
composition, projection and recursion equations in arbitrary equality models
of the theory, proves the equation in all those models, and applies the
existing completeness theorem. It does not infer derivability from truth in
only the standard naturals.

I read both files and independently rebuilt them with Lean 4.32 and
`-M6000 -j1 -DElab.async=false`. Both objects and complete logs match the
author's final build; six axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. The [replay evidence](pra-add-one-root-replay/)
includes all author snapshots and logs, including intermediate admitted probes
9–11, which are not part of the final source, plus the independent driver and
results. Previously checked project parents, the reviewed Foundation overlay,
and cached Mathlib objects were reused without a full transitive rebuild.

This is a derivation in the candidate theory, not yet a proof of its
compatibility with a standard PRA presentation, a conservation theorem, or the
requested consistency equivalence.
