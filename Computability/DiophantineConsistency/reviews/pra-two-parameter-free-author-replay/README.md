# Two parameter-free induction axioms: replay

`PRATwoParameterFreeInduction.PRA_proves_goal` eliminates two closed coded
Σ₁-induction axioms for arbitrary `Code 2` predicates whose bodies ignore
the universally bound induction parameter. It uses concrete zero/one tag
codes and candidate-PRA proofs of the two substitution identities. Goal
parameters are still allowed. It does not cover predicates depending on an
arbitrary shared induction parameter, additional predicate parameters, or
an arbitrary finite list of instances.

The author build passed at `/tmp/pra-two-parameter-free-author-r0y1e9ge`.
Private replay `/tmp/pra-two-parameter-free-independent-4kzy406x` and root
replay `/tmp/pra-two-parameter-free-independent-oh21jf32` passed. All four
source/object/full-log hashes matched the frozen manifest; each replay checked
all listed parent source/object pairs before and after. Root used the
independently checked 47-module provider
`/tmp/pra-after-preparation-merge-independent-blp1ky5k/lib`.

Replay: `python Computability/DiophantineConsistency/reviews/pra-two-parameter-free-author-replay/replay.py --parent /tmp/pra-after-preparation-merge-independent-blp1ky5k/lib`.
The parent manifest specifies the local graph being authenticated. Foundation
and Mathlib artifacts are inherited, not rebuilt here. Lean's classical
metatheory is used; the checks report `propext`, `Classical.choice`, and
`Quot.sound`, with no `sorryAx`.
