# Positive isUFormula fixpoint membership

This actual `isUFormula` sigma client applies the concrete positive bit graph majorant to Foundation `FormalizedFormula.blueprint L`. The statements retain an explicit bounded `limSeqDef` hypothesis, a supplied sequence witness and its size bound. They do not construct a recursive-history witness or show a rho certificate or HA equivalence. The candidate-PRA theorem is obtained by sound model reasoning via completeness, with no candidate-PRA IΣ₁ assumption.

Replay: `python3 Computability/DiophantineConsistency/reviews/pra-fixbit-uformula-bound-author-replay/replay.py --parent /tmp/pra-after-negative-refactor-independent-kz_apq2h/lib`. The parent is the independently replayed 20-module graph; Foundation transitive dependencies are inherited with listed boundary anchors checked.
