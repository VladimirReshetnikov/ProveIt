# Post-merge IΣ₁ extraction and bounded-induction refresh

The author run rebuilt 49 affected/new modules against the root-accepted finite-paired provider, authenticating 92 unchanged local source/object parents before and after the build. Foundation and Mathlib are inherited. Author and root source snapshots, full logs and terminal states are preserved here.

Independent replay passed at `/tmp/pra-after-prenex-merge-independent-ae3zqp5q/lib` and `/tmp/pra-after-prenex-merge-independent-m_2gvh6i/lib`, matching every author source/object/full-log hash and parent authentication. Run `python Computability/DiophantineConsistency/reviews/pra-after-prenex-merge-refresh-author-replay/replay.py --parent /tmp/pra-paired-finite-independent-259vy7un/lib` from the workspace root.

New extraction modules: `PRAISigmaOneFiniteTranslation.lean` and `PRAISigmaOneFiniteTranslationChecks.lean`. New two-free-parameter modules: `PRATwoParameterPacking.lean`, `PRATwoParameterPackingChecks.lean`, `PRATwoParameterInductionTransfer.lean`, `PRATwoParameterInductionTransferChecks.lean`, `PRATwoParameterOneInduction.lean`, and `PRATwoParameterOneInductionChecks.lean`. Some Parsons modules were rebuilt because they were not authenticated by the previous parent manifest; the author state lists all changed or newly authenticated sources.

The extraction returns a finite list of actual Foundation Σ₁ induction formulas and an actual mapped proof over candidate PRA plus their induction axioms. It does not supply a general Σ₁ prenex/collection theorem. The two-parameter theorem eliminates one bounded-matrix induction instance; it does not establish general Parsons conservation. The separate HA proof-existence theorem for the maintained 14-variable equation was already complete.
