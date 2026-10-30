# Post-fixed-goal merge candidate-PRA refresh

The author run rebuilt 31 modules against `/tmp/pra-two-parameter-free-independent-oh21jf32/lib`, and authenticated 159 unchanged local source/object parents before and after the build. Foundation and Mathlib are inherited from that provider. Its source snapshots, full logs, hashes, and driver are in this packet.

Run `python Computability/DiophantineConsistency/reviews/pra-after-fixed-merge-refresh-author-replay/replay.py --parent /tmp/pra-two-parameter-free-independent-oh21jf32/lib` from the workspace root. Two separate replays passed at `/tmp/pra-after-fixed-merge-independent-fcror0pc/lib` and `/tmp/pra-after-fixed-merge-independent-vpyarv0n/lib`, each matching all 31 source/object/full-log hashes and the parent authentication. Their terminal state records are preserved in this packet.

The finite-list endpoint in this packet concerns `Code 2` predicates which ignore the induction parameter. It does not establish conservation for arbitrary parameter-dependent induction or all Parsons proofs. The separate HA proof-existence theorem for the maintained 14-variable equation was already complete before this checkpoint.

The four new source files are `PRAFiniteInductionTagCodes.lean`, `PRAFiniteInductionTagCodesChecks.lean`, `PRAFiniteParameterFreeInduction.lean`, and `PRAFiniteParameterFreeInductionChecks.lean`. The four upstream-updated sources included in the refresh are `HerbrandFixedGoalWeakening.lean`, `HerbrandFixedGoalExtraction.lean`, `HerbrandFixedGoalExtractionBound.lean`, and `HerbrandStageSupport.lean`.
