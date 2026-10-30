# Post-merge generic and index-bound graph

The author run passed after rebuilding 35 affected/new modules and authenticating 178 unchanged local source/object parents against the accepted preceding-snapshot second-index provider. The merged source changes were `PRAOpenOneInduction`, `PRATwoParameterInductionTransfer`, `PRAMultiParameterInduction`, `PRAPairedTwoInduction` and `PRAPairedFiniteInduction`; `PRAFstIdxWitnessBoundChecks` was additionally rebuilt because its check was not in the assembled baseline. Root independent replay `/tmp/pra-after-five-induction-independent-p0oew8oa` passed with all source, object and complete-log hashes matching the author; private replay `/tmp/pra-after-five-induction-independent-x3ewusil` also passed with the same hashes. Author/root source snapshots and complete logs and all three terminal states are recorded. Foundation and Mathlib are inherited.

The graph covers generic strict-surrogate comparison and forward implication, conditional reverse, the fold, and the exact first-/second-index local and first-index family bounds. It does not prove the witness-bound certificate for Foundation's ZFC refutation sentence.

```sh
python3 Computability/DiophantineConsistency/reviews/pra-after-five-induction-refresh-author-replay/replay.py \
  --parent /tmp/pra-sndidx-bound-independent-b4cga067/lib
```
