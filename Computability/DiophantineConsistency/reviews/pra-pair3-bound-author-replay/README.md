# Triple-pair graph witness bound

The new sources are `PRAPairTripleWitnessBound.lean` and `PRAPairTripleWitnessBoundChecks.lean`. The author build passed against the root independently replayed post-five-induction provider, authenticating 79 unchanged local source/object parents. Private replay `/tmp/pra-pair3-bound-independent-tdkjd8zm` and root replay `/tmp/pra-pair3-bound-independent-xmaajon3` passed with matching source, object and complete-log hashes. Author/root source snapshots, complete logs and all three terminal states are recorded. Foundation and Mathlib are inherited.

`candidate_proves_pair3_bound` constructs an actual candidate-PRA derivation that, for every output code `p`, Foundation's exact mapped `pair₃Def(p,a,b,c)` entails its syntactically bounded form at `p+1`. This graph occurs in Foundation's `Nth.blueprint.core`; the proof does not bound that entire core or its fixpoint, and does not establish the ZFC refutation witness-bound certificate.

```sh
python3 Computability/DiophantineConsistency/reviews/pra-pair3-bound-author-replay/replay.py \
  --parent /tmp/pra-after-five-induction-independent-p0oew8oa/lib
```
