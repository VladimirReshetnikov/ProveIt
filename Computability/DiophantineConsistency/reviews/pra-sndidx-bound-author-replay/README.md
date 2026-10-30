# Second-index syntactic witness bound

The sources are `PRASndIdxWitnessBound.lean` and `PRASndIdxWitnessBoundChecks.lean`. The two-module author build passed against the accepted first-index family-sentence provider, with 79 unchanged authenticated local source/object parents. Private replay `/tmp/pra-sndidx-bound-independent-9_eql72e` and root replay `/tmp/pra-sndidx-bound-independent-b4cga067` both passed with matching source, object and complete-log hashes. Author/root source snapshots, full logs and all three terminal states are recorded. Foundation and Mathlib are inherited.

`candidate_proves_sndIdx_bound` constructs an actual candidate-PRA derivation of the universally closed mapped implication that Foundation's exact `sndIdxDef(x,p)` entails its `bnd` transformation with bound `p+1`. Foundation's vector machinery uses `sndIdxDef`; the proof does not yet connect the bound to an occurrence inside the coded history or establish a bound for the ZFC refutation predicate. A subsequent upstream PRA merge changed inherited induction dependencies, so this is a preceding-snapshot receipt until its affected graph is rebuilt.

```sh
python3 Computability/DiophantineConsistency/reviews/pra-sndidx-bound-author-replay/replay.py \
  --parent /tmp/pra-fstidx-family-sentence-independent-xcmjxzdd/lib
```
