# Negative lenbit and positive pow2 witness bounds

The Lean modules prove three local facts over arbitrary IOpen models and derive their universally closed counterparts in candidate PRA:

* The negated Foundation `lenbitDef` graph at arguments `(i,a)` implies its bounded translation with bound `a+1`. In its negative form the outer variable is universal, and each required divisibility witness is at most that variable, itself at most `a`.
* The same bound is preserved through arbitrary arithmetic rewritings, including the exact `“m. ¬!lenbitDef 1 m”` occurrence in Foundation `sppow2Def`.
* Foundation's positive `pow2Def` graph at `a` implies its bounded translation with bound `a+1`. Its bounded universal is handled directly in IOpen using the explicit upper bound on divisibility witnesses, with no bounded collection assumption.

The results leave other `sppow2Def` conjuncts, `ppow2Def`, `exponentialDef`, `bitDef`, the fixpoint, and ρ unresolved; they do not establish the target HA equivalence.

The replay authenticates the post-three-induction 34-module rebuild and its 195 unchanged local parent source/object pairs, together with selected Foundation source/object anchors including `PPow2`, `Pow2`, and `Exp`. Other Foundation and Mathlib transitive dependencies are inherited and are not source rebuilt.

After the author receipt is frozen, run:

```sh
python3 Computability/DiophantineConsistency/reviews/pra-neglenbit-pow2-bound-author-replay/replay.py --parent /tmp/pra-after-three-induction-refresh-hzfafndb/lib --expected Computability/DiophantineConsistency/reviews/pra-neglenbit-pow2-bound-author-replay/author/state.json
```
