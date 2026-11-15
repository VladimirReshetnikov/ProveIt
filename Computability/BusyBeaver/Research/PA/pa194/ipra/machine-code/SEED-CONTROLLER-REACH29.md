# Blank-tape startup and three encoded-controller steps

`PA194SeedControllerReach29.blankAndThreeSteps` proves the following uniformly in every PRA model. Begin the pinned literal physical machine at its blank configuration, and take the encoded controller's site-25 state with the startup's nine logical register values and an arbitrary controller-file tail. Three actual controller steps take sites 25→27→28→29 and reach the displayed final source state. There exists one model-valued physical time taking the blank machine to the matching physical site-29 frame. The proof incorporates the certified 58,154-step blank startup and the three physical source-instruction segments. The output physical suffix contains the original fixed startup `seedTail` with one additional one-valued spare block; the controller-file tail is arbitrary and independent of that physical suffix.

`PA194Site25Then27Then28.zeroPositiveIncrement` gives the same three source/physical transitions before specialization, with arbitrary register values satisfying register 8 = 0, register 0 = m+1, and physical suffix = `seedTail`. The physical clock is existentially quantified, and the matched frame is a model-level Lean statement. Neither theorem supplies a native iPRA derivation, source simulation for arbitrary times/sites, or a consistency implication.

The final staged checker is `check-seed-controller-reach29.sh`, invoked from the repository root with fifteen arguments:

```
/dev/shm/pa194-site28-controller/check-seed-controller-reach29.sh "$PWD" /dev/shm/pa194-model-length /dev/shm/pa194-source-controller /dev/shm/pa194-source-physical /dev/shm/pa194-site27-coherent/build /dev/shm/pa194-termgraph /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site28-controller /dev/shm/pa194-site28-complete-repo /dev/shm/pa194-site28-finish-repo /dev/shm/pa194-site28-seed-repo /dev/shm/pa194-site28-after-carry-repo /dev/shm/pa194-site28-roundtrip-repo /dev/shm/pa194-site28-codes-repo
```

Its four new Lean sources, in build order, are `PA194SourceSite28Physical.lean`, `PA194Site27PositiveThen28.lean`, `PA194Site25Then27Then28.lean`, and `PA194SeedControllerReach29.lean`. It rebuilds the prior encoded-controller and site-25/site-27 physical bridge suffix in the same fresh output, then these sources, auditing their theorem axiom reports for `sorryAx`. The coherent site-27 baseline, six disjoint site-28 physical stage directories, code-graph overlay, and general foundations remain prebuilt. The checker pins selected direct objects and rejects overlapping machine-object names among the machine stages; these measures do not authenticate their entire transitive closure. Earlier stage source rebuilds must be run independently or trusted. The independent replay log is `/tmp/pa194-seed-controller-reach29-replay.log`; consult its final PASS and exit status before relying on the replay.

The repository-source replay also passed using this directory for all four
source-directory arguments and the same retained object overlays.
