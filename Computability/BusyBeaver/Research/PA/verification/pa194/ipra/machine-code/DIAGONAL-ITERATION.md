# Model-length Cantor diagonal invariant

These three new Lean sources extend the exact source-round invariant in `DECODER-CANTOR.md`:

* `PA194DiagonalCode.lean` defines a fixed primitive-recursive coded state transition on a square-paired register pair `(x,y)`: `(x+1,y) → (x,y+1)` and `(0,y) → (y+1,0)`. It proves both branches and that each step increases the machine Cantor score by exactly one.
* `PA194DiagonalIteration.lean` proves `scoreIteration`: for every model-valued iteration count, the coded iterator's Cantor score is its initial score plus that count. Its proof is an object-language open induction carried out in every PRA model; its locally reproved primitive-recursion equations do not require IΣ₁.
* `PA194DiagonalLink.lean` proves `iterationProjects`, identifying both coordinates of that model-length iterator with the scheduler's actual `fixedFirst`/`fixedSecond` primitive-recursive codes at the resulting score. It also proves `positiveRoundMatches` and `zeroRoundMatches`, identifying the coded transition with the register-6/7 outputs of each corresponding actual controller round. The former needs PRA; the latter assumes IΣ₁ because the underlying variable-length controller drain does.

These are model-theoretic theorems, not native iPRA derivations. The model-length theorem concerns the coded diagonal iterator. The one-round source correspondences do not yet prove that a model-length number of variable-duration actual source rounds has the same coordinates, or that the source reaches site 42. Full scheduler/controller synchronization and the consistency equivalence remain open.

The common-source staged replay uses the 270-module fetch/controller/scheduler build and rebuilds the five source-round modules, the two Cantor/exit modules, and the three modules above in one fresh suffix output. The six graph objects and general project/package/Lake foundations remain prebuilt, with exact provenance in `/dev/shm/pa194-scheduler-controller/SCHEDULER-FETCH-MODEL.md`. The replay completed with exit 0, log `/tmp/pa194-diagonal-iteration-replay.log`, output `/dev/shm/pa194-diagonal-iteration-replay`. From the repository root, with a fresh output:

```sh
/dev/shm/pa194-unpair-diagonal/check-diagonal-iteration.sh "$PWD" /dev/shm/pa194-scheduler-controller /dev/shm/pa194-unpair-diagonal /dev/shm/pa194-fetch-coherent-full-v2 /tmp/pa194-fetch-coherent-full-v2.log /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-diagonal-iteration-replay
```

The new source SHA-256 values are pinned in `check-diagonal-iteration.sh`. Its called prerequisite checkers each print their own PASS; only the final diagonal PASS covers all ten suffix modules. The repository-source suffix replay also passed against the independently rebuilt fetch baseline, with the same prebuilt graph and foundation limitations.
