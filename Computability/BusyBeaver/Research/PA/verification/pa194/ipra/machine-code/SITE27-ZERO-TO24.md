# Site 27 zero branch through physical control 24

The checked chain starts from the pinned machine's site-27 physical root frame with argument 0 equal to zero. For arbitrary values in any model of PRA (including the complete file and suffix), it reaches physical control 11 after restoring the seven carried register blocks (`zeroRollback`), then control 12 (`zeroTo12`), then control 14 (`zeroTo14`), and finally returns to root control 24 (`zeroTo24`). The latter also proves the returned word is even. The elapsed physical time is existentially quantified. The returned-file identity and the return to the site-31 root frame are not part of this replay.

This is a model-uniform physical execution prefix, not an internally quantified native iPRA sentence, an actual scheduler/controller simulation, or either consistency implication.

Run `check-site27-zero-to24.sh` from the repository root with these nine arguments: repository root, model-length source directory, source-controller source directory, source-physical source directory, this directory, coherent machine baseline build, term-graph overlay, project foundation overlay, and iPRA foundation package overlay. The successful invocation is:

```
/dev/shm/pa194-site27-zero/check-site27-zero-to24.sh "$PWD" /dev/shm/pa194-model-length /dev/shm/pa194-source-controller /dev/shm/pa194-source-physical /dev/shm/pa194-site27-zero /dev/shm/pa194-site27-coherent/build /dev/shm/pa194-termgraph /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib
```

The fresh-output replay log `/tmp/pa194-site27-zero-to24-replay.log` ends in PASS. It rebuilt the relevant source-controller and site-25 physical suffix, the prefix, rollback, and control-12, control-14 and control-24 modules, and audited their printed axioms for `sorryAx`. The retained coherent machine baseline, graph overlay, and foundation overlays are prebuilt. Direct baseline objects used by the new chain are hash-pinned; their transitive closure is not independently authenticated or rebuilt by this script. The machine baseline is a single root, avoiding mixed machine-specific fallback roots.

The eight new sources are `PA194Site27ZeroTo5.lean`, `PA194Site27ZeroTo11.lean`, `PA194Site27ZeroExact.lean`, `PA194CarryAppendZero.lean`, `PA194Site27ZeroRollback.lean`, `PA194Site27ZeroTo12.lean`, `PA194Site27ZeroTo14.lean`, and `PA194Site27ZeroTo24.lean` (eight modules total). All reside alongside this document.
