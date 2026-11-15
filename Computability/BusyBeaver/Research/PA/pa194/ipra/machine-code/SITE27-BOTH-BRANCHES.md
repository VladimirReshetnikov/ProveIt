# Actual site-27 controller and physical frame, both branches

`PA194SourceSite27Zero.zeroBranch` proves that, in every PRA model, the pinned encoded source-controller instruction at site 27 with register 0 equal to zero takes the controller from site 27 to site 31 with its file unchanged, while the literal physical stepper takes its matching root frame to the site-31 root frame. Register values, the source-file tail, the physical spare register, and the physical suffix are arbitrary model values; the physical time is existential. The gap parameter is preserved at `(k+1)+1`.

`matchedStep` combines that theorem with the previously checked positive branch from site 27 to site 28. It uses the actual encoded controller step and a model-level matched-frame relation whose register values are function-valued witnesses. This is not a first-order definability theorem, a native iPRA sentence, or a uniform simulation of all source sites; it establishes neither direction of the desired consistency equivalence.

The proof rebuilds the eight sources listed in `SITE27-ZERO-TO24.md`, then the already existing site-25 frame relation, site-27 positive path and bridge, and these new source files: `PA194Site27ZeroFile.lean`, `PA194Path31Header.lean`, `PA194Site27ZeroPath.lean`, and `PA194SourceSite27Zero.lean`. The file identity is unconditionally proved for zero register 0; the separate `zeroBranchWithFile` theorem is explicitly conditional, and `zeroBranch` discharges its condition.

Run `check-site27-controller-both.sh` from the repository root with nine arguments: repository root, model-length source directory, source-controller source directory, source-physical source directory, this directory, coherent machine baseline build, term-graph overlay, project foundation overlay, and iPRA foundation package overlay. The replay invocation is:

```
/dev/shm/pa194-site27-zero/check-site27-controller-both.sh "$PWD" /dev/shm/pa194-model-length /dev/shm/pa194-source-controller /dev/shm/pa194-source-physical /dev/shm/pa194-site27-zero /dev/shm/pa194-site27-coherent/build /dev/shm/pa194-termgraph /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib
```

The fresh-output replay uses one prebuilt coherent machine baseline, a prebuilt term-graph overlay, and the foundational overlays. It hash-pins new source files and selected direct baseline objects and checks axiom reports for `sorryAx`. These pins do not authenticate or rebuild the full transitive closure of the retained baseline and foundational overlays. The independent replay log is `/tmp/pa194-site27-controller-both-replay.log`; consult its final PASS and exit status before treating the replay as complete.

The repository-source replay also passed using this directory for all four
source-directory arguments, with the same retained object overlays.
