# Site 27 zero-branch physical prefix

`PA194Site27ZeroTo5.zeroTo5` and `PA194Site27ZeroTo11.zeroTo11` prove, for every model of PRA and arbitrary model-valued registers and suffix, that the physical site-27 root frame with register 0 equal to zero reaches control 5 and control 11 respectively. The time is existentially quantified. The control-11 theorem exposes an odd selected-left value and the remainder of the tape; its proof does not yet identify the complete returned root frame.

These are physical-execution results, not a native iPRA theorem or a simulation of an arbitrary source-controller run. In particular they do not establish the site-31 root return, an actual scheduler/controller correspondence, or a consistency direction.

Run `check-site27-zero-prefix.sh` from the repository root with arguments: repository root, model-length source directory, source-controller source directory, source-physical source directory, this directory, coherent machine baseline build, term-graph overlay, project foundation overlay, and iPRA foundation package overlay. The successful scratch invocation and log are:

```
/dev/shm/pa194-site27-zero/check-site27-zero-prefix.sh "$PWD" /dev/shm/pa194-model-length /dev/shm/pa194-source-controller /dev/shm/pa194-source-physical /dev/shm/pa194-site27-zero /dev/shm/pa194-site27-coherent/build /dev/shm/pa194-termgraph /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib
```

`/tmp/pa194-site27-zero-prefix-replay.log` records a successful fresh-output replay and axiom reports without `sorryAx`. The checker rebuilds the relevant source-controller and site-25 physical source suffix before these modules. The coherent machine baseline, term-graph overlay, and foundational overlays remain prebuilt; in particular, the baseline's direct site-27 physical prefix and zero-cell objects are hash checked. Those checks are evidence about the selected objects, not independent authentication or a rebuild of their entire transitive closure.

For a repository-source replay, use this directory for all four source-directory
arguments. The retained object overlays remain the same as in the scratch run.
