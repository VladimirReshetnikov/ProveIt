# Coherent model-uniform PA194 header replay

`check-model-header-coherent.sh` runs the complete coherent PA194 blank-startup
checker in a fresh output directory, then uses `build-model-header-coherent.py`
to rebuild the missing standalone machine-module dependencies in that same
directory. It checks `PA194SeedHeaderPass.sourceHeaderPass` and both the exact
and existential forms of `PA194NinetyThreeReturnTwoWithTail`.

The first theorem concerns a physical root-to-root header pass for arbitrary
model-valued input and explicitly displays the transformed file. The second
concerns a physical return through two file blocks with the entire arbitrary
residual suffix retained. The block count is an external natural number; the
file entries and residual suffix code may be nonstandard model elements. Both
are conditional execution components. They do
not by themselves prove blank-to-refutation equivalence, the general source
controller simulation, or either consistency implication.

From the repository root, run:

```sh
IPRA_LEAN_OVERLAY=/path/to/audited-general-ipra-objects \
IPRA_FOUNDATION_OVERLAY=/path/to/audited-foundation-objects \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-model-header-coherent.sh
```

The startup checker rejects fallback search roots containing PA194/195/196,
M6, or known standalone machine-specific objects, so every such object in
this replay is rebuilt in the one fresh output directory. The general
primitive-recursive/iPRA and Foundation objects supplied by the two overlays,
as well as the project's Mathlib objects, remain prebuilt. Their complete
transitive closure is not rebuilt or individually pinned by this checker.
`PA194_HEADER_JOBS` controls the number of simultaneous Lean checks (default
2). Setting `PA194_AUDIT_BLOCK_GROUPS=1` instead performs only a partial
startup check and exits before these model-uniform theorems.

An independent staged run checked all 147 previously absent machine modules
against the preserved coherent startup/first-instruction build, with no
machine-specific fallback overlay. Its baseline was
`/dev/shm/pa194-standalone-replay/build`; its isolated symlink view was
`/dev/shm/pa194-header-coherent/build`. The compiler refused every existing
output or sidecar path, so it did not write through those symlinks. The
manifest `/dev/shm/pa194-header-coherent/manifest.json` records the source
hashes, prior coherent-baseline imports, and general search roots; all source
hashes remained unchanged during compilation. The log is
`/tmp/pa194-header-coherent-rebuild.log`.

A second staged test copied the coherent baseline without the eight source-frame
objects and used the portable scheduler to rebuild 155 modules, including those
source-frame modules; it exited 0 and detected no changed source hashes. Its
log is `/tmp/pa194-header-portable-scheduler.log`. Both target theorems and the
exact-time variant reported only `propext`, `Classical.choice`, and `Quot.sound`;
no `sorryAx` was reported. A separate end-to-end replay of the packaged checker
remains pending.
