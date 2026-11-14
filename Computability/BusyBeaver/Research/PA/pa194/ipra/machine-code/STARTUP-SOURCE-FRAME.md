# PA194 startup source-frame layout

`PA194StartupSourceFrame.modelDenseStartupSourceFrame` decomposes the exact
58,154-step literal blank-start endpoint in every candidate PRA model. It
reaches dense state 24 with left tape half 1 and right tape half
`2 * zeros(47, 2 * sourceFile(seedArgs) + 1) + 1`, expressed with the checked
primitive-recursive zero-run and source-file codes rather than model
multiplication. This exposes the 48-bit source-controller header and preserves
the complete remaining file.

The eleven logical arguments are `[2,0,0,0,0,0,0,0,0,1,tail]`. The first
nine are proved equal to `readFile` of the 35-block startup seed using
`seedArgs_logical`; `sourceFileCode` applies the separately checked logical to
physical register permutation. The tenth argument is the one-valued physical
spare, and `tail` encodes all 25 remaining one-valued spare blocks. The
resulting 26 spares are not discarded.

In the standard source semantics, `firstSeedSourceStep` uses the checked
source-tree lookup at site 25: the first instruction decrements logical
register 8, which is initially zero, so its zero branch goes to site 27 and
leaves the entire logical register mapping unchanged. This source-level step is
not yet identified with a physical PA194 run in arbitrary PRA models. The
model-uniform controller/source-frame simulation and both consistency
implications remain open.

The [seed-header dispatch](SEED-HEADER-DISPATCH.md) extends this endpoint
through twelve physical steps with an arbitrary model-valued residual tail.

The model decomposition and standard source facts passed a suffix rebuild
against retained checked dense-startup, arithmetic, source-tree and iPRA
prerequisite overlays. Their printed theorem axioms exclude `sorryAx`; a fresh
full replay is pending.

A source-pinned suffix replay against the retained prerequisite overlays is:

```sh
PA194_BRIDGE_OVERLAY=/dev/shm/pa194-standard-bridge \
PA194_DENSE_OVERLAY=/dev/shm/pa194-dense-startup-agent \
PA194_PARENT_OVERLAY=/dev/shm/pa194-startup-preserved \
PA194_PROJECT_OVERLAY=/dev/shm/pa194-model-neighborhood \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-startup-source-frame.sh
```

The checker pins selected prerequisite source files and directly imported object
hashes, rebuilds the source-frame module, and checks its printed axioms. It
retains transitive object dependencies from these overlays rather than
rebuilding or independently pinning their entire dependency closure. The paths
and object hashes describe these particular retained builds.
