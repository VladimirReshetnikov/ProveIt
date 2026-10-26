# Product projections and affine budgets

These are separate proof-only proposals against commit
`6175dff9a15491497c7a3c1bda4f6a62a6349c74`.

`patches/pairing-projections.patch` changes eight clients in four modules and
adds the 16-line general projection helper. Net saving: 8 production lines.
The complete modified PairingRepresentation module and its `rfl` data audit
compiled. The other six clients remain source-reviewed candidates; the
quadratic and tree witness-obligation shapes compile separately under the
existing certificate specification.

`patches/affine-budgets.patch` changes three arithmetic budget arguments and
adds the 21-line helper. Net saving: 8 production lines. The helper and both
numerical application regimes compile; the full GraphSizeBounds module was
not rebuilt. The ordinary numerical rule permits zero arity, whereas the
direct rule needs positive arity to pay its overhead.

`lean/` contains the helpers and checks. `patched-modules/` contains complete
candidates. `metrics.json` counts all new helper lines and imports. To
regenerate candidates and metrics, run `python3 make_patches.py --repo PATH`
against the pinned unmodified repository. The common top-level replay script
is the supported way to run checks in your own configured project.
