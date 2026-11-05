# Saved current-workspace 67/106 finite-audit failure

The read-only command `timeout 60s nice -n 19 python3 -B audit.py`, run in
`research/fourteen-normalized-product106`, exited 1 before its algebra or
degree checks. Its preserved stderr reports that the first pinned Lean
source, `CarrierNormalizedProduct106.lean`, differs from the workspace.
Stdout was empty. This is not a failed degree calculation; the calculation
was never reached. The original audit and certificate were not modified.

Independent hash comparison of all three Lean files pinned at that stage
finds:

| Source | Audit pin | Live workspace | Result |
| --- | --- | --- | --- |
| `CarrierNormalizedProduct106.lean` | `efaa7ff2df3751b00cae602aaf17c6e3140c568c6bee956fa7a28fda6596e46f` | `9ab48f6b5f63d926a184b0dae575a1bd95f291e6ac814019023107e89ba97862` | different |
| `CarrierScaledAuxiliary118.lean` | `2e222efd3b40626e6734fe30e5b7239fb7a7abd5fd9c14bee8e4a238c237c620` | `174c685cf1669080cccb3760a10317aff0c99bc439bf8070eeed525ec37bff04` | different |
| `CarrierNormalizedProduct106Checks.lean` | `e269c855713dbb0badc9b11f276a9cdb5b068f6ea364d2b401f2122f6ee7b0c6` | same | matches |

Both historical pinned files were recovered from Git commit `4a1fb8565a`
and retained here. Their exact differences from the live workspace are in
`source-diff.patch`: in each, a local proof of beta positivity was replaced
with the shared `CurrentMasks2011.beta_pos_int` lemma. These are source
changes, not a fresh checked theorem or a passing rerun of the old audit.
The current graph/source binding and historic endpoint are addressed by
separate packets; historical degree/port certificate claims retain their
original scope until a separately reviewed replay succeeds.

| Artifact | SHA-256 |
| --- | --- |
| `historical-CarrierNormalizedProduct106.lean` | `efaa7ff2df3751b00cae602aaf17c6e3140c568c6bee956fa7a28fda6596e46f` |
| `historical-CarrierScaledAuxiliary118.lean` | `2e222efd3b40626e6734fe30e5b7239fb7a7abd5fd9c14bee8e4a238c237c620` |
| `source-diff.patch` | `4ffebffda9bfdc728f4495303f2053fb68ab0f280db313efc97051fb5bf89a33` |
| `normalized106-audit-rerun.stderr` | `bfadc5702484a3f5f1b17a6ea05c1b7d7b60eb62a5bccb4de827878bdeb0b0e5` |
| `normalized106-audit-rerun.stdout` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `outer-terminal.json` | `77591ea6816ad73a4aee499e8c87995a8a9340640a5b4d8f318752d61c44fead` |
