# Restore the declared package 72 compact-port payload paths

The P13 and P14 `ACTIVE_BINDING.json` files referenced four gzip payloads in
`positive13/native/coefficients/`, but that directory was absent. Before
copying, [before.json](before.json) recorded all four missing paths and
verified the tracked source44 gzip payloads against **both** active bindings:
compressed and decompressed SHA-256, raw byte length, little-endian bit length
and minimal encoding. The four byte-identical files were then copied using
exclusive creation and verified again. The [result](result.json) records the
successful restored files. The other missing original binding metadata was
not created.

The first run failed before any write because the script had a mistyped
positive13 active-binding hash. That pin was corrected and the successful
run exited 0. The corrected script refuses to overwrite an existing target;
it is not an idempotent verifier. Its SHA-256 is
`beb51139327ed46693cbe20a70310d42af47bc9bd617a2b863c427564314d1c3`,
the before-observation SHA-256 is
`0e25a6dddc8ea5e730eff75e29ffd214b7dd54e493197e564d432ce0b5f00951`,
and the result SHA-256 is
`cdd61b4780d87c1f07282d0b7d732b2c8d9330f95c0c663f3670ffedf73db9b3`.
This is a file repair and byte check, not a Lean proof relating files to ports.
