# Factored n6/r11 upper endpoint: addition-orientation retry

The source preserves the theorem and the proof in [v3](../trace74-n6-r11-upper-compact-draft-v3/) except for using `add_le_add_right` directly at the single addition-order mismatch. No graph claim is made.

The [independent source review](../../reviews/trace74-n6-r11-upper-compact-v4-source-independent/README.md) passed the targeted change and verified v3 failure. The [independent prelaunch review](../../reviews/trace74-n6-r11-upper-compact-v4-prelaunch-independent/README.md) approved one coordinated check.

One author run completed in actual tool session 14415, exit 0 and fully reaped; its [terminal](observations/attempt01/terminal.json) SHA-256 is `c755bc4ae693037fec8773824d44645d91e4ad54537d19885a7dd1ae624cdd00`. The object `/tmp/trace74-n6-r11-upper-compact-v4-0up3vfpa/lib/Trace74N6R11CompactUpper.olean` SHA-256 is `cae7a590b48d4475b470a1f5a429cc9533b58bdeb02870b3b9fbccf88207821f`. The [independent result audit](../../reviews/trace74-n6-r11-upper-compact-v4-result-independent/README.md) passed; this is a conditional scalar upper endpoint.
