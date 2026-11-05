# Successful natural-sum MF diagnostic

`natural_sum` checks the equality in ℕ between the explicit recipe's unshifted high mask plus `rho^2011−1` and `CurrentMasks2011.highPort + CurrentMasks2011.beta`. It uses `congrArg₂` on the already checked high-port and beta recipe equalities. This is an isolated diagnostic; it does **not** prove the integer cast, the port-3 projection, the byte decoder, or any filesystem correspondence.

Observed runner session 46385 exited 0; both Lean dependency and compilation commands exited 0, and the sole axiom report is `[propext]`. The inherited runner's terminal string says `PASS current2011 MF shift identities`; its actual source and report prove only `natural_sum`. The runner rechecked its direct providers and 180 companion/shadow slots and the source/base preflight before and after. The successful object `/tmp/current2011-mf-natural-sum-probe-20261105/CurrentMFNaturalSum.olean` has SHA-256 `216a395f5b8c4618f888af095f12a497f09c76489c92b8548b3556555189aba1`.

The Lean process used `-M2800`, one thread, nice 19, idle I/O and a 180-second foreground timeout, without an automatic process-group RSS or host-memory stop. The check uses inherited source-built base/provider ancestry, not a new base rebuild or full dynamic/package-transitive trace. The complete byte-to-port problem remains open.

SHA-256: source `4f5598c161dd3c3e5c98371191ca3cde6df45d373aafb2bcaeeaf718e83aec78`; runner `6b13ac8ccaf936ab01da66a845dd60d3a4e26f92a1c4fb4c85c7d12e774bdaee`; state `64f0c12a6201e065253b963c340ff1e942dd65f037fa8e072642c7341b036131`; compile `407ba71ac792cc46c0d61a317d6a4cca949576ac55c362fa1ea40244343118ab`; outer observation `b19a955266136c8f25395c4478ff8b9dc3d215c31dfb19a9071e77f0276570ad`.
