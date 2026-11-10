# Conditional K stream digit-bound probe

This guarded source proposes that every digit in the constructed stream is below the actual radix, under the explicit assumption that each input coefficient plus one is below that radix. It also proposes concrete bounds for the first 32 and final 14 tile coefficients and all 44 controls. These samples do not cover the remaining tile blocks, so they do not establish the unconditional actual K stream bound. There is no byte or external JSON/gzip/file/PDF theorem.

The no-Lean preflight exited 0 against the independently audited symbolic K stream provider (`reviews/nine-sharing-sign17-k-radix-stream-current-terminal-independent/`). Source/object/logs, Init route and overlay are pinned; inherited one-thread, child and resource caps remain. Runner SHA-256 `56df38fa98af8ff5ca3cd30978417585422793f4a0ddde81626b25a778fac0cf`; manifest `368b44b0ae78386b58578e9e9feba89aca57e02d9c26dd081d23649fb1633f28`; source `dc854614e5fec801dafbed2c19ee1c94dbf913b0c08397dbd90a367fe518f1ee`. Independent prelaunch and exclusive allocation are required.

Independent prelaunch passed at `reviews/nine-sharing-sign17-k-digit-bound-probe-prelaunch-independent/`. Attempt 01 failed with observed outer session 85283, exit 1; see `attempt01/`. No module object or unconditional stream bound exists. Independent failure audit is pending.

The [independent failure audit](../../reviews/nine-sharing-sign17-k-digit-bound-probe-failure-independent/README.md) confirmed the failure; the attempt is frozen.
