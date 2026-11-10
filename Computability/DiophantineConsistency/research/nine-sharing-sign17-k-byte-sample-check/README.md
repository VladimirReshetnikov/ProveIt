# K radix/byte fixture sample guard

The proposed finite numeric fixture identities cover full blocks 2, 125 (including radix digit 1004), and 126, plus the five-digit/24-byte tail 252. The source-only generator reads externally pinned coefficient/snapshot data; these are arithmetic sample identities only and do not bind the actual symbolic stream to a full byte list or any external JSON/gzip/file/PDF. No Lean result is claimed yet.

No-Lean preflight passed (exit 0). The audited K stream provider and generator/source, Init, object/log and overlay routes are pinned; inherited one-thread and child/resource guards apply. Generator SHA-256 `59b4b5bd7268b919bfd017b447ec2c87c471e11d2be736b592dfae1b15dea387`; runner `264b0281e5f73c9d78969fc4b3433f6ea246ccfd3e1309e52771aa2b0386e669`; manifest `ae3a35aeaadda9590bab26f986b696896501a22733a423759f8cfaaabc5853b6`; source `1e21afdfbdab096bb503174c0125be6355200dea6a1890186e01e33a6e68f712`. Independent prelaunch and exclusive allocation are required.

Independent prelaunch passed at `reviews/nine-sharing-sign17-k-byte-sample-prelaunch-independent/`.

Attempt 01 completed with observed outer session 56779, exit 0; stage and postflight passed. See `attempt01/`. Independent terminal audit is pending.

The [independent terminal audit](../../reviews/nine-sharing-sign17-k-byte-sample-terminal-independent/README.md) passed; the attempt is frozen.
