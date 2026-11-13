# Author seed-overlay control

After the prelaunch packet was committed, an isolated Python check imported the exact launcher at commit `3a03b220a6`, read its pinned frontier plan and called `seed_overlay` into fresh temporary author and peer directories. The process actually exited `0`, reporting `PASS_SEED_OVERLAY author 807` and `PASS_SEED_OVERLAY peer 807`. Each resulting `.olean` entry was a symlink; each seed output row was checked against the pinned historical state and guard plan by `seed_overlay`. The temporary directories were removed when the control completed. No Lean process was launched.

This control exercises initial seed-overlay construction only. It does not check the full 342-module loop, direct imports, compiler exits, resource limits, stable HEAD, native-loader environment, dynamic ancestry, or a real build. Independent exact-byte prelaunch review remains required.
