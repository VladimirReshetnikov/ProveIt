# Strong-norm diagnostic failed on numeral conversion

Author-observed outer session `1359` returned numeric exit 1. Retained state SHA-256 `80899a5be35a092903a15ad21e8aba56fbd89b46daa045ea6862c51e6587719a`; pre-run producer survey `5e0a12ddb5419503ab2fc2418ee59db3d0185da0a11c2454870c3f17b34fc5f7`. The outer record is an author observation, not an independently observed transcript.

Lean exited 1 after 2.227 seconds without a monitor stop. Its compile log SHA-256 `6f7c5110898c0c8670d6d5d9e05caf79d75d461235acce36ad30804adf34f47c` reports a type mismatch at the final line: `lt_iff_succ_le.mp hgt` yields `1 + 1 ≤ f` while the goal is `2 ≤ f`. The generated axiom report includes `sorryAx` because of the failed declaration and is not proof evidence; no successful object was recorded. One linter warning was also emitted. The final all-stage guard and post-success producer survey were not reached. Point-observation and inherited-provider limitations remain as in the parent README.
