# Independent failure audit: three-prefix value group

Author-observed outer session 35327 exited 1; this is not an independently observed raw process transcript. The dependency scan passed. Lean compilation failed because the `q` and `N` rewrites did not match `Fin.last` against explicit `⟨1, ...⟩` and `⟨2, ...⟩` index forms. The log separately reports standard axioms for `prefix_B`, but the module as a whole failed and no group object was emitted; the `q` and `N` reports include error-contaminated `sorryAx`. There was no final postflight.

`check.py` verifies source, state and child logs, exact direct first-prefix producer path/hash, 100 guards and 1,169 overlay links. No sampled monitor stop/error was recorded. No Lean replay or successful group theorem object is claimed.
