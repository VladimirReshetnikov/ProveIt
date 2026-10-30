# Post-Rank-refactor compatibility rebase: preserved v4 failure

The v4 attempt `/tmp/adaptive86-machine-compat-rebase-v4-jpxfcgve` recorded `FAILED` (state SHA-256 `fb3f5eeb787af89da65097e69898b0fe8deceaa4512bbe2f0e88c12590f07bea`). It sought to extend the private helper module with the exact new `main_congruence_of_facts` proof after the Rank refactor. Ten earlier 86 modules compiled, but the helper module failed because its source omitted the historical `ArithmeticAdaptiveMainCongruence2011` import needed to resolve the `MainCongruence` type. No final machine theorem was built in this attempt.

The original state, driver, 507-object provider inventory, source snapshots, available complete logs and timings are preserved in `adaptive86-machine-compat-rebase-v4-failed-evidence`, `FILES.json` SHA-256 `136d92b254f014920054d08b900eae1acb0787481ca0c1dcb628251d23f1170d`. The separate v5 attempt adds that missing import in a new helper source, retaining v4 intact.
