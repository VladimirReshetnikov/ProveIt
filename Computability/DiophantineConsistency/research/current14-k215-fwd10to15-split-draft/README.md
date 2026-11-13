# K215 forward checks 10–15: proposed root splits

Each independent source-level refactor selects the two actual root children of `fwd10` through `fwd15`, proves their `allC fwdF` checks in separate modules, and joins them into its unchanged original-namespace theorem. Original project files remain untouched. Observed root cut/leaf counts: 44/89 for 10–14, 45/90 for 15. Each child and join remains uncompiled until the guarded stages succeed; no assumption is made that a split fits.
