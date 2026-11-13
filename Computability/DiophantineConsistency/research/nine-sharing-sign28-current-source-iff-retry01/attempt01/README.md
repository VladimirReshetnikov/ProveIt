# Factored sign28 source iff: partial failure

Author-observed outer session 36209 exited 1. The first stage compiled and its `exists_cons_iff` and `seed_cons_iff` reports are both `[propext, Classical.choice, Quot.sound]`; it emitted one unused section-variable warning. Its object SHA-256 is `2f7b33d5954dbc16bc528c98a3758954232304ad23f1121366881e307d74100b`.

The second dependency check succeeded, but Lean compile exited -6 with the uncaught interpreter memory exception. The sampled peak was 2,938,318,848 bytes, with no monitor stop reason or monitor errors. The exact trigger is unknown; the failed stage yields no proved source iff, and final postflight did not run. Retained state SHA-256 is `dfc94dbdc92becb9dc3971a1a999461f60fee832203f55371be933c5acfa9f93`; author outer receipt SHA-256 is `f80fcf0add0d96a2003b5230b3d5c7f0f15060c3fdfb95f0e56b782b4567005b`. Numeric outer exit is author-observed, and sampling has the limits in the state.
