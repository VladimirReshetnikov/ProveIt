# First natural-seed helper attempt: failed

This fixed-port-free helper attempts to combine the checked `strong_index`
and `auxiliary_seed_of` lemmas. Actual outer session 98597 exited 1 because
`absdiff` was not in scope; the captured Lean log reports `sorryAx`, so this
attempt is not a proof and its object is excluded. The exact source, runner,
state and compile/dependency logs are retained under [attempt01](attempt01/).
The corrected namespace-only retry is in
[the separate attempt02 packet](../thirteen-current2011-natural-seed-attempt02/README.md).
