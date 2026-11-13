# Independent audit of no-alias opacity retry failure

The author observed outer session 12392 exit 1. Independent checker session
77196 exited 0, validating the first stage's source and logs, direct guards,
overlay links and upstream bridge audit. The native source bytes equal those
of the earlier successful native child, but this retry's first compilation
exited `-6` with an interpreter memory exception under `-M2800`. No first
object, later stage or final postflight exists for this retry.

These outcomes show that the same source can behave differently across these
guarded runs. They do not determine why. This failure does not erase the
earlier independently audited successful native child, and it does not prove
the standard or translated endpoints. Provider checks remain point
observations and no independent Lean replay was performed.
