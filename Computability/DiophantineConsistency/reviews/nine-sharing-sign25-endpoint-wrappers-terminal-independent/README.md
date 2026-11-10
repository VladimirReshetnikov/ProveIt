# Independent audit of failed wrapper reuse attempt

Author outer session 95304 exited 1. Independent checker session 3418 exited
0 and recorded `result.json`. It verifies the attempted standard-wrapper
source and logs, both direct import bindings (including the earlier native
object), all direct guards and overlay links, and reruns the earlier partial
native audit.

The standard wrapper's dependency scan exited 0 but its compilation exited
`-6` with an interpreter memory exception. The translated stage and final
postflight were not attempted. The imported native object came from a
successful child of a different failed outer run; its full producer postflight
is absent. This failure does not establish the standard or translated endpoint
and does not erase the earlier native child. Provider guards and ancestry
checks are point observations; Lean was not independently replayed.
