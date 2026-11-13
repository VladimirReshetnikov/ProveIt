# Sign17 univariate-degree probe: partial failure

The author-observed outer session `47800` exited 1. The Equiv import compiled far enough to report product and dominant-add theorem axioms without `sorryAx`, but the mapped-degree proof has two unsolved goals and reports `sorryAx`. The module object and postflight are absent; no theorem from this failed module is claimed.

A preceding launch without the required `-I -S -B` flags exited 1 immediately with the usage message before creating output or running Lean. The recorded session above used the required flags.

The [independent failure audit](../../../reviews/nine-sharing-sign17-univariate-degree-probe-failure-independent/README.md) passed; the packet is frozen.
