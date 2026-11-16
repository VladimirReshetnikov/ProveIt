# AX11H MP scheduler-frame reduction

This stage relates the candidate source's fetch/decode sequence to the standard
scheduler fields, and proves a positive-time source-machine MP step between
scheduler frames under six explicit equations for the next scheduler state.
The equations describe next N, continuation, top, unchanged stack, D, and cleared
cache. The theorem applies in every PRA model whose arithmetic reduct satisfies
IΣ₁. The revised scheduler is not identified with those equations here.

Replay with `./check-mp-frame.sh PROVIDER-LEANPATH-FILE FRESH-OUTPUT`, after the
MP command stage and the scheduler-frame dependencies. The ordered provider
file identifies checked Lean search directories. All four modules are rebuilt
from repository source in one output directory and checked for `sorryAx`.
