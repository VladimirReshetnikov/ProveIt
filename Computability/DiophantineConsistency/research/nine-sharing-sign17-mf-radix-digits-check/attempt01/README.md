# MF source-port radix digits: partial failure

Author-observed outer session `48438` exited 1. Fifteen provider stages
compiled. The final stage's tail-length report is clean, but the high-port
first-digit proof hits recursion depth, and the decoded-digit arithmetic
leaves an unnormalized singleton/zero expression; downstream reports contain
`sorryAx`. No final object or postflight exists. No MF radix theorem is claimed.
The [independent failure audit](../../../reviews/nine-sharing-sign17-mf-radix-digits-terminal-independent/README.md) passed; the packet is frozen.
