# AX11H generic ordinary-MP scheduler step

`stepAlt` has arbitrary codes in its five AX branches and the AX11H ordinary
MP behavior. In every PRA model satisfying IΣ₁, `advance` proves that when the
decoded opcode is 1, the actual candidate source machine advances from the
current scheduler frame to its `stepAlt` frame in positive model time.

The equality between the intended revised scheduler and a particular
instance of `stepAlt` is a separate obligation; this module does not prove it.

Replay with `./check-generic-mp-scheduler.sh PROVIDER-LEANPATH-FILE FRESH-OUTPUT`
after the MP-frame stage. The ordered provider file lists checked dependency
directories; the checker rebuilds this module and rejects `sorryAx`.
