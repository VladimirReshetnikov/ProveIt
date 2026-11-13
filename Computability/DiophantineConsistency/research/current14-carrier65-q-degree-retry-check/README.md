# Generic Q degree bound: integer-cast retry

Outer session 89173 exited 1: `Int.cast_ofNat` was unused and the ring
evaluation's cast-of-2 equality remained unsolved; no object or postflight
exists. The [independent failure review](../../reviews/current14-carrier65-q-degree-retry-failure-independent/)
passed. The retry added `Int.cast_ofNat` to the ring evaluation proof; theorem
statements and other proofs were unchanged. The no-Lean preflight and
[independent prelaunch review](../../reviews/current14-carrier65-q-degree-retry-prelaunch-independent/)
passed. The independently audited prior
failed attempt and absent prior object are pinned. A successful theorem would
bound the rewritten generic Q factor under explicit input degree hypotheses;
it would not yet bind actual Carrier65 inputs or prove degree 150.
