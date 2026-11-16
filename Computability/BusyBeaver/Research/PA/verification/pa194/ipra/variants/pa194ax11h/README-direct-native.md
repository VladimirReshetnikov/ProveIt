# AX11H literal nonhalting and PA consistency, conditional transfer

`PA194AX11HDirectNative.consistency_iff_literal_nonhalt` derives in the
repository's standard iPRA proof system that PA consistency is equivalent to
nonhalting of the literal AX11H transition table. The theorem is conditional
on `CommandContracts`: for every PRA model whose arithmetic reduct satisfies
IΣ₁, the revised source program must implement the stated returning and
halting commands at model-valued clocks. Those two contracts are not proved by
this module.

The transfer uses the checked literal-table-to-source site-10 correspondence,
the conditional source/scheduler orbit, and the scheduler/PA equivalence.
Run `./check-direct-native.sh PROVIDER-LEANPATH-FILE FRESH-OUTPUT` with the
ordered checked providers for these stages; the checker rebuilds the source and
rejects `sorryAx`.
