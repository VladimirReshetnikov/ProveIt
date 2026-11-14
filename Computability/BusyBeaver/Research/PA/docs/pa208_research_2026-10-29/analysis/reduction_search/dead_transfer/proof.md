# Deleting the identically empty transfer before MP's zero push

The source loop at [3847,3850), prefix 0011011100, is

`(CD1,(CI6,CC2))`.

The preceding destructive comparison always enters this loop with T=0.
This follows directly because [3834,3837) clears T and the comparison never
increments it. The finite inductive certificate in `../no_mp_padding/`
also establishes T=0 here from both the ordinary source seed and the actual
calibrated bootstrap store. The loop therefore executes only its zero CD
branch, changes no register, and exits immediately.

Delete it and collapse its parent to the next sibling. All retained primitive
effects and edges are unchanged under the checked ordinal skip translation.
Every new execution corresponds to the old execution with those empty loop
checks erased. All abstract commands, proof-compiler blocks, startup
calibration, and theory statements are unchanged.

The source shrinks from 3,909 to 3,906 primitive occurrences but grows from 197
to 198 distinct DAG nodes. This identity deletion is a source experiment,
not a literal Turing-machine state reduction.
