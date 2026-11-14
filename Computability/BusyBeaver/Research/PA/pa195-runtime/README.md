# PA195 unfolded-parent register engine

`PA195RuntimeEngine.lean` binds the actual unfolded 202-control parent table
to the reusable register engine in the imported PA196 development. Lean
checks that every protected engine row agrees with the reference machine and
that the append-one tail is exact. Consequently `box_lemmas` instantiates the
four upstream mark, increment, zero-decrement, and positive-decrement
reachability theorems for arbitrary valid register files.

The `symbolic_segment` theorem instantiates the upstream symbolic-execution
soundness theorem for this exact parent machine. Given an explicit successful
symbolic-execution equality, it concludes positive physical reachability for
every valid complete register file and every gap parameter. It does **not**
yet prove any of the 4,815 candidate-specific symbolic-execution equalities or
connect source proof programs to the machine.

Run from the repository root:

```sh
Computability/BusyBeaver/Research/PA/pa195-runtime/check.sh
```

The script pins and rebuilds the four actual imported M6 sources, rebuilds the
finite table certificate, and checks this module using a private temporary
`/dev/shm` directory. The results are ordinary Lean theorems; they are not
PRA or iPRA derivations and do not establish a consistency equivalence.
