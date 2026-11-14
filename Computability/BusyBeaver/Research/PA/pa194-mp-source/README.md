# PA194 MP source execution

`PA194MPSource.MP.command_field` proves the actual PA194 source behavior of
the MP command on arbitrary natural inputs and an arbitrary untouched
register frame. Starting at site 3554, it reads the next encoded operand,
compares the encoded implication with the cached head, updates top and stack
according to the success or failure branch, and returns to site 25. The
more general `command` theorem accepts an arbitrary encoded input tail.

These modules adapt the upstream PA196 MP proofs; the concrete source rows
are all checked anew against the PA194 tree. Both theorems print `[propext,
Quot.sound]`. They concern ordinary finite Lean source execution; they do not
establish the PA proof-translation invariant or an internal PRA/iPRA
consistency result. The source tree retains the pinned Python archive-grammar
translation boundary described in `../pa194-source-tree/README.md`.

Run from the repository root:

```sh
Computability/BusyBeaver/Research/PA/pa194-mp-source/check.sh
```

The script rebuilds the pinned source and prerequisite semantic lemmas in a
private temporary directory, checks the concrete MP bindings, and proves both
branches of the source command.
