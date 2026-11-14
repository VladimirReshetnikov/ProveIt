# PA194 Shift source execution

The checked source command starts at site 3661 with arbitrary natural top
`t`, Cantor-coded stack `w`, cached head `h`, and arbitrary untouched-register
frame. `PA194ShiftSource.ShiftCommand.halt_of_sum_one` proves it reaches the
explicit halt when `t+h=1`. For `t+h≠1`,
`cyclic_normal_of_sum_ne_one` proves a positive source execution returns to
site 25 with top `h` and the stack decoded into the new stack and cached
head. `PA194StackDecode.unpair` separately proves the arbitrary-input stack
decoder at sites 11–25.

The six source modules adapt the upstream PA196 Shift proof, with all
concrete source rows checked anew against the PA194 tree. The two final
branch theorems print `[propext, Quot.sound]`. They concern ordinary finite
Lean source execution, not an internal PRA/iPRA proof or a consistency
statement. The source tree retains the pinned Python archive-grammar
translation boundary described in `../pa194-source-tree/README.md`.

Run from the repository root:

```sh
Computability/BusyBeaver/Research/PA/pa194-shift-source/check.sh
```

The script rebuilds the pinned source and prerequisite semantic lemmas in a
private temporary directory, checks the concrete Shift bindings, and proves
both branch theorems.
