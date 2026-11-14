# PA194 command scheduler and source

`PA194CommandTransfer.step` is the PA194-specific arithmetic command
interpreter. Its AX case uses the guarded old formula and pushes a separate
diagonal head; the inherited PA196 interpreter's bundled gate is not used.
The source execution proofs check the actual AX, MP, and Shift branches, and
the fetch/dispatch proof binds the three command targets to the PA194 tree.

`PA194CommandEquiv.halts_iff` proves that this interpreter's scheduler halts
if and only if the exact cyclic source execution halts, from any corresponding
site-25 state. The proof includes the source halt branch and arbitrary finite
command iteration. Each successful source command takes positive time, which
also supports the converse. The theorem prints `[propext, Classical.choice,
Quot.sound]`.

This is an ordinary standard-natural-number Lean result. It does not yet
establish that the command calculus checks PA refutations or formalize either
machine/consistency reduction inside PRA or iPRA. Source generation retains
the pinned Python archive-grammar translation boundary described in
`../pa194-source-tree/README.md`.

Run from the repository root:

```sh
Computability/BusyBeaver/Research/PA/pa194-command-source/check.sh
```

The script first rebuilds the AX core and guard in a private tmpfs directory,
then rebuilds the Shift, MP, fetch, and scheduler proofs using those fresh
objects. The complete fresh script has passed, including the AX core and guard, both
command branches, fetch/dispatch, and the final scheduler equivalence.
