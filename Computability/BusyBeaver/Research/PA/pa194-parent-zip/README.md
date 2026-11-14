# PA194 parent full-tape and zipper bridge

`PA194ParentZip.lean` proves that a transition table's full two-way tape and
its zipper representation stay synchronized at every standard finite step.
For the unfolded PA194 parent, `parent_halts_iff_zip` relates reaching native
halt control 254 in the quotient's full-tape semantics to the runtime zipper
machine becoming stuck, from any related configurations with a valid parent
control. `rowMachine parent` is definitionally the table used by
`PA194RuntimeEngine.machine`.

The theorem is about ordinary finite runs in Lean; it does not establish
internal PRA/iPRA execution semantics or either consistency implication. Its
source was checked with independently rebuilt local dependency objects, with
no `sorryAx` in the printed theorem dependencies. The standalone fresh rebuild
below was initiated but not completed during the long coverage and startup
checks; its completed status is not claimed here.

From the repository root, run:

```sh
Computability/BusyBeaver/Research/PA/pa194-parent-zip/check.sh
```

The script builds its local dependencies in a private temporary directory.
The finite quotient table's connection to the supplied archive is described
in `../pa194-quotient/README.md`.
