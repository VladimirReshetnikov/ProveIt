# Group the register determinism proof by control flow

The [same `run_det` theorem](../../../../../../../../Lean/BusyBeaver/ZFC/RMDag.lean) now shares its induction argument across
four car exits and four cdr exits. A non-normal car determines the node result;
otherwise its induction hypothesis fixes the intermediate register file before
the cdr is compared. The restarting case additionally aligns the next root run.
The primitive instruction cases and all other code are unchanged.

The file shrinks from 367 lines / 17,209 bytes to 302 lines / 12,989 bytes.
The exact final source passed in 2.170 seconds with zero warnings.
The [typed client](Audit.lean) passes and [reports](api.log) only `propext`,
matching the original theorem. The [independent source review](independent-review.json)
checks the case grouping and exact preservation of every public statement and
all other code.

The [result](result.json), [source record](source-check.json), and
[client record](api-check.json) bind the accepted bytes. The
[execution archive](execution.tar.gz) and [index](execution-index.json) retain
failed drafts and the rejected `grind` experiment, which compiled but used
additional classical/quotient axioms. No draft object supplies the final check.
The final endpoint rebuild is recorded [separately](../lean/README.md).
