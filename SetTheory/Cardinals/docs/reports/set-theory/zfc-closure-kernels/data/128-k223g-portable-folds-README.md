# Certified 226 → 223 contextual fold chain

Run `python3 check_folds.py --output fold_certificate.json` from any directory.
The checker uses only the Python standard library. `folds.json` pins the two
literal table hashes and supplies three transformations with their minimal
inductive invariants. The checker imports no search code or repository code.

The files prove that `parent226.k.tm` and `candidate223.k.tm`, started in
state 0, halt together for **every initial binary tape and head position**.
The separate halt label is 254. There are 223 working states and 446 rows in
the final table, and all declared working states are graph-reachable.

This local equivalence certificate does not by itself identify the parent
machine with proof search or Con(ZFC). The source derivation and quantified
runtime proof establish that premise separately. The parent here is the
G-source table after the closed right rotation repairing its maximum zero
run to six (`source-work/g-zero6/candidate0.k.tm` in the research workspace).

The fold order matters:

1. Merge 191 into 157, using predecessor-bit routing through states 67 and 187.
2. Merge 303 into 118, filling the old unreachable read-one row of state 118.
3. Merge the now identical state 302 into state 159.

The old invariant that state 118 scans zero is used only before the second
fold. Afterwards that row is intentionally reachable through old state 303.
The independently checked proof composes simulations and does not apply
that obsolete invariant to the final machine.

`fold_section.tex` contains a report section explaining the mathematical
proof. `negative_controls.json` records rejection of three deliberately
incorrect certificates. `fold_certificate.json` is the positive receipt.
