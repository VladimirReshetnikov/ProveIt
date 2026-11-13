# Independent terminal artifact audit of split initial agreement

PASS for the scoped eight-stage artifact review. All seven three-node group stages and their final assembly recorded dependency-scan and Lean-compile exits 0, without monitor stops. Source snapshots, manifests, all sixteen logs, eight object hashes, local stage-to-stage routes, 1,100 recorded direct guard slots and 1,067 overlay links were rechecked. The group logs contain 19 linter warnings; the assembly's exact axiom report is `[propext, Classical.choice, Quot.sound]` with no warnings.

The final `initial_agreement` statement is textually identical to the previously attempted unsplit theorem, and the assembly invokes initial-node facts 00–20 once each. In IΣ₁ models it asserts agreement between the static signed-pair valuation and reference valuation on the 21 initial nodes; the first fourteen witness coordinates are shifted by one. This theorem does not establish the full terminal agreement or source/iPRA equivalence.

The retained author observation reports session 3891's `PASS` stdout, but **does not contain a numeric outer exit**; no exit code is inferred. The state separately records PASS and all eight Lean-child exits 0. A point-in-time `/proc` scan at audit did not observe the runner, which is not proof of an earlier process history. Objects remain in the temporary provider. No Lean was replayed; direct guards and resource samples are point observations, and deeper package/dynamic ancestry is inherited.

Reproduce while temporary artifacts exist using `python3 -I -S -B check.py`. Checker SHA-256 `25d0cc2e97e9d42f76de780723e8d0edf0acdc81cfbbec0c6cda86096769d144`; result `dbff3cafab5e622810f3dcb48f381fbea06288ed777584dc7a417d9858afbe8b`.
