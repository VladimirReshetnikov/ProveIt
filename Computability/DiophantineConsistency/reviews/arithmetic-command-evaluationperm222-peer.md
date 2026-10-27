# C222 command evaluation: independent peer review

26 October 2026; reviewer `circuit_reduction`, author of neither reviewed leaf.
I previously reviewed the imported command-run and tick packets and authored
some lower parser/step leaves; that prerequisite role is distinct from this review.

**PASS.** I fully read the final 66-line main and 28-line checks, the root
replay driver, author receipt, source-derived import inventory, complete
nine-file author bundle, and the imported command-run definitions and proofs.
No source or mathematical correction is requested.

`run_eq_of_stopped_le` decomposes the later internal time and uses the actual
absorbing evaluator, rather than assuming scheduler absorption.
`stopped_runs_eq` compares the internal ordered times, giving uniqueness of
any stopped result even when either time is nonstandard. `terminal_eq_run`
uses the already proved internal drain bound. The one-step identity calls the
actual C222 tick on shifted word `raw+1`. Both `terminal_succ` branches retain
the actual permuted tail; a nonzero command result alone permits subtracting
one to decode its working state. Successful completion remains positive and
halt remains zero. The checks retain word1/raw0, both command-result branches,
and arbitrary stopped witnesses. There is no append-execution, fairness,
compiler invariant, exact215 simulation or HA equivalence theorem here.

The first independent preflight rejected one metadata record before creating
an overlay or running Lean: the newly appended command-run record listed its
two explicit imports but omitted implicit `Init`. The complete author closure
already included that boundary. I preserved `prepare-v1.py` and its exact
failure description, normalized only that record after reading its source,
and independently traversed the complete resulting import graph. This was a
metadata correction, not a source correction or compiler failure. The frozen
author packet was not edited.

The successful replay authenticated 118 current-source cached modules,
95 Foundation modules, 403 cached artifacts, 38 explicit external boundaries,
and 619 distinct source/object/toolchain/driver/evidence pins before and after
execution. No cached client imports either fresh leaf. Package/toolchain
boundaries are explicitly recorded; this is not a Foundation or full
repository rebuild. Only the two new leaves were compiled using Lean4.32.0,
`-M6000 -j1 -DElab.async=false`, fresh nonsymlink outputs and the512MiB guard.
They passed in2.362s and2.091s. The main log is empty. All six axiom reports
contain only `propext`, `Classical.choice`, `Quot.sound`, and both fresh objects
are byte-identical to the author objects. No Lean invocation failed.

Exact source pins:

- Main: `d3406e883f1a8a340c72c29d39082f167a866d2cd719fbb71b42c1593dbef798`.
- Checks: `af65af659e54d5d3043ee2c6a1ae88ae89047275285c66d31a1a1f4b6d6af306`.
- Main object: `1cbe56af570f4ca246e3cd67e6740200e679bdd00179de93bae43f9de23fc65a`.
- Checks object: `1564f3a0edba2976f36ee2f80563127e167494d7ddb06bd25ffc0558c1184198`.
- Independent [replay summary](arithmetic-command-evaluationperm222-peer-replay.json): `baea3f0577882c022af0dbd3177da13eb0fed10df472894b2d7432ae40932218`.
- Complete [replay manifest](arithmetic-command-evaluationperm222-peer-replay/FILES.json): `133f284f7fae8747abaf2d7520560ed3a5248863640da1db60dd80468b6a9712`.

Private output: `/tmp/command-evaluationperm222-independent-cwruz2om/lib`.
All source snapshots, logs, commands, object pins, author evidence and the
preflight-only failed driver are retained in the replay bundle. No frozen
source, shared dependency output, equation artifact or Git state was changed.
