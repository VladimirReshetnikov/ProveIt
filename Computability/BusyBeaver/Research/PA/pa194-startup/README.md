# PA194 parent blank startup

`generate.py` reads the hash-pinned unfolded PA194 parent table and produces
456 candidate checkpoints for the 58,154-step native blank startup. These
checkpoint values are untrusted: each of the 455 connecting runs is separately
checked by Lean's kernel using the imported, proved `PA196.FastRun` evaluator,
and Lean checks that the final checkpoint equals the formal source-site-25
frame with the exact complete initial register file and 26 one-valued spare
blocks. When all blocks pass, the generated `PA194StartupComplete.lean`
composes them into `startup_exact` and `startup_reach` for the exact PA194
unfolded parent.

From the repository root, rebuild pinned dependencies and check every block:

```sh
Computability/BusyBeaver/Research/PA/pa194-startup/check.sh
```

For a smaller independently reproducible check, pass `--start-block 0
--stop-block 10`. The generator always checks the expected number of
checkpoints and hash of the source table; producing them does not mean their
connecting Lean proofs have all passed. All temporary artifacts use `/dev/shm`.

This is a standard-Lean finite startup certificate. It does not alone prove a
full source-to-machine equivalence, a PA/PRA/iPRA theorem, or consistency of PA.

The completed full-run result, input hashes, and theorem scope are recorded in
[`verification.json`](verification.json).
