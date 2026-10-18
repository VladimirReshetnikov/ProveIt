# Exact prefix250 symbolic execution

`SymbolicPrefix250.lean` proves that a successful symbolic execution check yields a positive run of the exact 250 table, with the complete infinite tape represented at both ends. Register values and the affine gap parameter remain arbitrary natural numbers. The final halting theorem preserves the literal write and move performed by the halt transition.

The executor uses the checked exact 250 marking and register-box contracts. A valid file has at least ten blocks: nine primary registers and at least one spare. Increment appends a value-one spare. Positive decrement preserves the spare suffix and moves the physical file boundary right one cell. Zero decrement restores the file and returns through old 112; subsequent phase-bit steps are literal transitions. These effects replace the former 252 spare convention. Computation uses the checked balanced transition table, with every semantic step related to `machinePrefix250`.

The root's sole attempt passed the 826-line source and 87-line audit, with 14 named axiom probes, 14 typed callers and no warnings. All probed statements depend only on `propext` and, except the finite selector lookup, `Quot.sound`. The source, audit, executed guard, raw logs and result remain in the history artifact. The source object was recorded before the audit and its exact hash remained unchanged afterward.

Successful record SHA256: `68360e32a1d7aef0568f9f7e987c7922da7c856ac468557a80293ac646367fd8`.
Source SHA256: `dae576d8256699e8beac0fe22fb396f45570b1971d58f212905d3c1a7a214c65`.
Audit SHA256: `ab46bc30dc483a7c54e2a4398d430c01bdef1db163e409e96e324ef75f095076`.
Fresh object SHA256: `26f037fcd0551a2301f8c1355b98cce7a83c95c164acdc9b7c65da21f93593de`.

The guard pins the successful Boxes, Mark and Fast records, reuses twelve exact project source/object providers, and checks the complete import closure and actual first-provider resolution. Init and Omega are toolchain boundaries; there are no external project-library boundaries. All 42 current inputs were rehashed by the final author evidence review. The guard explicitly distinguishes Boxes/Mark's recorded pre-audit object timing from Fast's record, which verifies its final object without exposing that stronger timing field.

The two proof commands run serially with one thread, 4096 MiB, a shared 120-second budget and default elaboration limits. Publication changes only the guard's source/audit default paths. A root can prepare maintained defaults without compiling or querying a compiler version:

```sh
python3 Computability/BusyBeaver/Research/ZFC/check_prefix250_symbolic.py \
  --repo "$PWD" \
  --boxes-evidence Computability/BusyBeaver/Research/ZFC/results/prefix250-boxes-verification.json \
  --mark-evidence Computability/BusyBeaver/Research/ZFC/results/prefix250-mark-verification.json \
  --fast-evidence Computability/BusyBeaver/Research/ZFC/results/fast-table-prefix250-verification.json \
  --output /tmp/prefix250-symbolic-fresh-preparation --prepare-only
```

This command requires the supplied pinned provider objects and performs no dependency build. The author reviewed the complete source and final evidence; the root independently read the source and guard and executed the check. No additional independent child review is claimed.

The site checker, all 8,391 original instruction cases, dispatch-frame preservation, literal blank bootstrap, exact 250 consistency theorem and the requested PA-internalized equivalence remain separate obligations. The encoded source program retains its original 6,460 leaves. Mira-Cult, Jeff Ketchersid and Wade retain their original machine, verification and compiler attribution; the shared-carry construction is the ProveIt contribution preserved from incoming source 58 (`126d12e470`). The symbolic framework is adapted from the maintained `SymbolicPerm252.lean`.
