# Exact Rocq symbolic-executor replay from a row footprint

This component supplies a checked Rocq/Coq counterpart to the earlier Lean
`proof-fusion/runtime-dependency` idea. It targets the exact maintained
`K215F.Runtime230Core` source at ProveIt commit
`cbf94cb552a3b49509e0eee80e7455d4eb5974c6`.

## Verified result

For any two transition tables `a` and `b`, any fuel, branch assumption,
target predicate, symbolic start configuration and progress flag, if the
tables agree on every row read by the execution under `a`, the executions
return exactly the same optional symbolic configuration. The generated
footprints agree as well. Both success and failure are covered.

`FootprintReplay.v` proves the generic induction, retaining the exact
`moved || m` propagation of the production executor. `Runtime215Locality.v`
proves that the actual symbolic step reads at most one table row, supplies
that row, and instantiates the generic theorem. Its `sstepWith_original` is
a definitional equality with production `sstep`; `execWith_original` is
proved by induction against production `exec`. The four table applications
are the only changes in the parameterized step body.

All ten supplied source modules were freshly compiled with Coq 8.18.0.
The five new exported assumption reports say `Closed under the global
context`; recursive `coqchk -silent` for `Runtime215Locality` exited zero.
The exact sources, commands, object hashes, log hashes and elapsed times
are in `evidence/final/receipt.json`; raw logs are beside it. The production
Rocq 9.1.0 / rocq-stdlib 9.0.0 endpoint was not rebuilt.

The two new proof files total 215 lines and 8,062 bytes. These are added
component sizes, not a measured decrease in the existing K215 proof.

## Reproduce without a repository checkout

With `coqc` and `coqchk` installed:

```sh
python3 build.py --check-sources
python3 build.py --out /tmp/k215-locality-fresh
```

The second output directory must not exist. Use `--coqc PATH`,
`--coqchk PATH`, or `--lock PATH` to override tools or the shared compiler
lock. Add `--repo /path/to/ProveIt` to read from a checkout; every dependency
must match its pinned hash. The driver never changes the checkout.

The shipped `build.py` is the portable successor of the executed driver.
`build_driver_executed.py` preserves the exact source used for the recorded
compiler run. The successor changes dependency selection to the bundled
source bytes, adds identity checks and an optional checkout route; the
compiler commands and source order remain the same. Its source-only check
was run, but a second full compiler replay of that wrapper was unnecessary.

## Application and remaining obligations

1. Compute a footprint once for the same fuel, branch, start, target and
   progress flag used by a baseline execution.
2. Prove that the new table agrees on that footprint, or on a smaller support
   set together with a proof that the footprint is included in it.
3. Reuse the baseline *symbolic computation* via `siteFootprint_replay`.
4. Separately provide the target machine's concrete symbolic-execution
   soundness theorem, register-file oracle contracts, terminal behavior and
   complete source coverage. The unchanged symbolic oracle is a dependency
   of this replay theorem; its physical implementation is not established
   merely by checking the ordinary table footprint.
5. Rebuild the exact K215 endpoint after integrating shared runtime interfaces.
   Keep startup and source/program/calculus correctness as their own layers.

This does not prove equivalence of arbitrary whole machines, does not
supply all 6,176 K215 guarded-site instantiations, and does not show a
smaller Turing machine or a measured endpoint speedup. A target predicate
which itself changes with the table needs a separate equality hypothesis;
the checked theorem uses one fixed target predicate.

The immediate practical use is to avoid re-proving or recomputing a symbolic
execution when a candidate changes rows outside its saved support. The
longer-term simplification is one owned runtime over a table interface,
instead of namespace-specific copies. A separate exact source census shows
four runtime modules repeated across eight candidates, but these copies
are generated already. That is a cross-candidate ownership and replay
opportunity, not evidence of a reduction in the single K215 endpoint.

## Provenance and trust

The machine, source programs and runtime semantics are inherited. Original
header notices and applicable licenses are retained under `licenses/`.
`provenance.json` records the exact eight dependency paths and hashes.
New core/adapter code follows ProveIt's MIT No Attribution terms; inherited
terms are unchanged. The earlier Lean locality idea is expressly credited.

The files in `deps/` are inputs, not precompiled proof objects. No `.vo`
files or compiler binaries are supplied. The recursive audit imports
BusyCoq utilities; the five reported new theorem dependency sets are closed,
which is narrower than claiming that every imported utility has no axioms.
