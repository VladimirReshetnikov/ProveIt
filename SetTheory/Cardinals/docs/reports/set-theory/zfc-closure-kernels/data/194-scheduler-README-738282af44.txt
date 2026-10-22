Combined Lean component check
=============================

This standalone source bundle combines both proposed proof refactors in one
fresh build. All four enumerators use the same rebuilt numerical provider and
the restored shared six-goal implication basis. It includes 22 Lean modules:

* 12 unchanged repository providers at
  57541fe0cfe3af62b4cb58747d8d1d7c16b338d5;
* 2 restored shared-basis sources (DominatedImplication and Lukasiewicz);
* CofinalScheduler, the new generic candidate scheduling theorem;
* 4 refactored clients: EnumPerm, Enum254, Enum222, and EnumDom;
* SchedulerAudit and SharedBasisAudit, explicit typed compatibility clients;
* QuantifierCounterexample, the axiom-free payload quantifier counterexample.

The shared-basis mathematics is prior repository work, inherited from commit
49e99c5b7cc6c2e164331961de28bad3904361fd, not a new implication derivation.
The scheduler extraction credits the repository's earlier interface proposal
and existing EnumSafeStart254.complete_from result. The new contributions are
checked generic extraction, concrete clients, integration and compatibility
evidence, and the checked counterexample to an insufficient quantifier order.

Reproduce
---------

Requirements: Python 3.10 or newer, and a complete Lean 4.32.0 installation.
The Python checker uses only the Python standard library. All project sources
are included. No ProveIt checkout, Lake build, Mathlib, or network is needed.

  python3 check.py --lean /path/to/lean-4.32.0/bin/lean \
      --out /tmp/k215-combined-check

Choose an output directory that does not exist. The checker verifies every
source against source_provenance.json, sorts all project imports topologically,
and compiles each module into a new objects directory. LEAN_PATH contains only
that fresh directory. The compiler still uses the standard library supplied
with its installation. No precompiled ProveIt objects are reused.

Compiler commands use one worker and an 8192 MB memory limit. A fresh output
contains verification.json, compiler logs, and newly generated object files.
Verification receipts record source, compiler, checker, object, and log hashes,
the build order, command arguments, timings, warnings, and printed axiom reports.
The checker rejects compilation failures and reported uses of sorry/sorryAx.
The included evidence directory contains the recorded build's receipt and logs;
compiled object files are intentionally not included in the source bundle.

Exact validation scope
----------------------

This is a combined 22-module component build. It covers the shared implication
basis and its downstream Tarski, formula-code, numerical rho8, and C222/CDom
providers; the generic scheduler and all four concrete enumerator clients;
both compatibility audits; and the quantifier-order counterexample.

It does not rebuild the physical Turing-machine simulation, KEndpoint215,
or the repository's complete ZFC endpoint. It does not measure full endpoint
build times or proof-term savings. The machine transition tables are unchanged.

The source manifest distinguishes unchanged providers, inherited proof sources,
modified clients, and new modules, recording pinned repository paths and hashes.
It is an integrity and provenance record, not an additional trusted proof step:
Lean checks the bundled proofs. The check is intentionally independent of the
untrusted source generators, whose separate reproduction evidence belongs to
the shared-basis integration package.

Recorded combined build
-----------------------

All 22 modules compiled successfully with Lean 4.32.0, compiler commit
8c9756b28d64dab099da31a4c09229a9e6a2ef35. No project objects were reused.
Total compiler process time: 44.390 seconds in this run.
This is an environment-specific observation, not an endpoint benchmark.

The six warnings all come from unchanged TarskiComplete: unused section
variables and variable names. Modified sources and new audits emit none.
All 14 shared-basis typed clients and all 10 scheduler typed clients pass.

Axiom reports: the six generic implication consequences and the three
principal counterexample results are axiom-free. Scheduler reach_or_halt
and complete_at use propext and Quot.sound; run_invariant is axiom-free.
The concrete enumerator endpoint results use propext, Classical.choice,
and Quot.sound. No sorryAx or extra axiom is introduced by this bundle.
