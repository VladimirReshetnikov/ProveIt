EXACT DEPENDENCY TRANSPORT FOR THE K215 SYMBOLIC EXECUTOR

Status: newly compiled conditional Lean theorems against the maintained
production definitions at ProveIt commit
6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95. No new whole-machine endpoint or
alternate-machine correctness result is claimed.

Files
  BusyBeaver/ZFC/KRuntimeDependency.lean
  BusyBeaver/ZFC/KRuntimeDependencyAudit.lean
  build_runtime_dependency.py
  checked/build_receipt.json and checked/logs/*.log (accepted run)

The earlier history/attempt1.* records a failed first proof of list-membership
bookkeeping. Its reported sorryAx is failure evidence and is excluded from the
accepted run. The accepted module and client have zero compiler warnings.

Reproduction (Lean 4.32.0):
  python3 build_runtime_dependency.py --repo /path/to/ProveIt \
    --lean /path/to/lean --out /tmp/k215-dependency-check

The driver compiles six pinned production dependencies and the two supplied
modules into a separate output directory. It takes the project's shared build
lock and records source, object and log hashes. No repository file is modified.
The source commit and Lean version are checked. The exact existing compiler is
the trust boundary; the full 178-module K215 endpoint is not rebuilt here.

MATHEMATICAL CONTENT

For a source table M, a fixed branch assumption br, a target predicate tgt,
fuel f, symbolic start s and initial progress bit moved, traceReads computes
the direct lookup keys encountered before success, failure or fuel exhaustion.
Every complete option-valued row is compared, including an absent row.

The main practical theorem home_exec_transport_of_cover assumes:
  (1) KHomeReady.ready M = KHomeReady.ready N;
  (2) every source-trace lookup belongs to a saved finite support K;
  (3) M and N agree on every complete option-valued row in K.
It proves exact equality of the actual maintained KHomeReady.exec results.
The target predicate, branch, fuel, starting symbolic state and initial
progress bit are the same on both sides. Equality therefore preserves both
failure behavior and successful result; each intermediate progress bit is
preserved by the local theorem as well.

Condition (2) is a one-time source certificate. Retain it as an opaque theorem
for each baseline guard, then prove only (1) and (3) for a later table. The
finite sameOn check discharges (3). Without saved support-cover theorems,
reducing traceReads again for every target would repeat the old execution and
would not deliver the intended speed benefit.

The concrete theorem reused_exec_sound separately requires BoxLemmas N. It
combines exact execution transport with existing production exec_sound to
obtain a target concrete reachability proof. If moved = false, this proof is
strictly positive. Oracle success has no DIRECT table lookup, but its physical
soundness still depends on target BoxLemmas; that dependency is not erased.
Similarly, a successful Home shortcut has no per-state direct table lookup,
but its table readiness is checked separately and retained explicitly.

The core theorem uses only propext. sameOn_sound additionally uses Quot.sound.
The concrete semantic corollary uses precisely propext, Classical.choice and
Quot.sound, inherited from the maintained semantic library. There are no
new axioms, sorry declarations or native_decide calls.

PROOF STRUCTURE

The finite case split sstep_local checks every production sstep branch:
left run, right literal bit and right run read their (q,b) row; a successful
table-independent box oracle reads none; a failed oracle reads (q,false);
reorientation and malformed-input branches read none. Consequently agreement
on those keys gives equality of the entire option-valued step result,
including its Bool flag. Fixed Home mode adds a table-independent shortcut
case. Fuel induction then transports execWith, following precisely the
source's stopping test and source successor. Readiness equality connects
the two fixed-mode executions to the actual wrappers.

The audit client checks missing-row inclusion, successful oracle independence,
failed-oracle fallback, positive Home progress, and differing outcomes under
different Home modes despite empty direct read sets. The wrapper client keeps
readiness equality explicitly in its type.

RELATION TO EARLIER PROPOSALS

This implements and extends the uncompiled dependency-transport design in
verification/k215/simplification/proposals/rocq-composition/runtime/
DependencyTransport.lean.proposal. The earlier proposal identified the need
for a generic trace theorem and interpreter-local footprint proof. The new
work checks the exact production interpreter and active Home wrapper, adds
a reusable saved-support interface, and supplies freshly compiled receipts.
The idea itself is not claimed as newly discovered.

REMAINING INTEGRATION

Generate and kernel-check support-cover certificates for the actual baseline
site/branch executions. Prove target table readiness and target BoxLemmas.
For an unchanged guard, use the old successful execution theorem plus the
saved support theorem and finite target row check. Recheck any affected guard
whose support intersects a changed row or whose branch, start, target or
source meaning changed. Keep complete coverage, blank startup, source
correctness and endpoint composition obligations. For halt leaves, retain
the separate terminal-row premise of KSim.runHalt_sound: both rows at the
terminal state are absent in the target table. The trace stops upon reaching
its target, so its lookup support alone does not verify those terminal rows.
No new speedup, final
endpoint size or number of successfully reused guards is established by the
generic formalization alone.
