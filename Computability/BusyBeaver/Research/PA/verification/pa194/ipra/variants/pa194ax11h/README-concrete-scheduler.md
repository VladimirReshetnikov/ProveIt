# AX11H site 10 and concrete scheduler

`PA194AX11HConcreteScheduler.site10_iff_runK` specializes the source-orbit theorem to `stepK .top true`, `haltAtK true`, and the `runK` code. It proves, for every PRA model whose arithmetic reduct satisfies IΣ₁, that the candidate source reaches site 10 exactly when this command scheduler's halt bit is one at some model-valued time.

This equivalence explicitly assumes positive-time returning-command and site-10 halting-command contracts for every scheduler state. The contracts and the source-to-literal-machine binding are not supplied here. The full scheduler's PA-calibration proof is also separate; this module imports only its shared core definitions.

From the repository root, after replaying the initial orbit and the scheduler core, with a source-built `ConPACtlWords` provider:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants/pa194ax11h/check-concrete-scheduler.sh /dev/shm/pa194-ax11h-concrete-scheduler-repo /dev/shm/pa194-ax11h-initial-orbit-repo /dev/shm/pa194-scheduler-core-repo /dev/shm/pa194-ax11h-controller-scheduler-replay
```

The output must be fresh. The checker hashes its source and direct objects; the initial-orbit `leanpath.txt` retains the other staged transitive inputs. It rejects `sorryAx` and reports Lean axioms.
