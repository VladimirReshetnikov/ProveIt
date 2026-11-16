# AX11H initial source orbit

`PA194AX11HInitialOrbit.site10_iff_scheduler` specializes the candidate site-10 orbit theorem to the actual initial source state, standard scheduler seed and scheduler source frame. It accepts arbitrary unary step and halt-flag codes. Its explicit premises are a positive-time source return for every nonhalting command and a source path to site 10 for every halting command. Neither contract is established here.

`PA194AX11HDropOrbit.iterate_eq_drop` identifies the source orbit's iterator definitionally with `PA194StackCode.dropCode`; `site10_iff_drop_scheduler` expresses the conditional equivalence in the iterator form used by the command schedulers. These are model-level results for PRA models whose arithmetic reduct satisfies IΣ₁, not a literal-machine equivalence or a native iPRA theorem.

From the repository root, using the previously replayed candidate source orbit and scheduler frame:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants/pa194ax11h/check-initial-orbit.sh /dev/shm/pa194-ax11h-initial-orbit-repo /dev/shm/pa194-ax11h-source-orbit-repo /dev/shm/pa194-scheduler-source-frame-repo-v4
```

The output must be fresh. The checker records the source and direct input hashes. Transitive imports are retained from the source-orbit output's `leanpath.txt` and the scheduler-frame provider. It rejects `sorryAx` and reports Lean axioms.
