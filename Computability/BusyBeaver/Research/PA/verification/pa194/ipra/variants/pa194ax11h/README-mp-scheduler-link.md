# AX11H ordinary-MP step for the revised scheduler

`PA194AX11HMPSchedulerLink.advance` identifies the generic MP scheduler code
with `stepK .top true` and proves the corresponding positive-time source-machine
step between scheduler frames in every PRA model satisfying IΣ₁. The shared
scheduler core must be compiled first; the source-machine side depends on the
generic MP scheduler stage. This is one command branch, not the full machine
correctness theorem.

Run `./check-mp-scheduler-link.sh PROVIDER-LEANPATH-FILE FRESH-OUTPUT` with a
provider path containing both the scheduler core and generic MP stage.
