# Arbitrary-start stepper and literal machine

`PA194StepperZip.modelStepperZip` connects the explicit primitive-recursive
encoded stepper to the imported literal `M6.Zip` machine at every ordinary
natural-number time and from every literal starting configuration. Its right
side uses the packed numeric encoding of repeated
`PA194Bounded.zipTotalStep`. The proof first establishes the arbitrary-start
bounded-run bridge from the existing one-step binding and then proves the
primitive-recursive iterator agrees with that run.

This is a standard-natural-number theorem, not by itself a PRA-internal
simulation or a PA consistency reduction. The separate all-model stepper
recurrence and its native-iPRA consequences are documented in `STEPPER.md`.
The total step stutters at a halting control, as in `PA194Bounded`.

Run `check-stepper-zip.sh` with the pinned overlay environment used by
`check-stepper.sh`; it rebuilds dependencies and checks theorem axiom reports.
Set `TMPDIR=/dev/shm` when root-disk space is limited.
