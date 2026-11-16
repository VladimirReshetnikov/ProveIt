# Exact physical clock for the site-27 zero branch

`PA194Site27ZeroExactClock.zeroTo5Exact` and `zeroTo11Exact` give exact
clocks for the initial physical path. `PA194Site27ZeroClockPhysical` continues
through rollback, the header scan, and the site-31 path. Its
`zeroBranchWithFile` theorem uses a concrete clock expression built from the
existing primitive-recursive segment cost operations. The theorem holds in
every PRA model, with arbitrary model-valued remaining registers, padding,
spare and suffix and with the tested logical register 0 equal to zero. It
retains the complete register-file encoding. The mixed-overlay scratch checks
passed without `sorryAx` (`/tmp/pa194-site27-zero-exact-clock-v3.log` and
`/tmp/pa194-site27-zero-clock-physical-v2.log`).

`check-site27-zero-exact-clock.sh` extends the existing both-branches source
replay with these two exact-clock modules, auditing their source hashes and
reported axioms. It takes the nine arguments of
`check-site27-controller-both.sh` followed by the directory holding the two
new sources. The staged replay passed with exit 0; its log is
`/tmp/pa194-site27-zero-exact-clock-replay.log`. The selected machine and
foundation stages remain prebuilt, and the object/source audits do not
authenticate their full transitive closure.

The Code-12 transcription and its model-evaluation theorem are still in
progress and are not established by this result. Neither the model-level
physical theorem nor an existential model time alone is a native-iPRA proof of
the zero-branch execution. A native equality proof can follow once the exact
clock is expressed by a verified PR code.

Successful invocation, from the repository root:

```sh
Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-site27-zero-exact-clock.sh "$PWD" \
  /dev/shm/pa194-model-length /dev/shm/pa194-source-controller \
  /dev/shm/pa194-source-physical /dev/shm/pa194-site27-zero \
  /dev/shm/pa194-site27-coherent/build /dev/shm/pa194-termgraph \
  /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code
```
