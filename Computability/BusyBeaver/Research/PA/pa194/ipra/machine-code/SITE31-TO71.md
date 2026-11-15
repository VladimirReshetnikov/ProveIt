# Physical site-31 header and marked scan to control 71

`PA194Site31HeaderPassPath.firstPass` identifies the first physical header
pass's exact result as the same source-site-31 path followed by a named
transformed file suffix. `PA194Site31MarkedTo106.markedTo106` decodes that
marked path to literal control 106. `PA194Site31To71.site31To71` composes
both paths with the existing model-length scan through control 106 and reaches
control 71 with the exact clock and physical file expression shown in the
theorem. It holds in every PRA model and carries the full arbitrary source
file and suffix; it does not assume a blank spare tail. This is a prefix of
the site-31 register-0 increment, not the complete instruction.

`check-site31-to71.sh` extends the independently replayed header-pass checker
with these three modules in one output. It pins their sources and the selected
direct baseline scan object, rechecks inputs after the build, and audits
printed theorem axioms for `sorryAx`. Its replay passed with exit 0:
`/tmp/pa194-site31-to71-replay.log`. The site-27 machine baseline and general
foundations are prebuilt; selected hash checks do not authenticate their full
transitive source closure.

From the repository root, replay with:

```sh
Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-site31-to71.sh "$PWD" \
  /dev/shm/pa194-site27-coherent/build \
  /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code
```
