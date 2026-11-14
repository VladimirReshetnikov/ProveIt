# Coherent replay of the first seeded PA194 instruction

`check-first-instruction-coherent.sh` extends the coherent blank-startup replay
in the same fresh output directory. After rebuilding the literal machine,
source program, startup seed, numerical stepper, dense startup certificate,
and native iPRA startup equality, it rebuilds the register-file and
source-frame dependencies from source. It then regenerates and kernel-checks
all four blocks of the 462-step literal seed-to-site-27 run, composes them
with the 58,154-step startup, and checks the native iPRA equality at 58,616
steps. The source-frame theorem separately identifies the standard source
step from site 25 to site 27 with register 8 zero and the logical file
unchanged.

From the repository root, use:

```sh
IPRA_LEAN_OVERLAY=/path/to/audited-general-ipra-objects \
IPRA_FOUNDATION_OVERLAY=/path/to/audited-foundation-objects \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-first-instruction-coherent.sh
```

The underlying coherent startup checker rejects fallback search roots
containing PA194/195/196, M6, or known standalone machine objects. Thus all
machine-specific objects used in the replay are generated in the same new
output directory. The two provided overlays still supply prebuilt general
primitive-recursive/iPRA and Foundation artifacts; Mathlib objects are also
prebuilt. This is not an all-from-source replay of those foundational
artifacts. `PA194_AUDIT_BLOCK_GROUPS=1` is only a partial startup setup check;
it exits before the complete startup and first-instruction proofs.

An independent staged replay with this same source build order completed in
`/dev/shm/pa194-standalone-replay/build`, using
`/tmp/current14-standard-fresh-build-20261104/lib` and
`/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib` for those general
objects. The first-instruction trace and blank-to-site-27 composition report
`[propext]`; the model, classical PRA and native iPRA sentence theorems report
`[propext, Classical.choice, Quot.sound]`, with no `sorryAx`. The source-frame
and first-instruction logs are `source-frame.coherent.log` and
`first-instruction.coherent.log` in that retained build directory. A separate
end-to-end run of this wrapper is in progress.

These are fixed concrete execution facts. They do not prove the arbitrary
model-length source-controller simulation or either implication relating
literal PA194 halting to `Con(PA)`.
