# Literal M5 machine and revised source controller

The [archived radix-five table](../../../../../docs/pa194_radix_family_2026-11-13/machines/5/machine.tm)
has 194 working states and SHA-256
`180a0fd1f046d4cbd687b43979f0605619ad5f53054d32b9f62f33e7a3bccab8`.
The generation stage separately pins the dense table, native label map,
trie sites, and resolved source instructions.

The [initializer](PA194M5Initializer.lean) proves that the 58,320-step
literal blank run reaches the M5 source root in every covered arithmetic
`IΣ₁` model. The source has 3,734 sites, and its initial site-25 path
agrees with the primary path. The address lookup uses all 3,734 sites.
The [site checker](PA194M5Checks.lean) compares each resolved instruction
with the exact archived program, checks its physical branches and target
bounds, and verifies that halt occurs only at site 10.

The [controller theorem](PA194M5Controller.lean) compares literal
halting with reachability of site 10 in the [M5 source](README.md) at
model-valued clocks. It takes the finite site certificate as a premise.
Relating the radix-five source to PA consistency requires the separate
arithmetic calibration of its command interpreter.

From the repository root, supply the checked [M5 source](README.md)
and [PA1944L physical model](../pa1944l/README.md) stages.

```sh
variants=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants
literal=/dev/shm/pa194m5-literal
bash "$variants/pa194m5/check-physical.sh" /dev/shm/pa194m5-source /dev/shm/pa1944l-model "$literal"
bash "$variants/check-linear-coverage.sh" PA194M5 "$literal" /dev/shm/pa194m5-coverage
```
