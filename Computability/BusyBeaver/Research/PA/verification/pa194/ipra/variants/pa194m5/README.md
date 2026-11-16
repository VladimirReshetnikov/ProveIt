# M5 constructor loop

The delivered M5 source instruction list has 3,734 entries. The generator reads
`docs/pa194_radix_family_2026-11-13/machines/5/instructions.json` below the
PA directory and checks its SHA-256
`34375509c46552ff7f5c84e24d265cdf56ecd97b41fad3da14787232aa601ca4`.
The first changed multiplier tests register 7 at source site 123. Its positive
branch visits five increment instructions on register 1 and jumps back to
123. The zero branch exits at 130.

`PA194ProgramDrain.drain` proves positive-time execution of a certified
decrement loop with any finite list of register increments. It works over any
resolved instruction list and uses the existing arithmetic model of register
files and the model's `IΣ₁` induction. The specialized
`PA194ProgramDrain.multiply` adds the coefficient times the old register 7
to register 1, clears register 7, and preserves the other registers and the
arbitrary suffix. `PA194M5Constructor.firstMultiply` applies that result to
the exact archived rows at sites 123 through 129, with a positive model-valued
source clock.

The complete source dispatch assigns malformed ordinal 3,734 and halt ordinal
3,735, both beyond the 3,734 instruction sites. `PA194M5Control.haltExecution`
checks the delivered source halt at site 10. `haltedRun` and `malformedRun`
prove that the respective configurations are fixed over every model-valued
clock. The constructor proof uses this same dispatch and iterator. The literal
binary tape simulation and radix-five consistency calibration remain open.

From the repository root, supply a checked PA194 model stage whose
`leanpath.txt` exposes `PA194ModelMPDrain.olean`. A staged primary native
literal replay contains that model dependency.

```sh
dir=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants/pa194m5
bash "$dir/check.sh" "$PWD" /path/to/checked-pa194-model /path/to/fresh-m5-output
```

The checker regenerates the source list, builds the proof modules and records
the ordered model providers and source and object hashes.

The [constructor proof](README-constructor.md) covers all 61 archived
source occurrences. The [literal machine proof](README-physical.md)
connects the archived table to the revised source interpreter.
