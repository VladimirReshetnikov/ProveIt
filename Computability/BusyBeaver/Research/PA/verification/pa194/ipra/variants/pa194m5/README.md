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

This stage covers the source arithmetic and the delivered loop rows. It uses
the original controller's dispatch code for increment, decrement, and jump.
A complete controller for the larger source list requires separate malformed
and halt ordinals beyond its instruction sites. The literal binary tape
simulation and radix-five consistency calibration are independent proof
obligations for the final M5 endpoint.

From the repository root, supply a checked PA194 model stage whose
`leanpath.txt` exposes `PA194ModelMPDrain.olean`. A staged primary native
literal replay contains that model dependency.

```sh
dir=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants/pa194m5
bash "$dir/check.sh" "$PWD" /path/to/checked-pa194-model /path/to/fresh-m5-output
```

The checker regenerates the source list, builds the proof modules and records
the ordered model providers and source and object hashes.
