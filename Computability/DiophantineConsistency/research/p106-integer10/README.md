# Package 106: iPRA endpoints for the four ten-integer equations

Equations: `con-zfc-diophantine-forms/106-compact-certificates-round13/norm/integer10_{polar,linear,cubic,sixterm}.json`,
ten unrestricted integer unknowns `t g0 c0 k0 l w x y z m`, with 467, 470, 473 and 507 operations,
at the four ports of the 121x8801 machine (`Mixed121Ports.ports`).

## Lean

All modules are in `Lean/DiophantineConsistency/Z10/`.

| Layer | Modules |
| --- | --- |
| registers | `Z10Regs` (prefix, signed Pell certificate, polar value, the three shears) |
| soundness (zero ⟹ halt) | `Z10Bootstrap`, `Z10Squares`, `Z10Carrier`, `Z10Guard`, `Z10Lucas`, `Z10Cert`, `Z10Index`, `Z10KIndex`, `Z10Size`, `Z10ExpCong`, `Z10BridgeSound`, `Z10Prefix`, `Z10SparseCentral`, `Z10Contract`, `Z10Sound` |
| completeness (halt ⟹ zero) | `Z10Code`, `Z10Ratio`, `Z10BridgeComplete`, `Z10Interp`, `Z10Complete`, and `ZRows/Intersective23`, `ZRows/PellNegBase` |
| syntax | `Z10SyntaxPolar`, `Z10SyntaxLinear`, `Z10SyntaxCubic`, `Z10SyntaxSixterm` (generated) |
| endpoints | `IPRAInteger106` |

`IPRAInteger106.{Polar,Linear,Cubic,Sixterm}` each prove `native_equivalence`,
`standard_equivalence` and `reference_equivalence`. In the native and the standard iPRA theory,
"the equation has no integer zero" (`nativeNoZero (signedSplit expression)`) is equivalent to the
native rendering of "machine 215 does not halt", and so of Con(ZFC). The reference endpoint is the
order-erased form of the same equivalence in the equality-only reference theory. The axioms are
`propext`, `Classical.choice` and `Quot.sound`.

The three variants are translates of polar: their value is polar's at `m + shear`, where the shear
does not read `m` (`Z10Regs.exists_shift`).

## Tools

`tools/gen_literal106.py FORM [--check]` generates the syntax modules and checks them. It checks the
SHA-256 pin of the JSON file and the operation counts. It also checks every closed form, prefix
function, register, shear and the output against an independent model of `Z10Regs`, using exact
integers modulo a 127-bit prime at random points. With `--check`, it confirms that the file on disk
regenerates byte for byte. The layout tables (weights, targets, kernel positions and coefficients)
come from package 105's `generate_n105_layout.py`.

## Correction found by the generator

The sixterm JSON multiplies the second six-term quadratic by `y · ξ · E0 · 16`. `Z10Regs.sixT` had
the register `Ω` in place of the literal `16`. The difference factors through `Ω − 16`, and `Ω` does
not occur in the JSON's shear. `Z10Regs.sixT` now follows the JSON. The proofs were not affected:
`exists_shift` holds for every shear that does not read `m`.
