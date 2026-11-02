# External compact44 selector, copy and low-mask checks

The fail-closed [checker](check.py) pins the retained compact44 builder,
transition and coefficient-binding JSON, original ordered 943-row JSON and
the Lean tile-value formula. It calls the retained builder's read-only
`recipe()` function, compares all 943 ordered rows (including start row 0 `(2,435,3,1)` and
forbidden row 1 `(5,0,0,0)`), checks every selector
coefficient `1+2¹⁰(2⁴¹−vᵢ)`, and checks each of the 41 copy/anchor
coefficients against `2^(10+j)`. It also computes the recipe’s K in memory
and compares it with the selected retained candidate’s decompressed K bytes
(raw SHA-256 `c6d523bd32af8dd0345db843cdadf6932bfcad186912a6d112314b60657c554e`).
It also reconstructs β, MC and `MF_source = MF_native + β` (one shift),
compares all four values to the selected retained payloads, and checks the
standard-integer mask population total 590069 and port inequalities. The 41
positions are reconstructed from the
pinned builder offsets and binding permutation, checked distinct and inside
the 8,807-position cell, and checked to exclude dummy positions 1063/1064.
`E` is the 986-position union of 943 selectors, these 41 positions and the
two dummies.

For `MF_native`, it verifies all 8,807 finite radix digits, including origin
4 and the two clause-target digits `μ=2⁵¹−2`; model-level repetition and the
origin decrement in `MF_native·J−1` are separate proof obligations.

The checker independently evaluates the retained `MC` arithmetic recipe in
memory, checks equality to the selected retained candidate’s decompressed
`MC.bin.gz` bytes, and checks all 8,807 base-2⁶⁷ digits against the recipe.
In particular, position 1 is `ρ−1`, position
1063 is `ρ−4`, position 1064 is `ρ−2`, all other selector positions and all
41 copy/anchor positions are `ρ−2`. This matters when formalizing the mask:
once the all-model MC digit identities and local no-carry relations are
established, the forbidden selector should be zero, the 1063 dummy may range
from 0–3, and ordinary selector/copy positions should be Boolean. The old uniform-Boolean
`low_mask_decode`/`CarryInput.boolean` interface cannot be applied to all
positions without explicitly treating the special cases. Neither dummy is a
copy slot or contributes to the 41-bit W bound. These are finite external
checks and a model-proof obligation, not an all-model mask theorem.

The 0–3 dummy also prevents inferring a universal zero-carry condition from
the old Boolean-input carry argument. A possible replacement is a global
carry estimate for digits bounded by 3, followed by a clean target and
predecessor reset; the separate finite-support analysis identifies an
anchor-only cross-intersection relevant to that route. The checker confirms
externally that the support shifts for 4393 and 5495 are disjoint and those
for 2195 and 3296 intersect only at 0, all modulo 8807. For the two target
predecessors, the intersections `D₄₃₉₂∩D₅₄₉₄` and `D₄₃₉₂∩D₅₄₉₅` are
empty while `D₄₃₉₃∩D₅₄₉₄={2198}`; the exceptional intersection comes
from the ordinary anchor positions 2195 and 3296. The checker also exhausts
all 8,807 standard phase residues: for each, one of the two targets has a
temporal source outside E and its predecessor source is not dummy 1063.
This uses a single-residue source map as a finite hypothesis: a fractional
bit rotation may combine adjacent radix digits, so it does not itself prove
the actual temporal digit, the model-level cyclic transport, or a clean
predecessor. Neither the global
estimate nor the local reset or their application to this graph is proved
here. A separate calculation from the retained recipe gives
`ρ=147573952589676412928` and `M=29613572795083482608`: the existing
`4M+8 < ρ` holds, whereas `12M+8 < ρ` does not. Thus naively tripling M
would not preserve that particular slack inequality; this does not settle a
sharper estimate or the local-reset route. The checker also reproduces a
local arithmetic counterexample: `S=2⁵¹−2¹⁰` is not disjoint from the
mask, but adding the nonzero temporal contribution `2¹⁰` yields `2⁵¹`, which
is disjoint. Thus an output mask alone does not justify decoding S; this is not
a claimed graph zero.

Input hashes are checked before and after execution; this does not exclude
transient changes between those checks. The [observations](observations.json)
record actual normal and controlled
runs exiting 0, mutated selector and copy coefficients rejected by the same
validation function, and optimized Python rejected with exit 1. Reproduce
from this directory with

```
python3 -I -S check.py --negative-controls
```

The spatial monomial in K is `B·DR=ρ^(8807+42)`; 42 is only its residue
modulo the 8807-position cell, not its full exponent.

This does not prove that the Lean graph uses the recipe's materialized K,
that the four actual literal ports are the selected original tuple, that the
943-row language simulates K215 in every model, or that a checker, iPRA
proof, or final consistency equivalence has been established. The builder's
`recipe()` is executed, not its output-writing `materialize()` routine.

A preliminary one-off K check used the nonexistent filename `K0.bin.gz` and
actually exited 1; the subsequent check uses the retained `K.bin.gz`.
