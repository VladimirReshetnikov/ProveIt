# The wang943-mixed-121x8801 tuple: a Lean calibration, phase 1

4 November 2026. Claude session; not a paired replay.

## Why this tuple

These frontier equations use the tuple of
[`31-sun10/coefficients`](../../con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md),
with `ρ = 2^121`, `L = 8801` and `B = 2^1,064,921`:

- package 55's and 59's fourteen-positive 52 / 79;
- package 132's fifteen-integer 44 / 111.

Package 55's `fourteen/coefficients/ports.json` names exactly the package-31
payload hashes: β `6a029139…`, K `6984850d…`, MC `7c2b3417…` and MF `28c55970…`.

The tree's Compact44 calibration does not apply. It has the same overall
shape: `K = D_C + B·ρ^42`, clause terms reflected at `4393` and `5495`, the
same 943 rows. But it uses `ρ = 2^67` and `L = 8807`. Its clause coefficient is
the complemented binary selector `1 + 2^10(2^41 − value)`. Here it is a
radix-four field code `1 + Σ bitⱼ(x+512)·2^(10+2j) + anchors`. The decoding
layer must therefore be proved afresh.

## Phase 1: the symbolic kernel

[`Mixed121/Mixed121Kernel`](../../Lean/DiophantineConsistency/Mixed121/Mixed121Kernel.lean)
defines:

- the parameterized kernel `paramKernel r`, from the tree's
  `Compact943Data.rows`;
- the 44 copy and anchor positions;
- the 989-position support `E`.

It proves:

- the all-model cast identity `cast_paramKernel`;
- that `E` has 989 distinct positions, all below `4393`, and contains the 44
  copy and anchor positions;
- the two difference facts of the recipe's §2. `1102 ∉ E − E`, so the clause
  targets are disjoint modulo `L`. `1101 ∈ E − E` only as `3296 − 2195`, so
  the anchor targets meet only at zero;
- that every tile label is below 512.

The difference facts are not checked as list scans. Stated as
`E.all (fun e => !E.contains (e + 1102))` under `decide +kernel`, one of them
ran for more than twelve minutes without finishing, and the module took 6.9
hours to build. The module now checks them on the bitmask `m = Σ_{e∈E} 2^e`,
as `m &&& (m >>> 1102) = 0` and `(m ^^^ 2^2195) &&& (m >>> 1101) = 0`. The
kernel evaluates these operations natively. Two induction lemmas,
`testBit_maskOf` and `mem_of_testBit_maskOf`, transfer the results back to list
membership. Distinctness comes from a linear strictly-increasing check on the
sorted support.

[`tools/check_recipe.py`](tools/check_recipe.py) implements the recipe of §1
from the Lean rows. It checks that the rows are the package's
`wang943_tiles.json` in order. It then reproduces all four little-endian
payloads exactly: β 1,064,921 bits, K 1,070,004, MC 1,064,921 and
MF_source 1,064,922. This is finite external evidence for the transcription,
not a Lean theorem about the files.

## Phase 2: clause decoding

[`Mixed121/Mixed121Decoder`](../../Lean/DiophantineConsistency/Mixed121/Mixed121Decoder.lean)
proves the recipe's §2 decoding argument in every model of `𝗜𝚺₁`, generically
in the index type and the number `m` of radix-four fields. Consider a selector
vector `f` with Boolean entries, clause coefficients
`1 + 2^10·Σ_{k<m} b_ik 4^k`, and Boolean copy/anchor digits `g_k`. Suppose the
clause sum has no carry against `(2^10 − 2) + 2^10·Σ_{k<m} 4^k`. Then either
nothing is selected and every `g_k = 0`, or exactly one `i` is selected and
`g_k = b_ik` for all `k`.

The proof follows the recipe's order. First the low ten bits, which are
exactly the selector count, give `n ≤ 1`. Only then does each radix-four field
hold a digit below four, so that `noCarry_dsum_iff` at width 2 forces it into
`{0, 2}`. No carry-freeness of the upper fields is assumed.

[`Mixed121/Mixed121Digits`](../../Lean/DiophantineConsistency/Mixed121/Mixed121Digits.lean)
puts the actual coefficients into that form, for an arbitrary tile and so
without evaluating the row table. Every `clause tile` equals
`1 + 2^10·Σ_{k<44} digit_k 4^k`. The digit `10t + j` is bit `j` of
`x_t + 512`, and the four anchor digits are 1. Each extra weight is
`W k = 2^10·4^k`, and the native clause-target mask
`μ = 1022 + Σ W_k` is the decoder's mask at `m = 44`.

## Remaining phases

Measured against the Compact44 calibration, which is 472 modules plus the
endpoint layer:

1. binding the decoder's `f` and `g` to the native assignment's values at the
   clause targets and at the 44 copy and anchor positions;
2. the carry and padding bounds at `ρ = 2^121`, using the recipe's threshold;
3. the spatial and temporal overlap identities, and the binary-alignment
   argument for `b = 121`;
4. the packing, rank and controller layers. Compact44's `PackingInput d` is
   already parametric in `d`;
5. halt data, leaf facts and the equation endpoints for 52 / 79 and 44 / 111.
