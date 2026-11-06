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

## Phase 3a: one reflected clause band

[`Mixed121/Mixed121Band`](../../Lean/DiophantineConsistency/Mixed121/Mixed121Band.lean)
is the 121-bit analogue of Compact44's `CompactPartialBand`. Let `C` be an
`n`-cell native word in radix `2^121`, and let `T` be a clause target. The
band's selector and copy/anchor sum reads the digits of `C` at the cyclic
source cells `T − e`. `band_decomposition` rewrites this sum into the
decoder's input form. `band_decode` then concludes the following, given
Boolean source digits and no carry against `μ`: either the band is empty, or
exactly one tile is selected and all 44 copy and anchor digits equal that
tile's radix-four digits. Identifying this band with a column of the full
packed product is the overlap identity of the next phase.

## Phase 3b: the kernel as rotated bands, and the carry room

[`Mixed121/Mixed121Rotation`](../../Lean/DiophantineConsistency/Mixed121/Mixed121Rotation.lean)
generalizes Compact44's `BandCarryInputs` and `GenericBandCarryFamily` to an
arbitrary width `w`. Their proofs used `67` only as the width. It proves:

- `band_rotation_congr`: the 121-bit band rotation modulo `2^(121n) − 1`;
- `combined_congr`: the same for the full product;
- `kernel_bands`: in every model, the concrete kernel is
  `kernelBand 4393 + kernelBand 5495 + bareKernel`, with bare terms
  `ρ^30, ρ^62, ρ^1100, ρ^2200, ρ^8843`.

[`Mixed121/Mixed121Flatten`](../../Lean/DiophantineConsistency/Mixed121/Mixed121Flatten.lean)
puts the bands into Compact44's width-free aligned family
`Aligned (Fin 943) (Fin 44)`. It writes each raw column as two decoder inputs
plus the bare column and the temporal digit (`decoder_bands`). It also proves
the carry room `3·mass + 1 < 2^120` (`aligned_room`), the in-Lean counterpart
of the recipe's §3 threshold. The proof needs no row evaluation: each clause
coefficient is below `2^99` by its digit form, and each `W k` is below
`2^98`.

Build-time lessons:

- `norm_num` with `Finset.sum_range_succ` or `Fin.sum_univ_succ` in its simp
  set unrolled a 943-term selector sum. Generalizing each sum to an atom before
  `norm_num` fixed it.
- `congr 1` exhausted the recursion depth by unfolding `Compact943Data.row`.
  Explicit `sum_congr` rewrites replaced it.

## Phase 3c: ports, masks and the first `LeafFacts` link

The `Compact44/Facts/` halting chain takes `CompactLeafFacts.LeafFacts p v`
at the ports `p`. Its four leaves are port-generic. These four modules supply
what the next layer needs at the 121x8801 ports:

- [`Mixed121Ports`](../../Lean/DiophantineConsistency/Mixed121/Mixed121Ports.lean)
  defines `β = 2^(121·8801) − 1`, `K`, `MC` and `β + MF_native` as symbolic
  naturals. `MC` is a `CompactListMask` digit list, and `MF_native` is an
  explicit replicate list. The module proves the leaf bounds `0 < β`,
  `MC < β`, `β + MF < 2β`, `46 ≤ β` and `β + 1 = 2^d` without materializing a
  numeral. [`tools/check_ports.py`](tools/check_ports.py) rebuilds `MC` and
  `MF_source` from the lists and matches the payloads.
- [`Mixed121Masks`](../../Lean/DiophantineConsistency/Mixed121/Mixed121Masks.lean)
  proves the five mask facts of the port-generic saturation client:
  `popcount(MC) = d − 989`, `popcount(MF) = 989`, their sum `d`, `MC` even,
  `MF ≡ 4 (mod 8)`, and both masks below `2^d`.
- [`Mixed121Increment`](../../Lean/DiophantineConsistency/Mixed121/Mixed121Increment.lean)
  is a mechanical width-121 port of `CompactDummyBound`,
  `CompactMixedIncrement` and the model part of `CompactListMask`. Only
  `67/66/65` become `121/120/119`. Its `recipe_digits` gives native cells
  `dig C 0 = 1` and `≤ 3` from the low-mask no-carry.
- [`Mixed121Aligned`](../../Lean/DiophantineConsistency/Mixed121/Mixed121Aligned.lean)
  composes these with Compact44's port-generic
  `graph_aligned_congruence_facts` and `graph_saturation_facts`. Its
  `symbolic_aligned` is the counterpart of `symbolic_aligned_facts`. From
  `LeafFacts` at the 121x8801 ports it gives:
  - `q = 2^(dN)` and `J = rep(d, N)`;
  - the first-pair congruence;
  - the native cell bounds.

Kernel lesson (it cost a 47-minute build). The kernel must never compare two
non-identical terms under a Nat operation while a concrete mask is inside. Its
Nat-literal extension then evaluates the mask to a numeral: 8801 digits, each
with a support lookup. `unfold`/`delta` under `% 2`, `digits B (8800+1)`
against `digits B 8801`, and a typed `Finset.sum_range_succ'` instance all
triggered it. The module uses `rw` with `rfl` definition lemmas instead,
literal-form instances (`digits_8801`), and arithmetic over variables. It now
builds in under a minute of elaboration.

## Phase 3d: up the halting chain to a clean clause column

Six more links of the `LeafFacts` halting chain now hold at the 121x8801
ports. Each is the counterpart of a Compact44 `Facts/` theorem:

- `Mixed121Bands`: saturation (`saturated_aligned`) and the rotated-band
  congruence (`symbolic_bands`);
- `Mixed121Temporal`: the position no-carry and the temporal word;
- `Mixed121Carry`: the band family's `CarryInput`, its mass hypothesis
  following from the carry room;
- `Mixed121Clean`: the hull `Bad`
  (`x ≤ 1065 ∨ x ∈ {1095, 1096, 2195, 3296}`; Compact44's omits the second
  anchor 1096), with zero cells outside it and Boolean cells off the dummy;
- `Mixed121Source`: a safe zero source at one clause target for every
  temporal phase;
- `Mixed121CleanCarry`: a clause target `t` with zero carry into `t + 1`,
  where the graph digit equals the raw band column.

The bit-rotation argument underneath (the recipe's binary alignment for
`b = 121`) is 21 Compact44 modules whose width enters only as a literal.
[`tools/width_port.py`](tools/width_port.py) ports them mechanically to
`Mixed121/W121/`. It substitutes `67/66/65` with `121/120/119`, renames
namespaces to `W121.X`, and refuses any module that mentions the period
`8807`. Every port built on its first attempt. The two carry-reset files
were then retargeted at `Mixed121Rotation`'s width-generic carry family.

## Phase 3e: the decoded selection inside the chain

- [`Mixed121Single`](../../Lean/DiophantineConsistency/Mixed121/Mixed121Single.lean)
  is the counterpart of Compact44's foreign-band and single-band links. At
  either clause target, the other band's sources (the support shifted by
  `∓1102`) and the bare sources (offsets `30, 62, 1100, 2200, 8843`) lie
  outside `Bad`, so the clean graph digit is one band's decoder input alone.
- [`Mixed121Selected`](../../Lean/DiophantineConsistency/Mixed121/Mixed121Selected.lean)
  is the counterpart of the selected-inputs, local-no-carry and decoding
  links:
  - a band's source cells are the support positions themselves, so its
    selector and copy digits are Boolean;
  - `MF_native` has digit `μ` at both clause targets, so the high-mask
    saturation gives `NoCarry F_t μ`.

  `graph_selected_decode` then applies `Mixed121Decoder.decode` at the clean
  target. Either the band is empty, or exactly one tile is selected and all
  44 copy and anchor digits equal its digits. This is the recipe's §2 clause
  decoding, as a theorem about every `LeafFacts` valuation at the 121x8801
  ports.

## Remaining phases

Measured against the Compact44 calibration, which is 472 modules plus the
endpoint layer:

1. the clean-carry step: a `CarryInput` for the flattened family and a
   carry-free column at each clause target. This is Compact44's
   `Facts/FixedGraphCleanCarry`. Like the whole `Facts/` halting chain
   (45 modules, about 3,000 lines), it takes
   `CompactLeafFacts.LeafFacts p v` at the ports `p`, not a particular
   graph's zero. It is therefore a tuple-level port. `LeafFacts` is stated for
   arbitrary ports, and its `R` and `Nt` have exactly the shape of package 55's
   52 / 79 form. The per-form obligation is to prove `LeafFacts` at a positive
   valuation, as `P57Facts` did on Compact44. The width-generic `carry_input`
   and the room above are inputs to this step;
2. the padding cells `8792..8799` (the mask populations and low bits of §3
   are done, in `Mixed121Masks`);
3. the spatial and temporal overlap identities, and the binary-alignment
   argument for `b = 121`;
4. the packing, rank and controller layers. Compact44's `PackingInput d` is
   already parametric in `d`;
5. halt data, leaf facts and the equation endpoints for 52 / 79 and 44 / 111.
