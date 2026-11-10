# The wang943-mixed-121x8801 tuple: a Lean calibration

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

## Phase 3f: from one decoded block to a halting run

The rest of Compact44's `Facts/` halting chain, ported link by link. Every
link takes `CompactLeafFacts.LeafFacts Mixed121Ports.ports v` at a positive
valuation `v`. The 121-specific geometry is re-derived and checked by
`omega`/`decide`:

- the second anchor is `1096`;
- the bare offsets are `2200` and `8843 = 8801 + 42`;
- the field windows are ten cells wide;
- the copy indices are `9 → 29` for the successor, `42 → 40` for the orbit,
  and `30 + u ↔ 10 + u` and `20 + u ↔ u` for the field matches.

| Module | Link |
| --- | --- |
| [`Mixed121Occupied`](../../Lean/DiophantineConsistency/Mixed121/Mixed121Occupied.lean) | block `0` selects the Start tile, and all 44 copy cells carry its digits |
| [`Mixed121Parity`](../../Lean/DiophantineConsistency/Mixed121/Mixed121Parity.lean), [`Mixed121AnchorParity`](../../Lean/DiophantineConsistency/Mixed121/Mixed121AnchorParity.lean) | the anchor cells `2195`/`3296` are read through the bare offsets `1100`/`2200` |
| [`Mixed121Shift`](../../Lean/DiophantineConsistency/Mixed121/Mixed121Shift.lean) | the temporal shift is block-aligned: `(E/121) % (8801N) = 8801·s` |
| [`Mixed121Uniform`](../../Lean/DiophantineConsistency/Mixed121/Mixed121Uniform.lean) | every block's band decodes, uniformly in the block |
| [`Mixed121Field`](../../Lean/DiophantineConsistency/Mixed121/Mixed121Field.lean) | vertical (`30`/`D`) and horizontal (`62`/`8843`) field transport |
| [`Mixed121Copy`](../../Lean/DiophantineConsistency/Mixed121/Mixed121Copy.lean), [`Mixed121Orbit`](../../Lean/DiophantineConsistency/Mixed121/Mixed121Orbit.lean) | copy cells are block-local; selection propagates along the temporal orbit |
| [`Mixed121Successor`](../../Lean/DiophantineConsistency/Mixed121/Mixed121Successor.lean) | selection propagates to the spatial successor through the marker bit `9` |
| [`Mixed121AllBlocks`](../../Lean/DiophantineConsistency/Mixed121/Mixed121AllBlocks.lean) | every block is selected (`𝚺₁` induction in the model of `𝗜𝚺₁`) |
| [`Mixed121BlockWord`](../../Lean/DiophantineConsistency/Mixed121/Mixed121BlockWord.lean) | the selected tiles form a `𝚺₁` row word, packed into 10-bit blocks; no row is the impossible tile `1` |
| [`Mixed121FieldMatch`](../../Lean/DiophantineConsistency/Mixed121/Mixed121FieldMatch.lean), [`Mixed121TileMatch`](../../Lean/DiophantineConsistency/Mixed121/Mixed121TileMatch.lean) | neighbouring tiles agree on shared fields, and so match as Wang tiles |
| [`Mixed121Halt`](../../Lean/DiophantineConsistency/Mixed121/Mixed121Halt.lean) | row `0` is tile `0`; the word is a `CompactLocalWord.Word`; machine 215 halts |

The final theorem is

```lean
Mixed121Halt.halts_of_facts (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Mixed121Ports.ports v) :
    ∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0
```

over every model `V` of `𝗜𝚺₁`. Its axioms are only `propext`,
`Classical.choice` and `Quot.sound`. It is the exact counterpart of
`CompactLeafFactsHalt.halts_of_facts`. The tail after the local word
(`OldWordIdentificationDraft.local_to_marked`,
`ArithmeticWangSoundness.marked_halts`) is generic in the word, so it is
reused unchanged; both tuples encode the same 943 tiles in the same order.

The tuple-level calibration is therefore complete in the soundness
direction: a positive solution of any equation whose leaf facts hold at these
ports gives internal halting of machine 215. The whole `Mixed121/` tree is
54 modules, about 6,700 lines, including the 22 width ports under `W121/`.

## Phase 4: package 55's 52 / 79 form reaches halting

The 14-positive, 79-operation, degree-52 equation of
`con-zfc-diophantine-forms/55-congruence-norms/fourteen/polynomial.json`
is the first form placed on this tuple. Its four ports are package 31's
payloads (the same SHA-256s), and so they are `Mixed121Ports.ports`. Four
modules give its forward direction:

| Module | Content |
| --- | --- |
| [`P55Graph`](../../Lean/DiophantineConsistency/Mixed121/P55Graph.lean) | the 79-gate let-chain, checked against the pinned JSON by [`tools/generate_p55.py`](tools/generate_p55.py) `--check`; the four-squares form of a zero; ring evaluation of `M`, `W`, `Na`, `N0`, `Nt` |
| [`P55Root`](../../Lean/DiophantineConsistency/Mixed121/P55Root.lean) | each residual read in the model: transport and main root as for package 62 (`U = 4q⁴`, `Y = sq³`), strong and auxiliary norms as for package 64, and `N0 = 1` as the first Pell norm |
| [`P55Norm`](../../Lean/DiophantineConsistency/Mixed121/P55Norm.lean) | the local minimum block (`W² + Na² = 1` iff `W = 0`, `Na = 1`) and the unit split `N0·Nt = 1 ⟹ N0 = Nt = 1`; `N0 = −1` is the excluded consecutive-product negative Pell equation for `n = XY²` |
| [`P55Facts`](../../Lean/DiophantineConsistency/Mixed121/P55Facts.lean) | `facts_ports` at any ports with the four `leaf_bounds`, then `halts` at the 121x8801 ports via `Mixed121Halt.halts_of_facts` |

Only `P55Facts.halts` names the 121x8801 ports; the rest is port-generic.

## Phase 5: the converse, and the 52 / 79 iPRA endpoint

The halt-to-witness layer of Compact44 (see [`CONVERSE_PORT.md`](CONVERSE_PORT.md))
is ported to 121x8801. The λ = 2341 controller and the kernel residue come
first (`Mixed121ControllerData`, `…ControllerChoice`, `…ConstructionUnit`,
`…KernelResidue`, `…Calibration`). Then the cell and word layers
(`Mixed121Cell`, `Mixed121Word`, `Mixed121Block`, `Mixed121Column`), the
phases of the high mask (`Mixed121FieldParity`, `Mixed121Target`,
`Mixed121High`, `Mixed121Origin`), the calibrated packing (`Mixed121Rank`)
and the canonical halt data (`Mixed121Seeds.halt_first_gamma`). Differences of
substance from Compact44:

* `Γ` has order `5070` modulo `C0 = 11²·13·677·2341`, not `λ − 1`;
* all ten bits of each field window are uniform, so Compact44's marker-phase
  modules have no counterpart;
* the clause-target digit depends on the tile: it is `2·clause(i) − 1`, carry-free
  against `μ` because its bits are at `0` and `11 + 2k` (checked over the 943
  rows by `decide +kernel`);
* every packing field is discharged at once (`halt_chosen_rank_no_high`),
  where Compact44 used four stages with residual hypotheses.

`P55ConvZero` and `P55Converse` build package 55's fourteen witnesses from the
halt data, a hybrid of packages 62 and 64. [`IPRAPositive55`](../../Lean/DiophantineConsistency/Mixed121/IPRAPositive55.lean)
then proves, in native, standard and equality-only iPRA, that the 52 / 79
equation has no positive zero iff `¬Halts(M215)`, i.e. iff the mapped ZFC
refutation is absent. Axioms: `propext`, `Classical.choice`, `Quot.sound`.

Package 59's 14-positive 52 / 79 (`59-degree-separated/short/circuits/p79_d52_14positive.json`)
is a different polynomial at the same four ports: its output is
`M² + (Na − 1)² + (N0·Nt − 1)² + W²` instead of `M² + W² + Na² + (N0·Nt − 1)² − 1`,
and its auxiliary norm is written `ŷ² − Aaux·u·(V + ŷ)`. `P59Graph` proves, over any
commutative ring, that every residual evaluates as package 55's, and
[`IPRAPositive59`](../../Lean/DiophantineConsistency/Mixed121/IPRAPositive59.lean)
transfers package 55's bridge (a 59-zero has four vanishing squares; a positive 55-zero
has `M = W = 0` and `Na = N0 = Nt = 1` by `P55Norm.residuals`). It gives the same three
iPRA endpoints. [`tools/generate_p59.py`](tools/generate_p59.py) checks the 79 gates
against the pinned JSON, the package's exact-degree audit and the port hashes.

**Fifteen-positive forms on this tuple (2026-11-07).** Package 59's 91 / 69
(`p69_d91`), 101 / 68 (`p68_d101`) and 125 / 67 (`p67_d125`), package 56's
54 / 73 (Q54) and 46 / 74 (Q46), and package 47's 44 / 75 (`gap_minima75`) all bind
package 55's four ports. They are unit products or grouped sums of squares of the
residuals `N0, N1, Na, Nk, Nt, Ns` with an explicit multiplier `Nk = k − hE − R`.
`Short15Graph` … `Short15Facts` take a positive zero straight to `LeafFacts` and
`Mixed121Halt.halts_of_facts`; the new step is `Short15Index.minus_false`, which
rules out `Nk = Nt = −1` (`Nt = −1` gives `C ≥ 0` because `0 < K0`, then the Pell
doubling bound contradicts `c = kY + η`). `Short15ConvData` / `Short15ConvZero`
read the canonical halt data with `h = 4Ys'` and `γ = γold`. The endpoints are
`IPRAPositive59p69`, `IPRAPositive59p68`, `IPRAPositive59p67`, `IPRAPositive56q54`,
`IPRAPositive56q46` and `IPRAPositive47p75`, each with native, standard and
equality-only equivalences. [`tools/generate_short15.py`](tools/generate_short15.py)
`--check` binds each literal graph to its pinned JSON and checks that each package's
port hashes equal package 55's.

**Package 54's gate lists at these ports (2026-11-08).** Package 54's three
fifteen-positive frontier circuits, 80 / 70 (`p70_degree80`), 78 / 71
(`p71_degree78`) and 72 / 64 (`p72_degree64`), are bound in the package to its own
tuple `complemented-factorized-receiver-89x4831` (base `2^429959`), which the tree
does **not** calibrate. As for package 59's copy of 101 / 68, the Lean endpoints
take **54's gate lists, instantiated at package 55's 121x8801 ports**
(`Mixed121Ports.ports`); degree and operation count do not depend on the tuple.
54's literal c54-port equations remain uncalibrated. The output is
`A² + B(B − 2) + C²` with `A = N0·N1`, `B = Na·Nk·Nt` and `C = S`, over the same six
residuals as above. `Short15P54Split` shows that a zero has `A = ±1`, `B = 1`, `C = 0`
(`N0`, `N1` are never zero), hence `N0 = N1 = Na = 1`, `S = 0`, `Nk = Nt = ±1`, and the
`Short15` chain finishes as for the six-factor products. The converse uses
`Short15ConvData.canonical` unchanged. Package 54's own completeness argument
relies on a c54 fact, the low-mask phase `R ≡ 3 (mod 4)`; at 121x8801 that role is
played by the canonical halt data already proved here. The graphs are
`P54p70Graph`, `P54p71Graph` and `P54p72Graph`, and the endpoints are
`IPRAPositive54p70`, `IPRAPositive54p71` and `IPRAPositive54p72`, each with native,
standard and equality-only equivalences.
[`tools/generate_short15_p54.py`](tools/generate_short15_p54.py) `--check` binds each
Lean block to the gates of its pinned JSON. It also checks that 54's four port hashes
are disjoint from package 55's, so the endpoints are not 54's literal equations.
`--mutations` confirms that seven kinds of corrupted gate lists are rejected.

## Remaining phases

1. **Per-form leaf facts for 44 / 111.** Package 132's fifteen-integer form
   needs its own `LeafFacts` proof, as phase 4 did for 52 / 79.
2. **Completeness — done for 52 / 79 (phase 5).** Halting of machine 215 gives a solution. This is the
   recipe's witness construction: packing, rank, and the `λ = 2341`
   controller of §4. [`CONVERSE_PORT.md`](CONVERSE_PORT.md) maps Compact44's
   147-module halt-to-witness layer: 80 modules to hand-port (about 5,700
   lines), 17 width-only modules, 9 that only need import retargeting, and 41
   reusable unchanged. Compact44's controller is already the
   arbitrary-odd-factor construction, so its port changes the constants
   (`p = 581197 → λ = 2341`, `C0 = 342946332593 → 2492980061`), not the
   argument.
3. **Endpoints.** 52 / 79 is done for package 55 (`IPRAPositive55`) and package 59 (`IPRAPositive59`). 44 / 111 turned out to
   be on a different tuple, source34 ("mixed-parity-unrounded-1064921": same
   β, `b`, `L` and `λ = 2341` controller, but kernel `D_C = ρ^40 + ρ^41 + … `,
   `D_R = ρ`, parity-separated high mask), so it needs its own calibration.
