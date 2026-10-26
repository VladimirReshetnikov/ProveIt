# Constructed local coefficient cells and exact rank variation

Date: 2026-10-26. ROOT independently read all four complete frozen sources
and both author receipts before four fresh capped Lean runs. Both mains
and checks passed, with empty main logs and standard-only axiom reports.
Fresh main outputs were separate temporary objects; checks imported the
frozen author objects. Existing prerequisites were reused, without a
fresh whole-closure build claim.

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| CurrentCellConstruction2011.lean (256 lines) | 03344f81c7817f625633470218727176f975ee7617154589534a0b94feb9bd0a |
| CurrentCellConstruction2011Checks.lean (107 lines) | 847c5e2b22d2c985419087a057c91d7db3238992e0ddc7c180af49e9bc154c7a |
| NativeRankVariation.lean (112 lines) | 46c226eba0018eb15eaec66bb31b2ea8af7682fbef76d0245ee45c6aa236ef73 |
| NativeRankVariationChecks.lean (77 lines) | a5d44d4819a48e3900e19ee2ad684015b4806dd5a661081203ac4c6dd95d6b0a |

The local cell places its single selector at the actual physical
permutation position. Its complemented South/North/East/West bits use
942/960/969/978, respectively, with widths 9/9/8/8. Binary reconstruction
is proved generically for every finite prefix. Actual color bounds then
give the exact copied word `2^34−1−packedTile(tile i)`, while the selector
payload is `1+packedTile(tile i)`. Their sum is exactly `2^34`.

Consequently the occupied clause is exactly `2^45+2+selector1`, including
the genuine bare-selector contribution. It passes the existing clause
mask and is below radix `2^47`. Boolean support, literal Start origin
and all four Start label values are proved from the same cell. The
copied-word and selection adapters bind to existing cyclic definitions;
their explicit data equality exempts dummy977 and marker1004. These
control slots remain free for the later global construction.

Checks distinguish Start's East and West low bits, exercise South bits,
empty/truncated prefixes, actual physical selection, the complete clause
mask, N=1 cyclic binding, and arbitrary dummy/marker overrides preserving
copied labels. This is a local construction; it does not assert that
global incoming carries or all high-mask tests have been discharged.

The rank module first identifies the actual Carrier65 rank with
`(q*(q−F)−C)*(q^2−1)+(MC+q*MF)*J`. MF is the existing source high-mask
port; its beta shift is not added again. Over any commutative ring,
ordinary increments C→C+delta and F→F+A*delta change rank by exactly
`−delta*(q^2−1)*(1+q*A)`. Positional increments factor this as
`−rankGamma*B^j`. Actual-core adapters retain all ports and explicit
q/J/C/F equalities.

For integers, q>1, A≥0 and a positive increment give positive Gamma and
strict rank decrease, even if the ranks or mask arguments are negative.
The q=1 control gives zero change; negative A can reverse the sign.
A concrete check shows why congruent F values cannot replace the stated
ordinary increment equality. No safe mutation, mask preservation or
polynomial-zero preservation is inferred from this algebra alone.

All root commands used `lake env lean -M6000 -j1`. The 15 cell and 10
rank axiom audits contain only subsets of `propext`, `Classical.choice`,
and `Quot.sound`. The cell check log SHA-256 is
`9e60c25195252bd31da85f719fa507d642ea3257b8c1bec047bf70a6231b8849`.
The rank check log SHA-256 is
`208166be42aaea2cc32eadae211093656b803995b55a098a0841a2b98e97eec1`.
See author receipts for [local cells](current-cell-construction2011-author.md)
and [rank variation](native-rank-variation-author.md).
The [independent local-cell review](current-cell-construction2011-lean-peer.md)
also passed isolated fresh main/check replay with 15 standard-only reports
and byte-identical objects. It checked the true field orientation, full
clause mask, physical permutation and free control-slot interfaces.

The global Boolean word, shifted marker, cyclic carry/mask proof,
composite rank controller and positive arithmetic witnesses remain open.
The decimal equation page and size metrics are unchanged.
