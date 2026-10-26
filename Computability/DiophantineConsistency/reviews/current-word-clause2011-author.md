# Constructed word clauses and strict transport: author receipt

Date: 2026-10-26. Author: `controller_certificate`. Status: frozen,
fresh main and focused checks PASS. This is an author self-review,
not an independent review.

## Exact sources

Paths are relative to
`Computability/DiophantineConsistency/Lean/DiophantineConsistency/`.

| Source | Lines | Bytes | SHA-256 |
| --- | ---: | ---: | --- |
| `CurrentWordClause2011.lean` | 180 | 9339 | `df93b7dc684693e23097e5bfdba9aa3a9121595574b6026832d2a4f3f2fd24dc` |
| `CurrentWordClause2011Checks.lean` | 81 | 4089 | `68de30948d89ff90409aa6cf1a5c49c7d5ee81661347c9bcca775a7440041615` |

The main imports root's frozen `CurrentCarryConstruction2011`
(`6efd60cd1ce0f40aa48e68ec7d9c2b2c680bbdc0aa289488c268e79fa68a026a`)
and `circuit_reduction`'s frozen `CurrentReflectedGeometry2011`
(`268ecac628932a93d79593ae0b4e1c8819817db58f27ec9613c4ad23a29d60c1`).
The new proof reuses the existing actual-kernel fixed point; it does
not duplicate that construction. I independently reviewed and replayed
the carry composition immediately before implementing this packet.

I authored the existing word/cell/label/kernel dependencies. Their
relevant source bindings are:

| Dependency | SHA-256 |
| --- | --- |
| `CurrentWordConstruction2011` | `9455d6c2015906a8f76ff2be5275a95cae5340f0ca3e8dc16666ffc6bab2b5b8` |
| `CurrentCellConstruction2011` | `03344f81c7817f625633470218727176f975ee7617154589534a0b94feb9bd0a` |
| `CurrentCellLabels2011` | `88698cd0d678d788c169b22915594b9ce37dd5d5c19c3d0069b190e0575f740d` |
| `CurrentClause2011` (root authored) | `a76daeaa24d3b3b00cfb80e2aaa3c9082740f9f8349a8d18014c912a9001c566` |

I read the complete carry, reflected geometry, literal clause and label
sources, their invoked generic normalization and rotation interfaces,
and the relevant ordinary construction in sections8–9 of
`research/padding-staircase-independent/PROOF.md`. No frozen dependency
was edited.

## Derived arithmetic

Let `c` be the actual assembled word with independent dummy and marker
maps, and `base j` the canonical physical base of cell `j`. The new
`clause_convolution` theorem gives exactly

```text
convolution(actualKernel,c)(base j + 1005)
  = 2^45 + 2 + localDigit(a j,1).
```

This identity retains every reflected coefficient and the bare
selector1 collision. It follows from the existing literal convolution
formula, the constructed count one, the exact selector payload and the
full complemented copied word. It permits arbitrary natural control
values: neither dummy977 nor marker1004 participates in this clause.
There is no bit or sum enumeration over the942 tile table.

`physical_count` transfers the constructed abstract-selector count to
the literal942-field prefix via the proved physical permutation.
For Boolean controls, the existing reflected-geometry bound therefore
proves `low_carry_zero` at every field0..1004 in every cell. This holds
for every normalization satisfying the actual bounded recurrence and
for every binary displacement, including fractional phases; it does
not assume any mask test, matching labels or temporal alignment.

`displacement s` is exactly `47*(2011*s)`. For an unrestricted natural
stride `s`, the actual binary rotation becomes subtraction of `2011*s`
physical fields. The clause source remains at residue1005, outside
the low support, so it is zero. The residue proof handles arbitrary
wraparound and does not truncate a subtraction of natural indices.

The clause predecessor is field1004, whose carry was just proved zero.
The clause's exact raw value is below radix, so its outgoing carry is
also zero. `normalized_clause` then derives the same exact value for
the normalized digit. `clause_mask_pass` proves that digit avoids the
actual `CurrentHighDigits2011.maskDigits` at that position; no global
mask premise is used.

The digit is either `2^45+2` or `2^45+3`, hence both positive and
strictly below `radix-1`. Root's generic positive-digit and single-slack
helpers consequently establish

```text
0 < word(radix,digits) < radix^(N*2011) - 1.
```

`exists_clause_normalization` first obtains carries and digits from
the frozen assembled normalization, then derives the clause family,
the local mask family and the strict positive window for those same
digits. Its `Facts` component retains the actual transport congruence
with `(K+2^(47*(2011*s)))*word(radix,c)`. It does not supply the desired
transport positivity as a premise.

No marked tiling, matching colors, nonzero stride, unique Start,
source-system zero or controller witness is needed for these local
results. In particular `s=0` and `N=1` are valid. The module does not
prove whole-mask correctness, copy/marker/padding tests, the stronger
bound `F<q/radix`, the source scalar boxes, or a positive polynomial
solution. Those remain separate construction steps.

## Fresh checks and development history

I read all newly authored source before execution, inspected each
correction, and reread the complete final main and unchanged checks.
Builds were sequential under pinned Lean4.32.0 with `Elab.async false`:

```sh
lake env lean -M6000 -j1 \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentWordClause2011.lean \
  -o .lake/build/lib/lean/DiophantineConsistency/CurrentWordClause2011.olean
lake env lean -M6000 -j1 \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentWordClause2011Checks.lean \
  -o .lake/build/lib/lean/DiophantineConsistency/CurrentWordClause2011Checks.olean
```

Final main: PASS,4.27seconds, peak3282272KiB, no Lean diagnostics.
Checks: PASS on their first run,3.41seconds, peak3263252KiB. All eleven
intended axiom reports use only `propext`, `Classical.choice`, and/or
`Quot.sound`. No `sorry`, `admit`, `native_decide`, or added axiom occurs.

The focused checks include deliberately non-Boolean numeric control
maps in the raw identity, an actual selected physical1 bit equal to one,
seventeen-period shifted absence at `N=1`, low resets at binary phase46,
the zero-stride/single-cell construction, and the complete existential
strict transport endpoint with its actual product and local masks.

The first main attempt omitted the explicit carry-function argument
when applying the existing reset theorem. After correcting that
elaboration error, the next attempt exposed a redundant `omega` after
a rewriting tactic had already closed the goal. Removing that tactic
gave the final clean build. An unused section-variable warning was
also removed by explicitly omitting that variable from the generic
rotation adapter. No mathematical premise was strengthened or result
weakened in these corrections.

| Output | SHA-256 |
| --- | --- |
| Main `.olean` | `943922811f2ef84209aca68d8f117dd72119c67327cd63ae5bbbc615b10a6c59` |
| Checks `.olean` | `ff52458e78a7b76bcd02836a4f28ae285d6fb205079b7d00a7b8138953d8859b` |
| `/tmp/current-word-clause2011-main-stage1.log` | `aa7dbfe969ac7c3b5d0439a37945ddd74082cc050825e9d5f96889eb79182d7a` |
| `/tmp/current-word-clause2011-main-stage2.log` | `ad1acbf702c728f22500ba92ab53d1ea9c886da1edacb3094298ccb5b7cfa87a` |
| `/tmp/current-word-clause2011-main-stage3.log` | `2d10a17d5d94be8bbb66c2df3aa2c0fa6e25e779f0feda299d2e00a74eed925d` |
| `/tmp/current-word-clause2011-checks-stage1.log` | `53dd332a671b2488f2b0b11f5339647635125b739c5c02493dd31751f06ab244` |

Only the assigned new module, checks and this author receipt were
added. No frozen source or shared documentation was edited, and no
git operation was run.
