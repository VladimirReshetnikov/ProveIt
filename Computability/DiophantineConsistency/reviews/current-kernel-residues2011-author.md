# Author receipt: exact current kernel residues

The new `CurrentKernelResidues2011.lean` and focused Checks are frozen after complete source self-review and successful fresh capped compilation. This is an author receipt, not an independent peer review. No previously frozen source, equation, coefficient, umbrella file, or shared documentation was edited.

## Exact theorem scope

`K_mod_47`, `K_mod_2011`, and `K_mod_auxiliary` prove, with no residue hypotheses, that the original `CurrentKernel2011.K` has residues **26, 1995, 114787** modulo **47, 2011, 120199**, respectively. The corresponding `K_cast_*` theorems state the same results in the actual `ZMod` rings. The new unconditional `Hs_mod_*` theorems discharge the previous finite kernel premises and give residues **29, 674, 36379** for the actual expression `1 + B*K + B^2` at those moduli.

The exact generic `rawWord_cast` theorem binds the original finite stencil to its reindexed evaluation in every commutative semiring. The selector sum uses the already kernel-proved complete physical permutation. Protected Start is kept separately at position zero. The remaining941 selectors occupy positions1 through941, so their high-to-low evaluation is multiplied by `r^64`; the largest non-Start power is1004. All34 actual packed controls are retained in west/north/east/south order: positions978/960/969/942 with coefficient shifts10/18/27/35. All reflected coefficients are doubled, and the three bare powers18,1004,2020 occur exactly once.

`evaluate_sum` and `evaluate_append` are generic proofs. Each of59 physical-data chunks, of size16 except the final13, is then kernel-evaluated independently at each modulus. The three whole list evaluations are assembled through the generic append identity. The evaluated radix residues are2,1283,4237; the941-entry Horner residues are15,1822,64708; the control residues are4,241,88241. No full physical floor computation is performed in this module.

A newly authored standard-library Python snippet read the already frozen Lean chunk literals as inert data and generated candidate modular numerals. Every resulting block equation is proved with `decide +kernel`; all radix and final power equations use proof-producing `reduce_mod_char`. A separate direct check against the frozen ordinary coefficient JSON agreed, but neither that JSON nor Python execution is a Lean proof premise. No incoming program was executed.

This packet completes these literal finite residue premises. It does not establish a power orbit, LTE/CRT construction, safe dummy realization, a positive equation witness, the equation converse, or an internal ZFC equivalence.

## Verification and development chronology

Read the complete generic proof, all177 block statements and evaluations, the three append compositions, the exact whole-kernel binding, final residue interfaces, and the entire focused Checks before their executions. Final commands, sequentially from the repository root, were:

```text
lake env lean -M 6000 -j 1 -o .lake/build/lib/lean/DiophantineConsistency/CurrentKernelResidues2011.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentKernelResidues2011.lean
lake env lean -M 6000 -j 1 -o .lake/build/lib/lean/DiophantineConsistency/CurrentKernelResidues2011Checks.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentKernelResidues2011Checks.lean
```

Both final commands exited zero. Main:13.27 seconds, maximum RSS3477788KiB, empty log. Checks:3.50 seconds, maximum RSS3240692KiB. All13 printed axiom reports use only subsets of `propext`, `Classical.choice`, `Quot.sound`; no new axiom, `sorry`, `admit`, or `native_decide` is used.

The focused checks include the exact three original-K statements, empty and composite-modulus Horner endpoints, nonzero H residues, and actual expression corruption controls: omitting Start, moving the bare marker one field, and changing the reflected scale2 to1. The last uses an explicitly checked inverse24 modulo47.

Development failures were elaboration/proof-composition issues, not failed candidate numerals: list-length normalization in the generic finite sum; natural-cast normalization for control powers and radix; and an implicit auxiliary-modulus conversion that expanded the closed enormous K while kernel-checking an H wrapper. The latter hit the6GB cap and terminated normally with an error. It was replaced by a generic explicit `transport_modulus` lemma, retaining the exact original K. No memory cap was raised. The first focused check attempted division without a synthesized field instance; it was replaced by the checked modular inverse. Final source and checks have no warnings. No process was restarted merely because an observation timed out.

## Frozen identities

- `CurrentKernelResidues2011.lean`: 843 lines, 32387 bytes; source SHA-256 `6e6812f7181a4b7fa5c558aef5f369c3068c21870710d522a979c39c877c8f4f`; object SHA-256 `91a5c3514338ebe9f0ddbd3069e3928ff61595c332017ba773232b8c2a33063e`.
- `CurrentKernelResidues2011Checks.lean`: 63 lines, 2401 bytes; source SHA-256 `e91e763e095b1876b3c09b5ab1043ee69d03eed0b714ff180166d14ccbcea0ba`; object SHA-256 `db00c44dcd428b7cad190a5dc309c352c9cec681bdf680c258efa92027e79d56`.

Direct imports are `WangTiles942PhysicalOrder` and `CurrentControllerData2011`; Checks imports the new main module. Frozen direct-source identities:

- `WangTiles942PhysicalOrder.lean`: `eafbd5914bf4219d6ce48b501c8be41c228253ef719b65a02e7d167ada0ce3e9`.
- `CurrentControllerData2011.lean`: `a86aa5cc6b523bd659df8681012a1a39307ea340c27a7785629d30699ca151ae`.

Runtime receipts:

- `/tmp/current-kernel-residues-main-final.log`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- `/tmp/current-kernel-residues-checks-final.log`: `b4db922c7516f7bdf73490ddd3bf5cf44530abc4c9a5e186d877c2ec88c42584`.
- `/tmp/current-kernel-residues-main-final-time.log`: `f0577a971073420f12539e2d183f979c5047a7c53e7283ecdbada824a7acd259`.
- `/tmp/current-kernel-residues-checks-final-time.log`: `7ab1ae67506871c40265bbce5ecbf33ac12b4b570c046d7f2d00981b7b07b236`.
