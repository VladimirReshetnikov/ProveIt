# Incoming source review for the HA goal, 2026-10-26

**Result: PASS for the source and mathematical review described below.** No
blocking semantic finding. This is not a fresh Lean replay, merge receipt, full
dependency-closure check, or proof of HA provability.

The reviewed incoming commit is
`5a1db2b1f543c6af05de4cb54b148651d7b2914c`. Its merge base with the local branch is
`09eaa57ae5b80130ddb0aa5344f71e638ebb3e97`. The local commit sampled for this review
was `c823f106d2238359723f9cef740759ecc249d33f`. Each of the five affected local Lean
sources is byte-identical to its merge-base version; local additions such as
the corrected thirteen-variable, scaled-auxiliary, and object-equation packets
are separate from the incoming five-file delta and must be preserved by the
eventual merge.

I am `controller_certificate`. I authored the original literal
`CurrentKernel2011` dependency and several downstream construction/controller
modules, and previously reviewed the physical-order, modular-residue and
prime-power packets. I did not author these five incoming changes. This review
distinguishes that prerequisite involvement from independent inspection of the
new changes. The upstream receipt attributes the common-modulus port to
`v_finite_full_static`, the two power ports to `intake_e13`, and the integer
square and finite-order ports to upstream ROOT.

## Sources and preservation

I read the complete active diff, all 815 lines of the five final modules, all
135 added lines of the upstream review continuation, and the complete adoption
document delta. I also read the relevant actual library contracts for finite
order-hom rigidity, characteristic casts, guarded natural powers and modular
cast homomorphisms, and the unchanged auxiliary-order derivation used by the
new level-zero endpoint proofs. No incoming Lean, script, archive member or
proposal executable was run. No Git state, accepted source, build object or
other document was changed by this review.

Paths in this table are relative to `Lean/DiophantineConsistency/`.

| Source | Old/new lines | Incoming SHA-256 |
| --- | ---: | --- |
| `ArithmeticNonzero.lean` | 68 / 65 | `38aff54429a2df3bf722d6225ac18f0c15d84b8112000af1f9ab35d25c0100a2` |
| `CurrentKernelResidues2011.lean` | 843 / 426 | `f16f792f4449e423bfa6165f81a6b6e3d8c872531b4e428aaf0bebafd178a659` |
| `CurrentPowerCoordinates2011.lean` | 105 / 96 | `0682e3263153369d5694b3dcf0942e0b4a5cdd2b48b2c25199e4989cbe3896c3` |
| `PrimePowerOrder.lean` | 80 / 73 | `72c0c999cc47c961b2801e74ebe2328c840477b67805f9a9c72f152e9e389917` |
| `WangTiles942PhysicalOrder.lean` | 180 / 155 | `e4c47779d350f7ec34ed3cd15a17a584e23077a2a56a8c8a0c2a53f8376ddddf` |

A separate text comparison confirms that all 56 old public theorem headers and
13 definition headers are literal matches. Twelve complete definition blocks
are byte-identical. The remaining definition is `Rep.nonzero`: only its
correctness proof changes; its single witness and expression tree remain
literal. The sole new public theorem is `K_cast_common`. No `axiom`, `sorry`,
`native_decide` or `unsafe` declaration is introduced. Existing proof budgets
and opaque-base protection remain. The only added import is
`Mathlib.Data.Finset.Sort`.

The complete kernel reindexing/raw-word prefix through the chunk-length
certificates and the complete suffix beginning with `mod_of_cast` are
byte-identical. These important prerequisites also match the base, incoming
commit and sampled local commit exactly:

| Prerequisite | SHA-256 |
| --- | --- |
| `WangTiles942PhysicalData.lean` | `38a11d1ef8d3391074d4cd347e0f764417c6502afd9a6a064d54266456396f5b` |
| `WangTiles942Permutation.lean` | `3351336105f22baf653dcefb3bd83273924dd539353eebf5f1232da855045cef` |
| `CurrentKernel2011.lean` | `6f8642d8d3715335dcf61fb0060818226f227db24e126d4c14d58831e76d3a55` |
| `CurrentControllerData2011.lean` | `a86aa5cc6b523bd659df8681012a1a39307ea340c27a7785629d30699ca151ae` |
| `CurrentAuxiliaryOrder2011.lean` | `67db5e89285d56908ce482ffd72108c909ccc5e4f505ac2d324157344048e08e` |

## Mathematical checks

1. **Signed-square disequality.** For an arbitrary integer `z`, `z ≠ 0`
   implies `0 < z*z`, hence `1 ≤ z*z` by integer discreteness. Thus `z*z−1`
   has a natural witness. Conversely, the natural slack and the displayed
   equality force `0 < z*z`. The new proof retains negative integers, both
   values `±1` and zero slack, and correctly excludes zero. It does not assume
   a nonnegative input expression or introduce a branch-classification premise.

2. **Finite-order rigidity.** A strictly monotone endomap of `Fin n` is an
   injective order homomorphism. The imported theorem
   `OrderHom.eq_id_of_injective` applies to every finite linear order and
   identifies that homomorphism with the identity. Applying the resulting
   equality at `i` proves the unchanged theorem. There is no nonemptiness
   assumption: `n=0` is vacuous and `n=1` remains covered. All subsequent
   descending-weight, coverage, position and selector-reindexing proofs retain
   their original statements and data.

3. **Guarded prime-power cast.** `one_le_pow₀ hg` supplies exactly the bound
   required by `Nat.cast_sub`. Characteristic cast-zero then turns
   `m ∣ g^k−1` into the cast equality, and `sub_eq_zero` completes the iff.
   The guard `1 ≤ g` remains explicit. Modulus zero, modulus one and exponent
   zero are still admitted. No field, primality, nonzero-modulus or unit premise
   has been inserted. The LTE and exact-order proofs are unchanged.

4. **Power-coordinate endpoints.** The CRT equivalence still preserves order
   and the product order is the same least common multiple. The auxiliary
   endpoint now specializes the already proved `generator_order_succ 0`;
   that theorem follows from the independent literal lift and generic
   prime-power theorem and does not depend on `CurrentPowerCoordinates2011`.
   The full base endpoint similarly specializes the earlier `full_order 0`.
   There is no circular proof dependency. Explicit rewriting of
   `(d*auxiliary)*auxiliary^k = d*auxiliary^(k+1)` transports the dependent
   `ZMod` goal correctly. Both coordinate-existence statements and their
   unrestricted natural exponent domains are unchanged.

5. **Common kernel modulus.** The new modulus is exactly
   `47*2011*120199 = 11360848883`. Projection from this modulus to each old
   factor uses `ZMod.castHom` with the proved divisibility in the correct
   direction. The helper requires divisibility only; no converse CRT claim or
   unproved primality/unit hypothesis is used. The 941 non-Start weights, the
   doubled protected Start contribution, all 34 actual controls and the three
   bare kernel terms are still included through the unchanged generic
   `rawWord_cast` identity. `K_cast_common` proves a residue of the original
   kernel; it does not define a replacement kernel constant.

As an additional independent arithmetic check, I ran newly written read-only
Python which parsed the literal decimal pairs from the unchanged physical data
as data, without importing or executing project code. It checked all 59 chunks
(58 of length 16 and one of length 13), all 177 projections onto the old
chunk residues, the concatenated 941-row Horner value, the separate 34-control
sum, and the whole kernel by both concatenated and direct physical-position
evaluation. Results:

| Quantity modulo 11360848883 | Value |
| --- | ---: |
| `2^47` | 10653241607 |
| 941-row evaluation | 10463387658 |
| 34-control reflection | 4297442889 |
| Original full kernel `K` | 1491904576 |

Projection yields `K = (26,1995,114787)` modulo `(47,2011,120199)` and
`1+B*K+B² = (29,674,36379)` at those same moduli. This independent arithmetic
check supplements source inspection; it is not a substitute for Lean checking
the incoming proof terms.

## Upstream evidence and pending integration

The complete added upstream receipt distinguishes the failed uncompiled
coordinate candidate from its repaired final source, records absent-cache
queries separately from elaboration, and reports 24 successful final calls
with the shared residue client counted once. It reports unchanged axiom
outputs for 61 old audited declarations and the standard three axioms for the
new common-residue theorem. It separately records eight post-merge checker
refresh calls. I inspected those claims and their source bindings; I did not
reproduce those compiler runs, their timings, their `rfl` record audit, or all
their logs. No additional axiom-print or full-closure validation is attributed
to this receipt. Root's planned post-terminal affected-source refresh remains
necessary for the local checked environment.

Incoming documentary bindings:

- `research/lean-proof-simplification/ADOPTION.md`:
  `250c35df6a4968453fb623a1b9b7ee7407de37db395b16fcf6cd3a95dfea9771`.
- `reviews/lean-proof-simplification-20261026-root.md`:
  `b2a3fdf0255268164af1e96fcfafe71517fc1382a9b6947123dff66c89d957dd`.

The incoming diff changes no equation artifact, toolchain or Lake manifest.
The 5362-byte `equation.tex` remains
`a48ac1f5bc498bfdbf300c7050332ecaa28af1fc43f27d86b0879a79bd38714e`;
the 153046-byte `equation.pdf` remains
`417c2fa109cacf99d0e83af35d06cbdc8fed1179054d7245e07f3e51ebfff978`.
This review does not rerender them. These proof simplifications neither alter
the current polynomial nor establish the separately requested internal HA
equivalence.

## Inert archive placement inventory

The other eight incoming paths are newly stored ZIP blobs under
`docs/incoming/`. Only their Git paths, byte lengths and whole-blob hashes were
read. No member was extracted, opened, imported or executed, and no proposal
inside these archives is accepted by this review.

| ZIP basename | Bytes | SHA-256 |
| --- | ---: | --- |
| `Lean_Proof_Simplification_Positions_Rank_Rephase_2026-10-26.zip` | 2619796 | `0012750a52fff7d5545f48aebfdd33cb2befc9a09242498effc697463a7e72de` |
| `ProveIt_Lean_Shape_Windows_Growth_2026-10-26.zip` | 243731 | `5c17f57f08b30b183b056148d6552ded82d4dfa7e8bc189b16aa3b469d417467` |
| `ProveIt_Lean_Simplification_Round6_2026-10-26.zip` | 3025385 | `91afbb5a7deb3885613e97aa097eb5643ad5c1d32ea7aad2ec171ae5257285fc` |
| `ProveIt_Proof_Simplification_Review_2026-10-26.zip` | 806316 | `65b136894ad45087d97a18e34ccdf32baedb9cc93a40089bb284e6b9b5ae2020` |
| `diophantine-lean-proof-deltas-2026-10-26.zip` | 646644 | `063b929255793bf9a17e311fed75e922e5ba88d34ab4e4dbf7483757162cd7f7` |
| `diophantine_consistency_lean_simplification.zip` | 222064 | `2750657009c3a50123948d82b46ef59189ade62a41555272e44457ab503f0a09` |
| `lean-residual-guards-2026-10-26.zip` | 454656 | `74b2c4df610ad2d1b7ab71ee818f3152e793685dc60978908ec0d2490659c2fc` |
| `proveit-lean-rank-zero-test-2026-10-26.zip` | 402309 | `9a9aeb49119ab6fa164de613352d4899bdf067c5751a64f5f61d4f8497e9fc2a` |

The local merge and affected recompilation are deliberately left to ROOT
after its live 361-source check reaches a terminal result.
