# Current 2011 controller data: author receipt

This receipt covers the new Lean finite-data module and focused checks. I authored both files and read their complete final source. This is an author audit, not an independent peer review. No frozen source, umbrella file, main document, or Git state was edited.

## Frozen sources and inputs

| File | Lines | SHA-256 |
| --- | ---: | --- |
| `Lean/DiophantineConsistency/CurrentControllerData2011.lean` | 184 | `a86aa5cc6b523bd659df8681012a1a39307ea340c27a7785629d30699ca151ae` |
| `Lean/DiophantineConsistency/CurrentControllerData2011Checks.lean` | 76 | `94c31dd43489bb37d8aae28af221f7e7e9e95c7c6f32b3b98a5ec00c28cdb43a` |
| `Lean/DiophantineConsistency/CurrentKernel2011.lean` | 537 | `6f8642d8d3715335dcf61fb0060818226f227db24e126d4c14d58831e76d3a55` |
| `Lean/DiophantineConsistency/CurrentMasks2011.lean` | 196 | `72ec99ac052c4d244f22f2590fb5645cebbe9ffe3a18fd89fe1cb8db7248fe06` |
| `research/padding-staircase-independent/PROOF.md` | 990 | `69ce844ef80894251f4bd9510d9f60468585b4a004f4a624d3b347ce3e144fb8` |

I read the entire ordinary controller section 11 before implementation and compared its numerical parameters with the literal current mask/kernel definitions. The main module imports `CurrentKernel2011`, `Mathlib.Data.Nat.Squarefree`, `Mathlib.GroupTheory.OrderOfElement`, `Mathlib.Tactic.NormNum.Prime`, and `Mathlib.Tactic.ReduceModChar`. The checks import only the new main module.

## Proven scope

The definitions bind `d` to the actual mask width and `B` to the actual radix to the power 2011, proving `d = 47*2011 = 94517` and `B = 2^94517`. Lean proves primality of 47, 2011 and the auxiliary 120199, squarefreeness and oddness of `d`, the exact factorization and least-common-multiple spacing 9246, its coprimality with `d`, and `120199 = 13*9246+1 > d`.

The exact orders of 2 modulo 47 and 2011 are 23 and 402. The latter uses all proper prime-divisor tests at exponents 201, 134 and 6, giving residues 2010, 205 and 64. Coprimality with `d` proves the same exact orders for `B`. The base residues at 47, 2011 and 120199 are 37, 1283 and 37435; their square residues are 6, 1091 and 99283.

The full auxiliary lift is proved as a natural remainder:

```
B^(120199-1) % 120199^2 = 7300767062
7300767062 = 1 + 120199*60739
0 < 60739 < 120199
```

The proof reduces the exponent `94517*120198 = 11360754366` in `ZMod 14447799601` by proof-producing repeated squaring, then transports equality of casts to the natural remainder. It does not construct the unreduced natural power. The lift is nontrivial, and `B^2 % 120199 != 1` is also proved.

**The literal kernel residues are not proved in this packet.** The three `Hs_mod_*` theorems visibly assume, respectively, `CurrentKernel2011.K % 47 = 26`, `% 2011 = 1995`, and `% 120199 = 114787`. They conclude the corresponding remainders of the actual expression `1+B*K+B^2`, namely 29, 674 and 36379. These are conditional arithmetic wrappers, not a complete discharge of Pcst. The auxiliary prime is proof data, not an added equation coefficient. The later LTE/orbit/cardinality argument, controller witness, native packing converse, and equation equivalence are outside this module.

## Verification

After reading all final source, I ran sequentially from the repository root:

```
lake env lean -M 6000 -j 1 -o .lake/build/lib/lean/DiophantineConsistency/CurrentControllerData2011.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentControllerData2011.lean
lake env lean -M 6000 -j 1 -o .lake/build/lib/lean/DiophantineConsistency/CurrentControllerData2011Checks.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentControllerData2011Checks.lean
```

Both final commands exited 0. `Elab.async` is false. The final main log `/tmp/current-controller-data2011-main-final.log` is empty (SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`). The checks log `/tmp/current-controller-data2011-checks-final.log` has SHA-256 `9c8cca3bb9c6b55998a4e4a85108ce6991646f8db3f4a5c858c1b21bb36bbc55` and contains 21 axiom reports, all confined to `propext`, `Classical.choice`, and `Quot.sound` or no axioms. No `sorry`, `admit`, `native_decide`, new axiom, incoming program, or external certificate is used as a Lean proof.

Final object hashes are `d3e59650f41406c44c43bd0d702a16b9256f21c1242c6faeb4bbf0439951a7b8` (main) and `2ff1ef64160c12b118478622b09ed17e6c5b33875dc987a5e8c8dd855f5302cc` (checks).

Development did encounter elaboration failures and excessive closed reduction; they are not recorded as successful checks. The initial long run was deliberately terminated at roughly 5.87 GB. Short prefix replays located missing numeral-cast normalization, redundant tactics after a closed goal, and an incorrect repeated `Nat.add_mod` rewrite. The named auxiliary modulus had to be unfolded for the modular-power tactic. A later full run explicitly reported kernel excessive-memory errors when converting through a closed `Hs` alias: that conversion expanded the literal sorting kernel. The final endpoints print the polynomial expression directly, use a generic modular-algebra lemma, and keep `B` and `K` locally irreducible during elaboration. This changes no mathematical statement or constant. The final complete main and checks were replayed after those fixes; their logs are clean apart from the requested axiom reports.
