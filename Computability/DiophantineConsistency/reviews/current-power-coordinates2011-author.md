# Author receipt: actual full-modulus affine power coordinates

The two new main modules and their focused Checks are frozen after complete self-review and fresh successful capped compilation. This receipt records authorship, not independent review. Existing frozen source, unit proofs, equation constants, shared documentation, and Git state were not modified.

## Generic construction

`ControllerPowerCoordinates.exists_power_coordinates` takes only `C0>1`, `NeZero T`, an actual `g : ZMod(C0*T)`, its actual projection1 to `ZMod C0`, and `orderOf g = T`. It constructs an equivalence `e : ZMod T ≃ ZMod T` satisfying

```text
g^(e z).val = 1 + C0*z.val
```

in the full modulus, for every `z`. The proof applies the already proved `ControllerResidueLift.exists_coordinate` to every actual power `g^j.val`. Equal chosen coordinates imply equal powers; the canonical exponents lie below the exact order, so they are equal. This proves injectivity of the coordinate map. Finite surjectivity then supplies its inverse equivalence. Neither a coordinate map, a desired affine formula, nor a target subset is assumed. The singleton case `T=1` is retained.

The complete imported residue-lifting source and the used primary Mathlib canonical-power-injectivity lemma were read before execution. Direct imports are `ControllerResidueLift` and `Mathlib.GroupTheory.OrderOfElement`.

## Literal full-modulus binding

`CurrentPowerCoordinates2011` uses the frozen current finite data and actual auxiliary order. The fixed order23 modulo47 and402 modulo2011 both divide `auxiliary−1` through the checked spacing9246. Thus the actual generator `B^(auxiliary−1)` is1 modulo both fixed primes and hence modulo `d=94517`. It is also1 modulo the auxiliary prime120199 by the previously checked lift.

The generic `order_product` theorem uses the actual `ZMod.chineseRemainder` ring equivalence and the order formula for a product; it is valid for arbitrary coprime natural moduli. The complete primary CRT definition and product-order interfaces were read before execution. A kernel-checked finite equality proves `Nat.Coprime d auxiliary`; its prime-power consequence discharges the full CRT coprimality premise. The `full_order` endpoint then proves

```text
orderOf ((B : ZMod(d*auxiliary^(k+1)))^(auxiliary−1)) = auxiliary^k.
```

The block factorization `(d*auxiliary)*auxiliary^k = d*auxiliary^(k+1)` is proved, with explicit generic transport avoiding evaluation of the enormous B. `block_projection` proves the actual projection to `ZMod(d*auxiliary)` is1. Applying the generic construction gives `exists_coordinates` for every natural `k`. `exists_base_power_coordinates` rewrites the same constructed equivalence as

```text
B^((auxiliary−1)*(e z).val) = 1 + (d*auxiliary)*z.val
```

modulo the complete block modulus `(d*auxiliary)*auxiliary^k`. Thus the full modular power orbit and its affine parametrization are now conclusions. All hypotheses of the generic interface are discharged at the literal current constants; no supplied order/orbit/coordinate premise remains in these actual endpoints.

This packet does not yet place those exponents into safe physical dummy positions, derive a concrete Boolean coefficient's projected nonzero property, assemble an arbitrary-target physical subset, close the equation converse, or assert an internal ZFC equivalence. Those steps remain separate.

## Verification

Completely read all230 final source/check lines before successful execution. All commands used `Elab.async false` and the standard capped shape:

```text
lake env lean -M 6000 -j 1 -o .lake/build/lib/lean/DiophantineConsistency/NAME.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/NAME.lean
```

Generic main, actual main, generic Checks and actual Checks all exited zero. Both final main logs are empty; all14 axiom reports contain only subsets of `propext`, `Classical.choice`, and `Quot.sound` (the finite coprimality theorem has no axioms). No `native_decide`, new axiom, `sorry`, or `admit` occurs.

Checks cover an actual three-element orbit modulo9, composite C0=6 with a nine-element orbit modulo54, the singleton T=1, and the negative control that projection1 alone need not give the required order. Actual checks retain the full fixed modulus, the k=0/1 endpoints, the product identity and the unconditional affine B-power interface.

The first generic build needed an explicit natural-cast-one normalization when applying the quotient lemma. The first actual build needed an explicit natural-cast equality rather than backward rewriting `Nat.cast_one`, which had selected the exponent's one instead of the target's one. These were elaboration corrections only. No mathematical premise changed, no memory cap was raised, and no observational timeout prompted a restart.

## Frozen source and objects

- `ControllerPowerCoordinates.lean`: 42 lines; source SHA-256 `d15bf886e1f266c5b40757706e58f7d3a08cdeef8ae145110041b5308f2f3b2e`; object SHA-256 `bdc4f91dd48b9270e948cdfc8bb206fa294b7c28e2402b3554b20086f7cab2ad`.
- `ControllerPowerCoordinatesChecks.lean`: 36 lines; source SHA-256 `d65f5d660c0d0fc9d1f1a471512ea1b20dff59a68e6cacb8bbcaf3c5f8258514`; object SHA-256 `f58b0e96baa302827ec7bcf15f1b8c6371595143a0a69d13baa5ddac0a93971c`.
- `CurrentPowerCoordinates2011.lean`: 105 lines; source SHA-256 `53853c593225c4a616b0701bdbcd6773846e3a4add7cc5f653a9c7609bf96497`; object SHA-256 `c860089134eb67e9cee2236ed7f5af00dfcc67c1c1f410753245406f1bf81b69`.
- `CurrentPowerCoordinates2011Checks.lean`: 47 lines; source SHA-256 `d0e61dbaee6986d80c5348894aeaec32788c9d93e6827cef59908b1db6fe7c29`; object SHA-256 `ac5420afb36b3085e5f8d06d0374507bf9ad3eba0a0b7cc4bc1fc8711a5886ad`.

Direct project dependency identities:

- `ControllerResidueLift.lean`: `5b421650fb7565cb3c38f5e4819fdba7b46f61d8d1e37bc3ed786ac6ca2268cb`.
- `CurrentAuxiliaryOrder2011.lean`: `67db5e89285d56908ce482ffd72108c909ccc5e4f505ac2d324157344048e08e`.

Final logs and timing receipts:

- `/tmp/controller-power-coordinates-main2.log`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- `/tmp/current-power-coordinates-main-final.log`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- `/tmp/ControllerPowerCoordinatesChecks-final.log`: `3d4263d5d33b446d89d1502c3ec3e2f6df17850945ac0f3928752e1cf85d5d73`.
- `/tmp/CurrentPowerCoordinates2011Checks-final.log`: `b5a4b44f3ba05d3067e6785609da457e44b941663d0cefee35651f5302af67ee`.
- `/tmp/current-power-coordinates-main-final-time.log`: `51d9519b4ebb94b6905ec4cd40a4e5259fa25a3b860b8ff28f605a5e66fee71b`.
- `/tmp/controller-power-coordinate-checks-receipt.json`: `4f4a4a82c578801ae3e3ce08729959828364a65092e4ccc13b56d9dbb76b5f75`.
