# Author receipt: exact odd-prime-power order and actual auxiliary generator

The four new modules below are frozen after complete self-review and successful fresh sequential Lean compilation. This is an author receipt; an independent peer review remains separate. No previously accepted source, coefficient, equation, umbrella file, documentation index, or Git state was changed.

## Generic theorem and exact assumptions

`PrimePowerOrder.order_succ` proves

```text
Nat.Prime p → Odd p → p ∣ (g−1) → ¬ p² ∣ (g−1) →
  orderOf (g : ZMod (p^(k+1))) = p^k
```

for every natural `k`. `order_prime_power` gives the requested `n ≥ 1` formulation with order `p^(n−1)`. The only hypotheses are exactly those displayed. The module derives `1 < g` from nondivisibility by `p²`, rejecting natural values0 and1 before using subtraction. It derives `p ∤ g` from primality and `p ∣ g−1`.

`exact_lift` proves both divisibility by `p^(k+1)` and nondivisibility by `p^(k+2)` of `g^(p^k)−1`. It applies Mathlib's ordinary natural LTE theorem with `x=g,y=1`, proves base multiplicity exactly1, and uses the prime-power self multiplicity. The cast bridge explicitly supplies `1 ≤ g^k` before rewriting natural subtraction. The order proof treats modulus `p` separately with order1; higher powers use `orderOf_eq_prime_pow` with both the exact vanishing and preceding nonvanishing witnesses. No assumption that an orbit has the desired size appears.

Read the complete primary Mathlib `NumberTheory/Multiplicity.lean`, the used multiplicity divisibility/equality interfaces, the relevant `OrderOfElement` order and prime-power proofs, and the modular cast/congruence interfaces before executing this work. The generic module's direct imports are those three Mathlib areas: `NumberTheory.Multiplicity`, `Data.ZMod.Basic`, and `GroupTheory.OrderOfElement`.

## Actual maintained auxiliary binding

`CurrentAuxiliaryOrder2011` imports the generic theorem and the frozen `CurrentControllerData2011`. For the literal values `B=2^94517` and `auxiliary=120199`, it derives the entire domain interface from the already checked equality

```text
B^(auxiliary−1) % auxiliary² = 7300767062
                             = 1 + auxiliary*60739.
```

The positive residue bounds the generator below, projection gives residue1 modulo the auxiliary prime, natural modular congruence gives divisibility of generator−1, and the nontrivial lift excludes square divisibility. Thus `generator_order_succ k` proves the actual modular expression

```text
orderOf ((B : ZMod (auxiliary^(k+1)))^(auxiliary−1)) = auxiliary^k.
```

`generator_order n hn` gives `auxiliary^(n−1)` for every `n≥1`. Actual positivity, prime nondivisibility and exact lifted divisibilities are also public. The huge natural generator is kept symbolic; it is not evaluated as a numeral.

This proves the auxiliary prime-power order. It does not yet prove the simultaneous full-modulus CRT orbit, its affine coordinate bijection, safe controller positions, prescribed cardinality realization in those positions, the equation converse, or an internal ZFC equivalence. No missing domain premise is hidden in the displayed order theorems.

## Verification

All four final sources were completely read before their successful executions. Each used `Elab.async false`, with the command shape:

```text
lake env lean -M 6000 -j 1 -o .lake/build/lib/lean/DiophantineConsistency/NAME.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/NAME.lean
```

Execution order was generic main, generic Checks, actual main, actual Checks. All four final commands exited zero, both final main logs are empty, and the14 focused axiom reports contain only subsets of `propext`, `Classical.choice`, and `Quot.sound`. No `native_decide`, new axiom, `sorry`, or `admit` is used.

Checks retain the modulus-p base case, the order9 example4 modulo27, arbitrary lifted exponents, natural g=0/1 exclusion, and a cast-bridge exponent0/modulus0 endpoint. Negative controls show why oddness matters (3 modulo8 has order2 despite a first-order2-adic lift) and why the nontrivial lift matters (10 modulo9 already has order1). Actual checks cover prime, square and cube auxiliary moduli and the checked nonzero lift digit.

The first generic compile found only a dependent type simplification issue in its modulus-p base case: simplification of the modulus expression did not transport the cast instance. The correction keeps that exact modulus in the cast bridge. The corrected generic main and all subsequent three builds passed. No arithmetic hypothesis or conclusion was changed; no resource cap was raised and no observational timeout caused a restart.

## Frozen identities

- `PrimePowerOrder.lean`: 80 lines; source SHA-256 `781aa36c18153b4f7e7e6b7df204b3b42545bc8cabf0f9f25736d012e598dd47`; object SHA-256 `348b7f689fd74a426167fa298fb71575d67e78627894ac4b2b98d3c67751f27b`.
- `PrimePowerOrderChecks.lean`: 46 lines; source SHA-256 `c7f8fe09ae961e9879e166a62cbc299b2995702e432323ad4dd00a7f9b165eaa`; object SHA-256 `789ee101c1e65b0c837e60e6ade67d650ead6c6c85ba39d3eb1eaa29179f334b`.
- `CurrentAuxiliaryOrder2011.lean`: 62 lines; source SHA-256 `67db5e89285d56908ce482ffd72108c909ccc5e4f505ac2d324157344048e08e`; object SHA-256 `a444266e8175211407a465402fc5f2ae65023025654df86ff1f743b145ba1899`.
- `CurrentAuxiliaryOrder2011Checks.lean`: 43 lines; source SHA-256 `5f5c6ea233495dec39d7842ce0393b5ba7d607a10a16ca78ef63f2a41953aca1`; object SHA-256 `57d48fb13c6aa5442668633d785a188c7a37ce05dac6a46d9f1d7e82717f6475`.

Frozen actual-data dependency:

- `CurrentControllerData2011.lean`: `a86aa5cc6b523bd659df8681012a1a39307ea340c27a7785629d30699ca151ae`.

Complete final logs:

- `/tmp/prime-power-order-main-final.log`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- `/tmp/prime-power-order-checks1.log`: `31d7c7bb08b174805a6a40e02f6c6c0567b78afc2244da346288c800087e30b5`.
- `/tmp/current-auxiliary-order-main1.log`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- `/tmp/current-auxiliary-order-checks1.log`: `3495b16063934dcb8c62cf805161124e322958847444825311525f0728a13601`.
