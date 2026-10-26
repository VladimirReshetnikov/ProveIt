# Actual 2011 controller units: author receipt

Status: frozen, freshly checked on 2026-10-26. Author: `controller_certificate`.
This is an author audit, not an independent review. I read both complete final
sources before their capped builds. I previously authored `CurrentKernel2011`;
`complemented47_review` authored the checked controller data and literal kernel
residues; `circuit_reduction` authored `NativeRankVariation`. Those dependencies
were reused unchanged. Only the two new Lean files and this receipt were added;
no shared documentation, frozen source, or Git state was changed.

| File | Lines / bytes | SHA256 |
|---|---:|---|
| `Lean/DiophantineConsistency/CurrentControllerUnits2011.lean` | 201 / 8167 | `1c3bdb8af6c4113589b92b76aa895fbee3ecad4ca4d32f8e6290b382bf2f004f` |
| `Lean/DiophantineConsistency/CurrentControllerUnits2011Checks.lean` | 85 / 3595 | `40af856fb4a962ff6650b3a3f74758625377470935e9b7652476c9991a9e0bdf` |

## Exact scope

The new definitions are `dimension n = 120199^n`, `q n = B^(dimension n)`,
`A rw = CurrentKernel2011.K + B^(dimension rw)`, and

```
Gamma rw n = radix^977 * (q n^2 - 1) * (1 + q n * A rw).
```

`coprime_Gamma_width_cells` proves, without arithmetic or unit hypotheses,

```
Nat.Coprime (Gamma rw n) (94517 * 120199^n)
```

for every pair of natural exponents `rw,n`. `isUnit_Gamma_width_cells` gives
the corresponding unit in the actual quotient ring. The width exponent is
independent of the cell-count exponent; neither an inequality nor a divisibility
condition between the dimensions is supplied. In particular both exponents may
be zero. A zero exponent gives dimension one, not dimension zero.

`q_gt_one` derives strict positivity from the actual `B = 2^94517` before
`quadratic_ge_one` justifies every cast of the natural subtraction. The public
`Gamma_cast_rankGamma` identifies the complete natural coefficient with
`NativeRankVariation.rankGamma (q n : Int) (A rw : Int) (radix^977 : Int)`.
`Gamma_pos` proves its strict positivity. No source tuple, masked word, native
calibration, or assumed unit appears in those final statements.

## Mathematical audit

For the fixed primes 47 and 2011, the checked orders are 23 and 402. The actual
auxiliary prime is congruent to one modulo each order, so every power
`120199^n` is likewise congruent to one. `pow_eq_pow_of_modEq` then proves
`B^(120199^n) = B` in each corresponding `ZMod`. At the auxiliary prime,
`ZMod.pow_card_pow` proves the same equality by Frobenius, including exponent
zero. This last step does not use the separately developing LTE/order lifting.

The same power theorem is used separately for `n` and `rw`. Consequently the
coupling factor reduces to the original checked expression `1+B*K+B^2`,
without evaluating the large literal K again:

| prime | q residue | `(q^2-1)` residue | `(1+q*A)` residue |
|---:|---:|---:|---:|
| 47 | 37 | 5 | 29 |
| 2011 | 1283 | 1090 | 674 |
| 120199 | 37435 | 99282 | 36379 |

All last two entries are nonzero, so primality yields coprimality for the two
factors. Every prime is odd, so `radix = 2^47` and its 977th power are coprime
as well. Multiplication proves the three prime results, then coprimality with
`47*2011` and `120199^n`, hence with their complete product. No CRT orbit or
valuation claim is part of this argument.

The checks include dimension one, `q 0 = B`, the actual `A 0` residue, both
`Gamma 0 0` and the unequal-exponent case `Gamma 17 0`, all factor residues,
and the entire signed `windowRank` perturbation identity with the new Gamma.
They also distinguish a literal invalid width zero from a dimension-one
power, and verify that the degenerate `q=1` rank factor is zero and cannot be
coprime to d. All 14 printed axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`.

## Reproduction and build evidence

Toolchain: `leanprover/lean4:v4.32.0`. Its file SHA256 is
`2773c517aa90b66ea8a2c52bddddf84393157797f8341be0df45294fff7fd32e`.
Both new files use `Elab.async false`; no dependency build was launched.
From the repository root, the final commands were:

```sh
lake env lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentControllerUnits2011.lean -o .lake/build/lib/lean/DiophantineConsistency/CurrentControllerUnits2011.olean
lake env lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentControllerUnits2011Checks.lean -o .lake/build/lib/lean/DiophantineConsistency/CurrentControllerUnits2011Checks.olean
```

Each final process exited zero. Main: 5.06 seconds, 3,269,476 KB peak RSS;
checks: 3.35 seconds, 3,241,736 KB. The main has one benign elaboration notice
that exponent 977 exceeds the evaluation threshold 256. The final checks have
no warnings or errors. This is a fresh replay of the two new modules against
existing compiled dependencies, not a fresh replay of their entire closure.

| Artifact | SHA256 |
|---|---|
| New main `.olean` | `2b6f6f8e5766a198e7d66bda90b948f25e72c3f1d574ca9c5df48d2bfb1bcdde` |
| New checks `.olean` | `82a1fecea83f4d12fffa69ff386c7fb7d997780e2fae1f2dc385b38760b471c3` |
| `/tmp/current-controller-units2011-main.log` | `546cf62ed1ef5ba37843eb6d25203f452d4e0959616a34b6ff30167959632b48` |
| `/tmp/current-controller-units2011-checks.log` | `5c379544ca0c60d5f1c5c88c05f1ecfdb8edf13ca4390acd6dd9934261b0318a` |

The direct project dependency bindings used here are:

| Dependency | Source SHA256 | Imported object SHA256 |
|---|---|---|
| `CurrentKernelResidues2011` | `6e6812f7181a4b7fa5c558aef5f369c3068c21870710d522a979c39c877c8f4f` | `91a5c3514338ebe9f0ddbd3069e3928ff61595c332017ba773232b8c2a33063e` |
| `CurrentControllerData2011` | `a86aa5cc6b523bd659df8681012a1a39307ea340c27a7785629d30699ca151ae` | `d3e59650f41406c44c43bd0d702a16b9256f21c1242c6faeb4bbf0439951a7b8` |
| `NativeRankVariation` | `46c226eba0018eb15eaec66bb31b2ea8af7682fbef76d0245ee45c6aa236ef73` | `4d73da3692ddee9ed725396f830bf859743bcbfaaf5c90b6341007bd2f8c9232` |

The inspected mathlib source hashes are `e13bd133063e0349d955817f5f319f8c861f7d6136afa326cb477302348f1db3`
for `FieldTheory/Finite/Basic.lean` and `f5f551cc84fa8cc46ecd5b431703dbdc98d73c24d5d312dc9c35600659245169`
for `GroupTheory/OrderOfElement.lean`.

Development history: an initial literal-modulus conversion in the auxiliary
coupling theorem hit the 6 GB kernel cap. An opaque generic modulus-transport
lemma avoids reducing K during that conversion. Initial drafts also needed
an explicit natural-subtraction positivity lemma, auxiliary-modulus unfolding
for a small residue, and explicit integer casts in the signed perturbation
check. A redundant closed-natural `A 0 = K+B` check repeatedly triggered the
same kind of large-constant conversion even after an attempted abstract helper;
the final test checks the actual residue instead, while the universal theorem
and direct `Gamma 0 0` case retain full zero-exponent coverage. The memory cap
was never raised; no unsafe evaluator, additional axiom, or weakened final
coprimality theorem was introduced.

This packet establishes actual rank-step units only. It does not establish
prime-power orders, reachability of prescribed ranks, a safe Boolean dummy
mutation, or the converse polynomial/Con(ZFC) endpoint.
