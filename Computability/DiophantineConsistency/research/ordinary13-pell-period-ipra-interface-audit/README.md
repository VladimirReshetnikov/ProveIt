# Interface from the Pell-period model lemma to iPRA

There **is** an existing all-model-to-iPRA theorem for a complete equation/machine bridge: `IPRAExpressionNative.equivalence_of_bridge` accepts `HAExpressionAssembly.PolynomialBridge e` and returns the selected native-iPRA no-zero/consistency biconditional. The proposed `h=2mc` period lemma is only one internal-model ingredient; it does not have that bridge's type and cannot be passed to this theorem on its own. The conditional parent construction, its model realization and the new period specialization remain unelaborated. The historical iPRA endpoint for the separately displayed 14-variable equation is a distinct result with its own provider qualifications.

## The actual existing end-to-end interface

For a finite integer expression e, `PolynomialBridge e` requires **every** relevant `IΣ₁` model to satisfy the equivalence between the literal no-zero sentence and absence of a halting time for the designated represented machine. `HAExpressionAssembly.isigma1_equivalence` uses classical first-order completeness and the separately proved machine/refutation bridge to produce an `IΣ₁` derivation of `classicalNoZero e ↔ sourceSentence`. `PRAExpressionZFCStrict.comparison_of_isigma1` applies a specialized witness-transfer theorem to produce the corresponding comparison in the selected classical PRA. `IPRAExpressionNative.comparison_of_pra` uses negative translation, the specific no-zero translation identity, and the selected ZFC refutation comparison. Finally `IPRAStandardTheory.provable_iff` transfers the same intuitionistic-language sentence between the repository's native and standard iPRA presentations.

These are genuine source interfaces, subject to their documented historical compilation/provider scopes. The whole-expression assembly does **not** say that any arbitrary theorem about all `IΣ₁` models yields a derivation of its intended positive existential form in iPRA. The conditional lift would first need its actual graph bindings and all necessary witness hypotheses established in those models, plus both directions of the complete polynomial/machine bridge or another separately proved syntactic route.

## A precise standalone period obligation

A possible first-order `ℒₒᵣ` period sentence σ would universally quantify m and a and existentially quantify c, h, xh, yh, r and t, asserting

```text
yDef(c,m,a) ∧ h=2*m*c ∧ xDef(xh,h,a) ∧ yDef(yh,h,a)
∧ xh=1+c*c*r ∧ yh=t*c*c.
```

This is an illustrative logical specification, **not** an existing checked Lean definition. The current `ArithmeticPellRecurrence` source supplies `xDef`, `yDef` and their `Σ₁` function representations. A concrete σ must still be built with correct bound-variable order, multiplication terms, quantifier scopes and evaluation lemmas. If the new draft elaborates, its all-model statement and those evaluation lemmas can provide a classical `IΣ₁ ⊢ σ` via the same completeness pattern. A single standard-natural check would not suffice.

To use `PRAISigmaOneOpenComparison.comparison`, one must additionally choose a candidate-PRA `θ` with `θ.Open` and prove in classical PRA that the language-mapped σ implies `(∃⁰ θ).univCl`. This typically requires a concrete primitive-recursive coding or packing of all witnesses, source/candidate graph correspondence and an open characteristic relation. The theorem's explicit `hgoal` premise is substantive; it is not supplied by the model lemma. `PRAWitnessTransfer.transfer` is also conditional: it requires the specified Σ₁ graph hypotheses, all-model replacement statement, a candidate-PRA dominating term and an already bounded instance. It is not a generic unconditional extraction of the period witnesses. This audit makes no exhaustive claim that no alternative Pell code exists elsewhere in the repository.

`IPRAFullGGTransfer.from_classical` accepts a **classical PRA derivation** of a sentence φ and produces its Gödel–Gentzen translation `φᴺ` in native iPRA. It does not directly accept an `IΣ₁` model theorem. For a positive `∀ parameters, ∃ witnesses` period assertion, the translated existential remains negatively translated; even if the matrix's atomic equalities are made stable, an intuitionistic step from double-negated existence to actual unbounded existence is an additional obligation. `IPRANativeOpenDecidable.openStable` concerns open formulas, and `IPRAMappedNoZero.mapped_gg_noZero` is specifically a universally quantified **negated equality**. Neither source interface removes a general positive unbounded existential. A direct primitive-recursive witness construction and internal proof, or an appropriately proved bounded/constructive witness theorem, is a possible alternative; neither is provided here.

## What the explicit index does and does not solve

For `h=2*m*c`, ordinary natural arithmetic gives `gcd(4h,c)=gcd(8mc,c)=c`, including c=0. Thus the general conditional lift's premise `gcd(4h,c) | (R−m)` reduces for this explicit h to the stronger `c | (R−m)` used by the special lift. The stronger existing ordinate divisibility at `h=m*c` gives the same simplification. Neither supplies that rank congruence or the `m≡3 (mod 4)` premise. The separate actual-graph mod-5 obstruction shows a conditional slice where that phase premise cannot hold; alternative witnesses or a different transfer would be needed there.

`check.py` pins and inspects the exact named source signatures and checks 900 small instances of the elementary gcd identity. This is a bounded source audit, not an exhaustive repository search, Lean elaboration, provider/axiom check or proof of a new iPRA theorem. Reproduce from `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary13-pell-period-ipra-interface-audit/check.py | cmp - research/ordinary13-pell-period-ipra-interface-audit/receipt.json
```
