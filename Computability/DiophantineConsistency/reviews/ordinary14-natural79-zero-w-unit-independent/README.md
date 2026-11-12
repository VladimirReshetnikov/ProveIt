# Independent source review: natural-79 units at w=0

The [unelaborated source draft](../../research/ordinary14-natural79-zero-w-unit-draft/README.md) states a mathematically valid route from a 79 graph zero at `w=0` and three explicit residue-exclusion premises to positive units for all five factors. Its stated assumptions do not require beta, J, gamma, K0 or w positive. The draft and its supporting sources have not been type-checked or run in Lean; its graph-pattern residue hypotheses are not discharged by this packet.

The pinned literal graph has `X=q*w`, `ell=(X*Y)*kY`, and first factor `F0=r²-ell*(ell+k)`, so `w=0` gives the exact arbitrary-port identity `F0=r²` over a commutative ring. In an ordered difference ring that square is nonnegative and cannot equal `-1`. The source product order is first, main, auxiliary, strong, guard; the proposed signed-pair conversion swaps the last two to match the existing `product5_positive` signature, which requires negative-unit exclusions for the first, main, auxiliary and strong factors and forces the remaining guard unit. This is a logical source-level match, not verification of the tactic calls or pair coercions.

The three generic modulo-four source lemmas each exclude the negative unit for an explicit expression pattern. The draft's `restricted_residues_of_shapes` takes all three 79-factor pattern equalities as hypotheses: it does not prove them merely by citing the generic lemmas. Binding those expressions, proving the subsequent J/divisibility steps and obtaining a coherent endpoint remain separate obligations.

The receipt pins the candidate, graph source, new draft and relevant signed-pair and residue signatures. It checks selected exact DAG rows and performs 150 finite signed-port controls at `w=0`; finite controls do not replace the unbounded ordered-model reasoning or Lean proof checking. No axiom report, provider closure, iPRA derivability or physical-file/PDF association is established.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural79-zero-w-unit-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural79-zero-w-unit-independent/result.json
```
