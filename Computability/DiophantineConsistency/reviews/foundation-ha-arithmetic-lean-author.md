# Eight Foundation arithmetic axioms in HA: author receipt and next-obligation audit

Author: `circuit_reduction`. This is author review, not an independent peer
review. The complete new Lean sources and both private drivers were read before
execution; the final sources were reread before freeze. No frozen source,
vendor file, shared object, umbrella or Git state was changed.

## Frozen packet and replay

| File | Lines | SHA256 |
|---|---:|---|
| `Lean/DiophantineConsistency/FoundationHAArithmetic.lean` | 102 | `ece709d6a8f73c0b58663d529bed62762350f09cea4034bd9bf0ba69b2b999b8` |
| `Lean/DiophantineConsistency/FoundationHAArithmeticChecks.lean` | 82 | `b4f01c916e069d04a2d525bb0219b72580a330d11312000ab70435fbb0b68e44` |
| `reviews/foundation-ha-arithmetic-dependency-replay.json` | — | `3a3f7a2ad81e7dbf94e41e914635cd062e590813790009feca515f8c513cb050` |

The final snapshot is `b8f4085b41c32e92f4433eaedbee099237159e2c`.
Both final direct fresh builds passed with `-M6000 -j1` and source-level
`Elab.async false`, using `/tmp/foundation-ha-arithmetic-9e37o_cg`.
The main log is empty; checks contain exactly 22 reports using only
`propext` and/or `Quot.sound`. There are no final warnings, `sorryAx`, custom
axioms or `Classical.choice` in those reports.

Fresh main object:
`e0b34d4eca0748ad946ac7f7271054d160aa55b3e9e0bb3a7d7f17d3842c389c`.
Fresh checks object:
`5d5fc9763d0d3f5dd0925517811ea34a2ab830ac07565c319ef2b568889dff48`.

Two superseded development failures are preserved in the manifest: a local
notation used as a namespace and a final-list-membership simplification;
then a source numeral lacking an `OfNat` instance and an opaque decidable
equality in a structural negative control. The final control uses constructor
no-confusion and the literal source constant constructor. No failed object
was accepted, and the eight endpoint statements did not change.

## Authenticated dependency scope

The exact import closure contains 76 Foundation modules and 12 PAHF/HA
custom modules. All 76 Foundation records are contained in the previously
accepted arithmetic215 inventory of 95 modules, including all 17 beyond the
older 59-module GG closure. Every selected source, trace, and all four object
companions were rechecked by SHA256. Their recorded Lake source/output hashes
were compared to the accepted Lake-hash receipt and actual unchanged traces;
the overlapping 59 records also agree with the frozen GG manifest.
No genuinely new Foundation dependency or unvalidated source/object pair was
needed. The twelve other modules were reused under their exact source/object
pins. Compiler, toolchain and package identities were rechecked.

The source-header import walk finds neither broad `Mathlib.Tactic` nor the
conflicting `Mathlib.LinearAlgebra.Matrix.Defs`. The new leaves use narrow
imports and compile together successfully. No prerequisite, Foundation
arithmetic closure, or native-equation closure was freshly rebuilt. This is
two fresh leaves using authenticated prerequisites, not a fresh 88-module
replay. Commands, drivers, exact records, prior receipt hashes, logs and exit
codes are preserved in the JSON manifest.

## Literal axiom binding

Each theorem targets the existing named Foundation sentence, passed through
the existing `Semiformula.doubleNegation` and `FoundationPAHFSyntax.sentence`:

```lean
HA.Proves (FoundationPAHFSyntax.sentence PeanoMinus.Axiom.addZeroᴺ)
```

There are corresponding exact statements for the other seven rows below.
No renamed arithmetic-image axiom predicate is assumed. The concrete list
`semiringAxioms` contains exactly these eight original sentences; its length
is eight, `semiringAxioms_subset` proves source membership in `PeanoMinus`,
and `semiring_axiom` proves every listed sentence's literal GG image in HA.
It does not assert that derived formulas themselves belong to `Formula.Ax_s`.

| Actual Foundation axiom | HA equality used | Quantifier count |
|---|---|---:|
| `addZero` | `HA.Arithmetic.add_zero` | 1 |
| `addAssoc` | `HA.Arithmetic.add_assoc` | 3 |
| `addComm` | `HA.Arithmetic.add_comm` | 2 |
| `mulZero` | `HA.Arithmetic.mul_zero` | 1 |
| `mulOne` | `HA.Arithmetic.mul_one` | 1 |
| `mulAssoc` | `HA.Arithmetic.mul_assoc` | 3 |
| `mulComm` | `HA.Arithmetic.mul_comm` | 2 |
| `distr` | `HA.Arithmetic.mul_add` | 3 |

For each row, constructive HA double-negation introduction is applied to the
proved equality body **before** universal closure. The resulting literal
sentence has its quantifiers outside the double-negated equality. No
double-negation shift or elimination is used. Each `change` is definitional;
the checks independently state all eight exact syntax identities by `rfl`,
including de Bruijn variable order and the source-one interpretation `S 0`.
Further checks reopen the actual translated commutativity axiom at arbitrary
parameterized terms, and prove that `ltIrrefl` is not in the discharged list.

## Remaining arithmetic and induction obligations

The following is a read-only implementation map, **not additional theorems**.
The exact sources were reread: `PeanoMinus/Basic.lean:15–53`,
`Basic/Eq.lean:31–57`, `Arithmetic/Schemata.lean:19–55`, and GG definitions and
rewriting/implication lemmas in `NegationTranslation/GoedelGentzen.lean`.

All nine equality-theory cases remain to be linked to their actual GG images:
reflexivity, symmetry, transitivity; the four function symbols `0,1,+,*`;
and both relation symbols `=,<`. They require only HA equality rules and
constructive logical lifting. In particular, relation congruence for `<`
uses equality elimination in the actual existential `ltFormula`; it does not
require an order axiom. The zero-arity function cases retain the source's
empty-conjunction antecedent. A suitable next exact endpoint is:

```lean
-- Proposed, not yet proved:
theorem equality_axiom {σ : Sentence ℒₒᵣ}
    (h : σ ∈ Theory.eqAxiom ℒₒᵣ) : HA.Proves (sentence σᴺ)
```

Nine PeanoMinus order/geometric cases remain. Write
`L(x,y) := exists d, x + S d = y`, with the existing capture-avoiding shifts.

| Source axiom | Concrete constructive HA work still required |
|---|---|
| `addEqOfLt` | Eliminate an `L(x,y)` witness `d`, then supply `S d` as the summand. |
| `zeroLe` | Actual zero/predecessor decomposition; prove `0=x` or `L(0,x)`. |
| `zeroLtOne` | Explicit witness zero and the proved `zero_add` identity. |
| `oneLeOfZeroLt` | From `x=S d`, split `d=0` or `d=S e`; supply equality with one or the order witness `e`. |
| `addLtAdd` | Reuse the order witness and the proved additive rearrangements. |
| `mulLtMul` | From witnesses `d` and `z=S e`, use difference witness `d*z+e`, since `(S d)*z=S(d*z+e)`. |
| `ltIrrefl` | HA formula induction proving `x+S d≠x`, using successor injectivity/nonzero. |
| `ltTrans` | Compose witnesses `d,e` using witness `d+S e` and additive identities. |
| `ltTri` | Actual nested formula induction and zero/predecessor cases; no unrestricted LEM. |

The natural-case packet owned by `complemented47_review` is separate and was
not assumed or imported here. The displayed positive facts still need to be
connected to the exact GG encodings of source implications/disjunctions and
existentials. Foundation classical implication is NNF disjunction, so its GG
image is not definitionally a primitive implication. Reuse the proved logical
equivalence `Derivation.imply_doubleNegation` through the existing logical
adapter, or prove the required finite constructive implications directly.

Arbitrary induction is a distinct next leaf. Proposed unclosed target:

```lean
-- Proposed, not yet proved:
theorem translated_succInd (φ : Semiformula ℒₒᵣ Nat 1) :
    HA.Proves (formula (Arithmetic.succInd φ)ᴺ)
```

Instantiate actual HA induction at `formula φᴺ`, transport zero/successor
substitutions, and replace the source `x+1` by `S x` using the proved HA
`add_one` equality under the arbitrary body. Convert the curried source
premises using the existing GG implication equivalence. The final source
axiom is `Semiformula.univCl (succInd φ)`, so its `fvSup/fixitr/allClosure/
toEmpty` parameter closure must also be proved to match the target closure.
The current syntax leaf has the required environment/rewrite tools but does
not yet prove this whole closure theorem. In particular, the inspected
intuitionistic formula module does not supply an analogous `univCl` definition
that may simply be substituted for the actual classical source closure.

Neither order, equality-theory transport, induction transport, the actual215
internal calibration, nor the final HA consistency-equivalence endpoint is
claimed by this packet. No GG recursion has been copied or replaced.

## Primary source pins for the remaining-obligation audit

Paths are relative to the unchanged Foundation source root
`/home/codex/src/Proofs/lib/FormalizedFormalLogic-Foundation/Foundation/`.

| Source | SHA256 |
|---|---|
| `FirstOrder/Arithmetic/PeanoMinus/Basic.lean` | `856a38ddda30c1505f6d991e6033ef7c41ebc82418b503ab711dfe173dc72303` |
| `FirstOrder/Basic/Eq.lean` | `f1a53113cb76030f89a78579f822dcfab1e53dccb1b8ede7caf8287630ab63d6` |
| `FirstOrder/Arithmetic/Schemata.lean` | `5b1a1d84b71c3f943a0867c14d3b0c8c381062ec742d984fefdacf9f2209a6fd` |
| `FirstOrder/NegationTranslation/GoedelGentzen.lean` | `52fabd00a01e1f5671e1f078c36f9848f2e219e0a4e616deaad4e523057586ea` |
