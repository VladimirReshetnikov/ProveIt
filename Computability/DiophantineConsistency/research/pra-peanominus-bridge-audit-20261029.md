# Foundation PA-minus into candidate PRA: axiom audit

The desired statement is `PRA ⊢ Semiformula.lMap PRALanguage.embedding σ` for every `σ ∈ 𝗣𝗔⁻`, where `embedding : ℒₒᵣ →ᵥ language` maps `0`, `1`, `+`, `*`, equality, and strict order to the designated finite primitive-recursive function codes and the candidate's order relation. The target `PRA` is the candidate first-order theory defined in this repository. `PRAPeanoMinusTranslation.PRA_proves_peanoMinusAxiom` covers every axiom constructor, and `PRA_proves_peanoMinusTheorem` transports every Foundation PA-minus theorem using first-order soundness and completeness in the Lean metatheory. An independent replay against the separately checked order provider passed at `/tmp/pra-peanominus-translation-independent-mjfgmjj7`.

Foundation's `PeanoMinus` has equality plus these 17 non-equality families. An earlier progress report and version of this audit incorrectly said 16; the constructor-by-constructor count is 17. Status below concerns proofs at the exact mapped Foundation sentence, not merely standard-natural truth. A model lemma is a fact in **arbitrary** candidate-PRA equality models; Foundation completeness can then yield a closed candidate-PRA derivation. “Not yet discharged” means no exact mapped theorem has been verified in this audit; it does not assert unprovability.

| Foundation axiom | Current evidence and remaining work |
| --- | --- |
| Equality | `PRAQCompatibility.PRA_proves_qEquality` proves the exact mapped equality axioms. |
| `addZero` | `PRAPeanoMinusBasic.PRA_proves_addZero` proves the exact mapped sentence using the established Q proof. |
| `addAssoc` | `PRAPeanoMinusAddAssoc.PRA_proves_addAssoc` proves the exact mapped axiom using open induction in arbitrary candidate-PRA models. |
| `addComm` | `PRAPeanoMinusBasic.PRA_proves_addComm` proves the exact mapped sentence using the arbitrary-model addition commutativity lemma. |
| `addEqOfLt` | `PRAPeanoMinusOrderBasic.PRA_proves_addEqOfLt` proves the exact mapped axiom in arbitrary candidate-PRA models. |
| `zeroLe` | `PRAPeanoMinusOrderBasic.PRA_proves_zeroLe` proves the exact mapped axiom in arbitrary candidate-PRA models. |
| `zeroLtOne` | `PRAPeanoMinusOrderBasic.PRA_proves_zeroLtOne` proves the exact mapped axiom in arbitrary candidate-PRA models. |
| `oneLeOfZeroLt` | `PRAPeanoMinusOrderBasic.PRA_proves_oneLeOfZeroLt` proves the exact mapped axiom in arbitrary candidate-PRA models. |
| `addLtAdd` | `PRAPeanoMinusOrderAlgebra.PRA_proves_addLtAdd` proves the exact mapped axiom using the order witness and addition laws. |
| `mulZero` | `PRAPeanoMinusBasic.PRA_proves_mulZero` proves the exact mapped sentence using the established Q proof. |
| `mulOne` | `PRAPeanoMinusBasic.PRA_proves_mulOne` proves the exact mapped sentence from multiplication recursion and zero laws. |
| `mulAssoc` | `PRAPeanoMinusMulAssoc.PRA_proves_mulAssoc` proves the exact mapped axiom using open induction and distributivity in arbitrary candidate-PRA models. |
| `mulComm` | `PRAPeanoMinusMulComm.PRA_proves_mulComm` proves the exact mapped axiom using open induction and multiplication left-zero and left-successor in arbitrary candidate-PRA models. |
| `mulLtMul` | `PRAPeanoMinusOrderAlgebra.PRA_proves_mulLtMul` proves the exact mapped axiom using order witnesses and distributivity. |
| `distr` | `PRAPeanoMinusDistributivity.PRA_proves_distr` proves the exact mapped axiom using open induction and mapped-model addition associativity. |
| `ltIrrefl` | `PRAPeanoMinusOrderBasic.PRA_proves_ltIrrefl` proves the exact mapped axiom in arbitrary candidate-PRA models. |
| `ltTrans` | `PRAPeanoMinusOrderAlgebra.PRA_proves_ltTrans` proves the exact mapped axiom using order witnesses. |
| `ltTri` | `PRAPeanoMinusOrderBasic.PRA_proves_ltTri` proves the exact mapped axiom in arbitrary candidate-PRA models. |

The existing `PRAQOrder.PRA_proves_all_Q` discharges every **Robinson Q axiom**, including its strict-order clause, under the same embedding, and `PRAQProofTranslation.PRA_proves_qTheorem` transports Q theorems via soundness and completeness. PA-minus has additional ordered semiring and trichotomy axioms, so the Q theorem cannot be substituted for the desired PA-minus theorem. The mapped PA-minus axiom proofs use open induction, subtraction, and the order-witness characterization in arbitrary candidate-PRA equality models.

The proof route takes place in classical Lean metatheory and must not be confused with an internal HA proof. Even a complete PA-minus interpretation would not eliminate the Σ₁ induction rule or establish the required PRA equivalence. The HA equivalence for the maintained 14-variable PDF equation is already established separately.

After the independent translation replay, an upstream merge changed
`PRAQCompatibility` and `PRAPeanoMinusBasic`. The replay covers the preceding
source snapshot; the affected chain needs a current-source rebuild.
