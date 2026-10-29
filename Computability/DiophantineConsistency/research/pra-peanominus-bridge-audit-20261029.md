# Foundation PA-minus into candidate PRA: axiom audit

The desired statement is `PRA ⊢ Semiformula.lMap PRALanguage.embedding σ` for every `σ ∈ 𝗣𝗔⁻`, where `embedding : ℒₒᵣ →ᵥ language` maps `0`, `1`, `+`, `*`, equality, and strict order to the designated finite primitive-recursive function codes and the candidate's order relation. The target `PRA` is the candidate first-order theory defined in this repository. A theorem transporting all Foundation PA-minus proofs is a subsequent consequence, not yet established.

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
| `addLtAdd` | Not yet discharged; depends on addition and order compatibility. |
| `mulZero` | `PRAPeanoMinusBasic.PRA_proves_mulZero` proves the exact mapped sentence using the established Q proof. |
| `mulOne` | `PRAPeanoMinusBasic.PRA_proves_mulOne` proves the exact mapped sentence from multiplication recursion and zero laws. |
| `mulAssoc` | `PRAPeanoMinusMulAssoc.PRA_proves_mulAssoc` proves the exact mapped axiom using open induction and distributivity in arbitrary candidate-PRA models. |
| `mulComm` | `PRAPeanoMinusMulComm.PRA_proves_mulComm` proves the exact mapped axiom using open induction and multiplication left-zero and left-successor in arbitrary candidate-PRA models. |
| `mulLtMul` | Not yet discharged. |
| `distr` | `PRAPeanoMinusDistributivity.PRA_proves_distr` proves the exact mapped axiom using open induction and mapped-model addition associativity. |
| `ltIrrefl` | `PRAPeanoMinusOrderBasic.PRA_proves_ltIrrefl` proves the exact mapped axiom in arbitrary candidate-PRA models. |
| `ltTrans` | Not yet discharged. |
| `ltTri` | `PRAPeanoMinusOrderBasic.PRA_proves_ltTri` proves the exact mapped axiom in arbitrary candidate-PRA models. |

The existing `PRAQOrder.PRA_proves_all_Q` discharges every **Robinson Q axiom**, including its strict-order clause, under the same embedding, and `PRAQProofTranslation.PRA_proves_qTheorem` transports Q theorems via soundness and completeness. PA-minus has additional ordered semiring and trichotomy axioms, so the Q theorem cannot be substituted for the desired PA-minus theorem. Existing addition/multiplication recursion laws, induction rule, subtraction and order witness lemmas are ingredients for the remaining families.

The proof route takes place in classical Lean metatheory and must not be confused with an internal HA proof. Even a complete PA-minus interpretation would not eliminate the Σ₁ induction rule or establish the required PRA equivalence. The HA equivalence for the maintained 14-variable PDF equation is already established separately.
