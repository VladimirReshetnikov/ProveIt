import DiophantineConsistency.ObjectMultiplication
import DiophantineConsistency.NaturalExpression

/-!
# Interpreting supplied natural expression syntax inside ZFC

The formula generator uses only the supplied finite expression and coordinate
map. Its correctness holds for every ZF model's internal natural numbers.
Object-level totality and functionality are derived by first-order completeness.
-/

namespace DiophantineConsistency.ObjectNaturalExpression

set_option maxRecDepth 16000

open SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency
open ObjectArithmetic ObjectMultiplication

universe u
variable {V : Type u} {mem : V → V → Prop} {σ : Type*}

/-- Relational evaluation over an arbitrary model's internal arithmetic. -/
def EvalRel (H : ZFAxioms mem) (v : σ → V) : NatExpr σ → V → Prop
  | .constant n, z => z = natV H n
  | .var i, z => z = v i
  | .add p q, z => ∃ a b, EvalRel H v p a ∧ EvalRel H v q b ∧ AddRel H a b z
  | .mul p q, z => ∃ a b, EvalRel H v p a ∧ EvalRel H v q b ∧ MulRel H a b z

/-- Compile expression evaluation to a set-theory formula with explicit
free-coordinate slots and a specified output slot. -/
def evalForm : NatExpr σ → (σ → Nat) → Nat → Form
  | .constant n, _, z => fNumF z n
  | .var i, coordinates, z => fEq z (coordinates i)
  | .add p q, coordinates, z =>
      fEx (fEx (fAnd (evalForm p (fun i => coordinates i + 2) 1)
        (fAnd (evalForm q (fun i => coordinates i + 2) 0) (addForm (z + 2) 1 0))))
  | .mul p q, coordinates, z =>
      fEx (fEx (fAnd (evalForm p (fun i => coordinates i + 2) 1)
        (fAnd (evalForm q (fun i => coordinates i + 2) 0) (mulForm (z + 2) 1 0))))

/-- Exact arbitrary-model semantics for the supplied formula generator. -/
theorem evalForm_spec (H : ZFAxioms mem) (e : NatExpr σ)
    (coordinates : σ → Nat) (z : Nat) (ee : Nat → V) :
    Sat mem ee (evalForm e coordinates z) ↔ EvalRel H (ee ∘ coordinates) e (ee z) := by
  induction e generalizing coordinates z ee with
  | constant n => exact fNumF_spec H n z ee
  | var i => rfl
  | add p q hp hq | mul p q hp hq =>
    simp only [evalForm, Sat, EvalRel, hp, hq, addForm_spec H, mulForm_spec H,
      Function.comp_def, scons]

theorem evalRel_result_nat (H : ZFAxioms mem) (v : σ → V)
    (hv : ∀ i, mem (v i) (omegaV H)) (e : NatExpr σ) {z : V} (h : EvalRel H v e z) :
    mem z (omegaV H) := by
  induction e generalizing z with
  | constant n => rw [h]; exact natV_mem_omega H n
  | var i => rw [h]; exact hv i
  | add p q hp hq => exact addRel_result_nat H h.choose_spec.choose_spec.2.2
  | mul p q hp hq => exact mulRel_result_nat H h.choose_spec.choose_spec.2.2

theorem evalRel_total (H : ZFAxioms mem) (v : σ → V)
    (hv : ∀ i, mem (v i) (omegaV H)) (e : NatExpr σ) : ∃ z, EvalRel H v e z := by
  induction e with
  | constant n => exact ⟨natV H n, rfl⟩
  | var i => exact ⟨v i, rfl⟩
  | add p q hp hq | mul p q hp hq =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hq
      have haN := evalRel_result_nat H v hv p ha
      have hbN := evalRel_result_nat H v hv q hb
      first
      | obtain ⟨z, hz⟩ := addRel_total H haN hbN
        exact ⟨z, a, b, ha, hb, hz⟩
      | obtain ⟨z, hz⟩ := mulRel_total H haN hbN
        exact ⟨z, a, b, ha, hb, hz⟩

theorem evalRel_unique (H : ZFAxioms mem) (v : σ → V) (e : NatExpr σ)
    {z z' : V} (h : EvalRel H v e z) (h' : EvalRel H v e z') : z = z' := by
  induction e generalizing z z' with
  | constant n => exact h.trans h'.symm
  | var i => exact h.trans h'.symm
  | add p q hp hq | mul p q hp hq =>
      obtain ⟨a, b, ha, hb, hz⟩ := h
      obtain ⟨a', b', ha', hb', hz'⟩ := h'
      have ea := hp ha ha'
      have eb := hq hb hb'
      subst a'
      subst b'
      first
      | exact addRel_unique H hz hz'
      | exact mulRel_unique H hz hz'

/-- Internal expression evaluation agrees with external evaluation on numerals. -/
theorem evalRel_numerals (H : ZFAxioms mem) (v : σ → Nat) (e : NatExpr σ) :
    EvalRel H (fun i => natV H (v i)) e (natV H (e.eval v)) := by
  induction e with
  | constant n => rfl
  | var i => rfl
  | add p q hp hq => exact ⟨_, _, hp, hq, addRel_numerals H _ _⟩
  | mul p q hp hq => exact ⟨_, _, hp, hq, mulRel_numerals H _ _⟩

theorem evalRel_numerals_iff (H : ZFAxioms mem) (v : σ → Nat) (e : NatExpr σ) (z : V) :
    EvalRel H (fun i => natV H (v i)) e z ↔ z = natV H (e.eval v) := by
  constructor
  · intro h
    exact evalRel_unique H _ e h (evalRel_numerals H v e)
  · intro h
    subst z
    exact evalRel_numerals H v e

private def conjunctionForm : List Form → Form
  | [] => fImp fBot fBot
  | f :: fs => fAnd f (conjunctionForm fs)

private theorem conjunctionForm_spec (ee : Nat → V) (fs : List Form) :
    Sat mem ee (conjunctionForm fs) ↔ ∀ f ∈ fs, Sat mem ee f := by
  induction fs with
  | nil => simp [conjunctionForm, Sat]
  | cons f fs ih => simp [conjunctionForm, Sat, ih]

/-- A finite guard that all supplied free coordinates are internal naturals. -/
def inputsNaturalForm {n : Nat} (coordinates : Fin n → Nat) : Form :=
  conjunctionForm (List.ofFn (fun i => fNatF (coordinates i)))

theorem inputsNaturalForm_spec (H : ZFAxioms mem) {n : Nat}
    (coordinates : Fin n → Nat) (ee : Nat → V) :
    Sat mem ee (inputsNaturalForm coordinates) ↔ ∀ i, mem (ee (coordinates i)) (omegaV H) := by
  rw [inputsNaturalForm, conjunctionForm_spec]
  constructor
  · intro h i
    exact (fNatF_spec H ee (coordinates i)).mp
      (h _ (List.mem_ofFn.mpr ⟨i, rfl⟩))
  · intro h f hf
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
    exact (fNatF_spec H ee (coordinates i)).mpr (h i)

/-- A closed sentence asserting total evaluation at the supplied natural inputs. -/
def totalForm {n : Nat} (e : NatExpr (Fin n)) (coordinates : Fin n → Nat) : Form :=
  sealF (fImp (inputsNaturalForm coordinates)
    (fEx (evalForm e (fun i => coordinates i + 1) 0)))

theorem sentence_totalForm {n : Nat} (e : NatExpr (Fin n)) (coordinates : Fin n → Nat) :
    Sentence (totalForm e coordinates) := Sentence_seal _

/-- A closed sentence asserting functionality of the supplied evaluation formula. -/
def uniqueForm {n : Nat} (e : NatExpr (Fin n)) (coordinates : Fin n → Nat) : Form :=
  sealF (fImp (inputsNaturalForm coordinates)
    (fAll (fAll (fImp
      (fAnd (evalForm e (fun i => coordinates i + 2) 1)
        (evalForm e (fun i => coordinates i + 2) 0)) (fEq 1 0)))))

theorem sentence_uniqueForm {n : Nat} (e : NatExpr (Fin n)) (coordinates : Fin n → Nat) :
    Sentence (uniqueForm e coordinates) := Sentence_seal _

/-- Actual ZFC provability of totality, for every supplied finite expression. -/
theorem zfc_proves_total {n : Nat} (e : NatExpr (Fin n)) (coordinates : Fin n → Nat) :
    BProv ZFCax_s [] (totalForm e coordinates) := by
  apply completeness_inf_context ZFCax_s [] _ Sentences_ZFC
  intro Dom m v hmodel _
  let H := axioms_of_zfc_model v hmodel
  apply (seal_valid (mem := m) _).mpr ?_ v
  intro ee hg
  have hv := (inputsNaturalForm_spec H coordinates ee).mp hg
  obtain ⟨z, hz⟩ := evalRel_total H (ee ∘ coordinates) hv e
  exact ⟨z, (evalForm_spec H e (fun i => coordinates i + 1) 0 (scons z ee)).mpr hz⟩

/-- Actual ZFC provability of functionality, including zero input coordinates. -/
theorem zfc_proves_unique {n : Nat} (e : NatExpr (Fin n)) (coordinates : Fin n → Nat) :
    BProv ZFCax_s [] (uniqueForm e coordinates) := by
  apply completeness_inf_context ZFCax_s [] _ Sentences_ZFC
  intro Dom m v hmodel _
  let H := axioms_of_zfc_model v hmodel
  apply (seal_valid (mem := m) _).mpr ?_ v
  intro ee _ z z' h
  exact evalRel_unique H (ee ∘ coordinates) e
    ((evalForm_spec H e _ _ _).mp h.1) ((evalForm_spec H e _ _ _).mp h.2)

end DiophantineConsistency.ObjectNaturalExpression
