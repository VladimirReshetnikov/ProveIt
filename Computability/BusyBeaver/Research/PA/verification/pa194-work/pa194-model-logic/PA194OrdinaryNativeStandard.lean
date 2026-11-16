import PA194OrdinaryChosenMatrix
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194OrdinaryNativeConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRALanguage IPRANativeFormula
variable {L : Language} {M : Type} [s : Structure L M] {ξ : Type}
def evalNative (f : ξ → M) : {n : ℕ} → (Fin n → M) → Semiformulaᵢ L ξ n → Prop
  | _, _, .falsum => False
  | _, b, .rel r ts => s.rel r (fun i => (ts i).val b f)
  | _, b, .and p q => evalNative f b p ∧ evalNative f b q
  | _, b, .or p q => evalNative f b p ∨ evalNative f b q
  | _, b, .imp p q => evalNative f b p → evalNative f b q
  | _, b, .all p => ∀ x : M, evalNative f (x :> b) p
  | _, b, .exs p => ∃ x : M, evalNative f (x :> b) p

theorem eval_native (f : ξ → M) : ∀ {n : ℕ} (p : Semiformula L ξ n) (b : Fin n → M),
    evalNative f b (native p) ↔ Semiformula.EvalAux s f b p
  | _, .verum, _ => by simp [evalNative, native, Semiformula.EvalAux]
  | _, .falsum, _ => by simp [evalNative, native, Semiformula.EvalAux]
  | _, .rel r ts, _ => by rfl
  | _, .nrel r ts, _ => by rfl
  | _, .and p q, b => by simp [evalNative, native, Semiformula.EvalAux, eval_native f p b, eval_native f q b]
  | _, .or p q, b => by simp [evalNative, native, Semiformula.EvalAux, eval_native f p b, eval_native f q b]
  | _, .all p, b => by simp [evalNative, native, Semiformula.EvalAux, eval_native f p]
  | _, .exs p, b => by simp [evalNative, native, Semiformula.EvalAux, eval_native f p]
local instance : Structure language ℕ := natStructure
local instance : Structure.Eq language ℕ := ⟨fun _ _ => iff_of_eq rfl⟩

theorem nativeOrdinaryConsistency_standard :
    evalNative (M := ℕ) Empty.elim ![] nativeBoundedOrdinaryConsistency ↔
      Entailment.Consistent PA194PAeq.ordinaryPAeq := by
  change ¬evalNative Empty.elim ![] (native (∃⁰ ∼ordinaryMatrix)) ↔ _
  rw [eval_native]
  have h : ¬(Semiformula.EvalAux natStructure Empty.elim ![] (∃⁰ ∼ordinaryMatrix)) ↔
      (∀⁰ ordinaryMatrix).Evalb (M := ℕ) ![] := by
    change ¬(∃⁰ ∼ordinaryMatrix).Eval ![] Empty.elim ↔
      (∀⁰ ordinaryMatrix).Eval ![] Empty.elim
    simp [Semiformula.eval_ex, Semiformula.eval_all]
  exact h.trans ordinaryMatrix_standard
#print axioms eval_native
#print axioms nativeOrdinaryConsistency_standard
end PA194OrdinaryNativeConsistency
