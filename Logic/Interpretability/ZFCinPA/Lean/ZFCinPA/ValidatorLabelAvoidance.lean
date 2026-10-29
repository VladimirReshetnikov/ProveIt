import ZFCinPA.ValidatorEnvironmentLabels254

set_option autoImplicit false
noncomputable section

/-! Syntax-only label avoidance shared by the C222 and C254 encoders. -/
namespace LeanProofs.ZFCinPA.ValidatorLabelAvoidance
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC.ArithmeticCode254
open ValidatorEnvironmentLabels254
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Avoid every stored label; all indices and the vector length are internal. -/
def Avoid (z env : V) : Prop := ∀ i<len env, z≠env.[i]
/-- The finite free vector has the additional fallback label 1. -/
def FreeAvoid (z env : V) : Prop := z≠1 ∧ Avoid z env
/-- Avoid all labels that the encoder may allocate below a binder. -/
def StreamAvoid (z fresh : V) : Prop := ∀ k : V, z≠fresh+2*k

lemma avoid_nil (z : V) : Avoid z (0 : V) := by simp [Avoid]
lemma avoid_cons {z env x : V} (he : Avoid z env) (hx : z≠x) : Avoid z (x∷env) := by
  intro i hi
  rcases zero_or_succ i with (rfl | ⟨i,rfl⟩)
  · simpa using hx
  · simpa using he i (by simpa using hi)
lemma free_label_avoids {z env : V} (he : FreeAvoid z env) (i : V) :
    z≠freeLabel env i := by
  classical
  by_cases hi : i<len env
  · simpa [freeLabel,hi] using he.2 i hi
  · simpa [freeLabel,hi] using he.1
lemma stream_head {z fresh : V} (h : StreamAvoid z fresh) : z≠fresh := by
  simpa using h 0
lemma stream_next {z fresh : V} (h : StreamAvoid z fresh) : StreamAvoid z (fresh+2) := by
  intro k
  rw [show (fresh+2)+2*k=fresh+2*(k+1) by ring]
  exact h (k+1)
lemma stream_of_lt {z fresh : V} (h : z<fresh) : StreamAvoid z fresh := by
  intro k
  exact ne_of_lt (lt_of_lt_of_le h (le_add_of_nonneg_right (Arithmetic.zero_le _)))

lemma term_label_avoids {n t : V} (ht : IsSemiterm ℒₛₑₜ n t)
    (F B z : V) (hlen : len B=n) (hF : FreeAvoid z F) (hB : Avoid z B) :
    z≠TermLabels.term F B t := by
  rcases ht.case with (⟨i,hi,rfl⟩ | ⟨i,rfl⟩ | ⟨k,f,args,hf,_,rfl⟩)
  · rw [TermLabels.term_bvar]
    exact hB i (by rwa [hlen])
  · rw [TermLabels.term_fvar]
    exact free_label_avoids hF i
  · have hf' : V ⊧/![k,f] (LeanProofs.ZFCinPA.instLORDefinableSet.func).val := hf
    rw [show (LeanProofs.ZFCinPA.instLORDefinableSet.func : 𝚺₀.Semisentence 2) =
      .mkSigma “k f. ⊥” from rfl] at hf'
    simp at hf'

end LeanProofs.ZFCinPA.ValidatorLabelAvoidance
