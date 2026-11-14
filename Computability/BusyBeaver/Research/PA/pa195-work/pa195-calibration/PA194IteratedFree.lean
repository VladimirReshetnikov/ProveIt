import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1
import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.EquationalTheory
set_option autoImplicit false
set_option maxHeartbeats 1000000
/-! A model-length certified sequence of Foundation universal openings
preserves internal PA provability. -/
namespace PA194IteratedFree
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma free_of_all {p : V} (hp : IsSemiformula ℒₒᵣ 1 p)
    (h : Provable (𝗣𝗔 : ArithmeticTheory) (^∀ p)) :
    Provable (𝗣𝗔 : ArithmeticTheory) (free ℒₒᵣ p) := by
  let φ : Bootstrapping.Semiformula V ℒₒᵣ 1 := ⟨p,by simpa using hp⟩
  have ha : (𝗣𝗔 : ArithmeticTheory).internalize V ⊢ ∀⁰ φ := (tprovable_iff_provable).mpr h
  have hshift : (𝗣𝗔 : ArithmeticTheory).internalize V ⊢ ∀⁰ φ.shift := by simpa using TProof.shift! ha
  have hf : (𝗣𝗔 : ArithmeticTheory).internalize V ⊢ φ.free := by
    simpa [Bootstrapping.Semiformula.free] using
      TProof.specialize! hshift (Bootstrapping.Semiterm.fvar 0)
  exact (tprovable_iff_provable).mp hf

lemma free_history_sound (lines : V)
    (hseed : Provable (𝗣𝗔 : ArithmeticTheory) lines.[0])
    (hstep : ∀ i, i+1 < len lines → ∃ p, IsSemiformula ℒₒᵣ 1 p ∧
      lines.[i] = ^∀ p ∧ lines.[i+1] = free ℒₒᵣ p) :
    ∀ i < len lines, Provable (𝗣𝗔 : ArithmeticTheory) lines.[i] := by
  have hdef : 𝚺₁-Predicate (fun n : V => ∀ i < n, i < len lines → Provable (𝗣𝗔 : ArithmeticTheory) lines.[i]) := by
    definability
  have hall : ∀ n : V, ∀ i < n, i < len lines → Provable (𝗣𝗔 : ArithmeticTheory) lines.[i] := by
    intro n
    induction n using ISigma1.sigma1_succ_induction
    · exact hdef
    case zero => intro i hi; exact False.elim (not_lt_zero hi)
    case succ n ih =>
      intro i hi hil
      by_cases hlt : i < n
      · exact ih i hlt hil
      · have hieq : i = n := le_antisymm (lt_succ_iff_le.mp hi) (le_of_not_gt hlt)
        subst i
        rcases zero_or_succ n with (rfl | ⟨j,rfl⟩)
        · exact hseed
        · rcases hstep j hil with ⟨p,hp,hprev,hout⟩
          have hj : j < j+1 := lt_add_one j
          have hjlen : j < len lines := lt_trans hj hil
          have hprevproof := ih j hj hjlen
          rw [hprev] at hprevproof
          rw [hout]
          exact free_of_all hp hprevproof
  intro i hi
  exact hall (len lines) i hi hi
#print axioms free_of_all
#print axioms free_history_sound
end PA194IteratedFree
