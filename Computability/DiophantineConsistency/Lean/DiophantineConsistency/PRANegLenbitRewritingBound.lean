import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRANegLenbitWitnessBound
import DiophantineConsistency.PRABndRewriting
/-! Bound the rewritten negative lenbit graph, including the first
    concrete occurrence in Foundation sppow2Def. This is a local result. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRANegLenbitRewritingBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRANegLenbitWitnessBound DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
theorem neg_lenbit_rew_bound {n : ℕ} (ω : Rew ℒₒᵣ Empty 2 Empty n) (e : Fin n → V) :
    (ω ▹ (∼lenbitDef.val)).Evalb e →
      (bnd (ω ▹ (∼lenbitDef.val))).Evalb (Fin.snoc e (((ω #1).val e Empty.elim)+1)) := by
  intro h
  let g : Fin 2 → V := fun i => (ω #i).val e Empty.elim
  have hf : (Semiterm.val e Empty.elim ∘ ω ∘ Semiterm.fvar) =
      (Empty.elim : Empty → V) := Subsingleton.elim _ _
  have hg : (Semiterm.val e Empty.elim ∘ ω ∘ Semiterm.bvar) = g := rfl
  simp only [Semiformula.eval_rew] at h
  rw [hg,hf] at h
  have hv : ![g 0,g 1] = g := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun j => Fin.elim0 j) j
  have hs : Fin.snoc g (g 1+1) = ![g 0,g 1,g 1+1] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun j => ?_) j
    exact Fin.cases rfl (fun j => Fin.elim0 j) j
  have hb := neg_lenbit_bound (g 0) (g 1) (by simpa [hv] using h)
  have hn := PRABndRewriting.natural (∼lenbitDef.val) ω e (g 1+1)
  rw [hs] at hn
  exact hn.mpr hb

def negFirst : ArithmeticSemisentence 1 := “m. ¬!lenbitDef 1 m”
theorem negFirst_bound (m : V) (h : negFirst.Evalb ![m]) :
    (bnd negFirst).Evalb ![m,m+1] := by
  let ω : Rew ℒₒᵣ Empty 2 Empty 1 := Rew.subst ![Semiterm.numeral 1,#0]
  have h0 : (ω ▹ (∼lenbitDef.val)).Evalb ![m] := by exact h
  have hb := neg_lenbit_rew_bound ω ![m] h0
  exact hb
def boundedNegFirst : ArithmeticSemisentence 2 := bnd negFirst

def negFirstBoundBody : ArithmeticSemisentence 1 := “m. !negFirst m → !boundedNegFirst m (m+1)”

theorem negFirstBoundBody_model (e : Fin 1 → V) : negFirstBoundBody.Eval e Empty.elim := by
  simp [negFirstBoundBody, boundedNegFirst, Semiformula.eval_substs]
  exact negFirst_bound (e 0)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing

def negFirstBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding negFirstBoundBody

theorem candidate_proves_negFirst_bound : PRA ⊢ negFirstBoundSentence := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact negFirstBoundBody_model e
end DiophantineConsistency.PRANegLenbitRewritingBound
