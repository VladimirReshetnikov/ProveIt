import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRAExtWitnessBound
import DiophantineConsistency.PRABndRewriting
/-! Transfer the extDef local bound through arbitrary substitutions, including
    the exact first initial occurrence in exponentialDef. The remainder of
    exponentialDef is not bounded here. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRAExtRewritingBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRAExtWitnessBound DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

theorem ext_rew_bound {n : ℕ} (ω : Rew ℒₒᵣ Empty 3 Empty n) (e : Fin n → V) :
    (ω ▹ extDef.val).Evalb e →
      (bnd (ω ▹ extDef.val)).Evalb (Fin.snoc e (((ω #2).val e Empty.elim)+1)) := by
  intro h
  let g : Fin 3 → V := fun i => (ω #i).val e Empty.elim
  have hf : (Semiterm.val e Empty.elim ∘ ω ∘ Semiterm.fvar) =
      (Empty.elim : Empty → V) := Subsingleton.elim _ _
  have hg : (Semiterm.val e Empty.elim ∘ ω ∘ Semiterm.bvar) = g := rfl
  simp only [Semiformula.eval_rew] at h
  rw [hg,hf] at h
  have hv : ![g 0,g 1,g 2] = g := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun j => ?_) j
    exact Fin.cases rfl (fun j => Fin.elim0 j) j
  have hs : Fin.snoc g (g 2+1) = ![g 0,g 1,g 2,g 2+1] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun j => ?_) j
    refine Fin.cases rfl (fun j => ?_) j
    exact Fin.cases rfl (fun j => Fin.elim0 j) j
  have hb := ext_bound (g 0) (g 1) (g 2) (by simpa [hv] using h)
  have hn := PRABndRewriting.natural extDef.val ω e (g 2+1)
  rw [hs] at hn
  exact hn.mpr hb
def initialX : ArithmeticSemisentence 1 := “X. !extDef 1 4 X”

theorem initialX_bound (X : V) (h : initialX.Evalb ![X]) :
    (bnd initialX).Evalb ![X,X+1] := by
  let ω : Rew ℒₒᵣ Empty 3 Empty 1 := Rew.subst ![Semiterm.numeral 1,Semiterm.numeral 4,#0]
  have h0 : (ω ▹ extDef.val).Evalb ![X] := by exact h
  have hb := ext_rew_bound ω ![X] h0
  exact hb
def boundedInitialX : ArithmeticSemisentence 2 := bnd initialX

def initialXBoundBody : ArithmeticSemisentence 1 := “X. !initialX X → !boundedInitialX X (X+1)”

theorem initialXBoundBody_model (e : Fin 1 → V) : initialXBoundBody.Eval e Empty.elim := by
  simp [initialXBoundBody, boundedInitialX, Semiformula.eval_substs]
  exact initialX_bound (e 0)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing

def initialXBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding initialXBoundBody

theorem candidate_proves_initialX_bound : PRA ⊢ initialXBoundSentence := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact initialXBoundBody_model e
end DiophantineConsistency.PRAExtRewritingBound
