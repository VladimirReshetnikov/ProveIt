import DiophantineConsistency.PRAWitnessCalculus

/-! Existential witnesses in a fixed closed sentence can be chosen in the
metatheory of each model. This does not bound witnesses below universal
quantifiers in their matrix. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAWitnessClosedExistential
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open StrictSigmaOneInduction PRAWitnessCalculus

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

/-- A closed existential inherits witness bounds from its matrix. -/
theorem wb_exs_sentence {ψ : ArithmeticSemisentence 1} (hψ : WB M ψ) :
    WB M (∃⁰ ψ) := by
  classical
  by_cases h : ∃ x : M, ψ.Eval ![x] Empty.elim
  · obtain ⟨x, hx⟩ := h
    refine wb_exs (fun _ => x) (mono_const x) ?_ hψ
    intro e _
    refine ⟨x, le_rfl, ?_⟩
    have he : (x :> e) = ![x] := by
      funext i
      exact Fin.cases rfl (fun j => Fin.elim0 j) i
    simpa only [he] using hx
  · refine wb_exs (fun _ => 0) (mono_const 0) ?_ hψ
    intro e ⟨x, hx⟩
    exfalso
    apply h
    refine ⟨x, ?_⟩
    have he : (x :> e) = ![x] := by
      funext i
      exact Fin.cases rfl (fun j => Fin.elim0 j) i
    simpa only [he] using hx

/-- Two leading existential witnesses of a closed sentence may be selected
jointly. Only the matrix needs a uniform witness bound. -/
theorem wb_exs_exs_sentence {ψ : ArithmeticSemisentence 2} (hψ : WB M ψ) :
    WB M (∃⁰ ∃⁰ ψ) := by
  classical
  obtain ⟨B, hB, hb⟩ := hψ
  by_cases h : ∃ x y : M, ψ.Eval ![y,x] Empty.elim
  · obtain ⟨x,y,hxy⟩ := h
    let w := x + y + 1 + B ![y,x]
    refine ⟨fun _ => w, mono_const w, ?_⟩
    intro e _
    have he : e = ![] := Subsingleton.elim _ _
    subst e
    simp only [bnd, Semiformula.eval_bexs]
    refine ⟨x, ?_, y, ?_, ?_⟩
    · simpa [w, val_lastVar] using
        (lt_of_lt_of_le (lt_succ_iff_le.mpr (show x ≤ x+y by simp))
          (show x+y+1 ≤ x+y+1+B ![y,x] by simp))
    · simpa [w, val_lastVar] using
        (lt_of_lt_of_le (lt_succ_iff_le.mpr (show y ≤ x+y by simp))
          (show x+y+1 ≤ x+y+1+B ![y,x] by simp))
    · rw [cons_snoc, cons_snoc]
      have hbound : B ![y,x] ≤ w := by simp [w]
      simpa using eval_bnd_mono ψ ![y,x] Empty.elim hbound (hb ![y,x] hxy)
  · refine ⟨fun _ => 0, mono_const 0, ?_⟩
    intro e he
    have he' : e = ![] := Subsingleton.elim _ _
    subst e
    simp only [Semiformula.eval_ex] at he
    exact False.elim (h (by simpa using he))

end DiophantineConsistency.PRAWitnessClosedExistential
