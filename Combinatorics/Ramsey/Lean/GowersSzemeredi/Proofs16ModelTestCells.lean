import GowersSzemeredi.Proofs16ModelTestSelection
import Mathlib.Combinatorics.Pigeonhole

/-! A single ten-cell refinement excludes every model detected by the
chosen test from all four-term column relations in the retained core. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem same_cell_quad_not_separates {N : Nat} [NeZero N]
    (gamma a b c d : ZMod N)
    (hab : dirichletCell 10 (gamma*a) = dirichletCell 10 (gamma*b))
    (hcd : dirichletCell 10 (gamma*c) = dirichletCell 10 (gamma*d)) :
    ¬ Separates gamma (a-b+c-d) := by
  have h1 := dirichletCell_close hab
  have h2 := dirichletCell_close hcd
  have he : gamma*(a-b+c-d) = (gamma*a-gamma*b)+(gamma*c-gamma*d) := by ring
  have h3 := centeredAbs_add_le (gamma*a-gamma*b) (gamma*c-gamma*d)
  unfold Separates
  rw [he]
  omega

/-- Refine the valid columns into ten cells; the detected models cannot
occur as any four-term map value in the resulting dense subcore. -/
theorem exists_model_test_cell {J : Type*} {N g d : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N)) (I : Finset J) (Gamma : Finset (ZMod N))
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (f : J → ZMod N → ZMod N) {rho r : Real}
    (hrho : 0 < rho) (hr : 0 < r) (hrle : r ≤ rho)
    (hA : A.Nonempty) (hI : I.Nonempty) (hGamma : Gamma.card ≤ g)
    (hT : ∀ x ∈ A, (T x).card ≤ d)
    (hf : ∀ j ∈ I, IsFreimanLinearOn (bohr Gamma rho) (f j))
    (hf0 : ∀ j ∈ I, f j 0 = 0)
    (hne : ∀ j ∈ I, ∃ y ∈ bohr Gamma (refinementKernelRadius g d rho (r/2)), f j y ≠ 0)
    (hN : refinementKernelCap g d rho (r/2) < N) (h7 : 7 ≤ N) :
    ∃ (P : Finset (ZMod N)) (y gamma : ZMod N), P ⊆ A ∧
      modelTestDensity g d r/10*A.card ≤ (P.card : Real) ∧
      y ∈ bohr Gamma r ∧ (∀ x ∈ P, y ∈ bohr (T x) r) ∧
      modelTestDensity g d r*I.card ≤ ((I.filter (fun j => Separates gamma (f j y))).card : Real) ∧
      ∀ a ∈ P, ∀ b ∈ P, ∀ c ∈ P, ∀ e ∈ P, ∀ j ∈ I,
        Separates gamma (f j y) → L a y-L b y+L c y-L e y ≠ f j y := by
  classical
  obtain ⟨y,gamma,hy,hAcount,hIcount⟩ := exists_model_test A I Gamma T f hrho hr hrle hA hI hGamma hT hf hf0 hne hN h7
  let S := A.filter (fun x => y ∈ bohr (T x) r)
  let cell := fun x => dirichletCell 10 (gamma*L x y)
  obtain ⟨t,_,ht⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s := S) (t := (Finset.univ : Finset (Fin 10))) (f := cell) (b := (S.card : Real)/10)
    (fun _ _ => Finset.mem_univ _) Finset.univ_nonempty (by norm_num; linarith)
  let P := S.filter (fun x => cell x = t)
  have hP : modelTestDensity g d r/10*A.card ≤ (P.card : Real) := by
    have h := div_le_div_of_nonneg_right hAcount (by norm_num : (0 : Real) ≤ 10)
    change (S.card : Real)/10 ≤ (P.card : Real) at ht
    nlinarith only [h,ht]
  refine ⟨P,y,gamma,?_,hP,hy,?_,hIcount,?_⟩
  · intro x hx
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
  · intro x hx
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
  · intro a ha b hb c hc e he j _ hsep heq
    have hab := (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
    have hce := (Finset.mem_filter.mp hc).2.trans (Finset.mem_filter.mp he).2.symm
    have hn := same_cell_quad_not_separates gamma (L a y) (L b y) (L c y) (L e y) hab hce
    exact hn (heq.symm ▸ hsep)

end LeanProofs.GowersSzemeredi
