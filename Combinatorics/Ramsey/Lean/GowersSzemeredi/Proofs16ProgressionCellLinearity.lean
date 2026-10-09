import GowersSzemeredi.Proofs16ProgressionCoordinateCells
import GowersSzemeredi.Proofs16GapCoordinates

/-! Order-two Freiman maps on a translated proper progression preserve
eight-term relations within coordinate cells. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open OAI.Erdos3.BohrProgression

theorem translated_progression_coordinate_affine {N : Nat} [NeZero N]
    (P : CyclicCenteredGAP N) (t : ZMod N) (f : ZMod N → ZMod N)
    (hf : FreimanHom 2 (translatedFreimanDomain P.carrier t) f) :
    ∃ (b : ZMod N) (l : Fin P.rank → ZMod N),
      ∀ u : P.Param, f (t+P.eval u) = b+∑ i, ((u i : Nat) : ZMod N)*l i := by
  let a : ZMod N := t-∑ i, (P.radius i : ZMod N)*P.step i
  have he (u : P.Param) : gapPoint a P.step (fun i => (u i : Nat)) = t+P.eval u := by
    simp only [gapPoint,a,CyclicCenteredGAP.eval,CyclicCenteredGAP.coeff,
      Int.cast_sub,Int.cast_natCast,sub_mul,Finset.sum_sub_distrib]
    ring
  have hmem (n : Fin P.rank → Nat) (hn : ∀ i, n i < 2*P.radius i+1) :
      gapPoint a P.step n ∈ translatedFreimanDomain P.carrier t := by
    let u : P.Param := fun i => ⟨n i,hn i⟩
    rw [show gapPoint a P.step n = t+P.eval u from he u]
    exact Finset.mem_image.mpr ⟨P.eval u,Finset.mem_image.mpr ⟨u,Finset.mem_univ _,rfl⟩,rfl⟩
  refine ⟨f a,fun i => f (a+P.step i)-f a,?_⟩
  intro u
  have h := freiman_linear_gap_affine (hf.isFreimanLinearOn (by omega)) a P.step
    (fun i => 2*P.radius i+1) (by intro i; omega) hmem (fun i => (u i : Nat)) (fun i => (u i).isLt)
  simpa only [he u] using h

theorem progression_cell_eight_sum {N : Nat} [NeZero N]
    (P : CyclicCenteredGAP N) (hP : P.Proper) (t : ZMod N) (f : ZMod N → ZMod N)
    (hf : FreimanHom 2 (translatedFreimanDomain P.carrier t) f)
    (u v : Fin 8 → P.Param)
    (hcell : ∀ j, progressionCellCode P (u j) = progressionCellCode P (v j))
    (he : ∑ j, (t+P.eval (u j)) = ∑ j, (t+P.eval (v j))) :
    ∑ j, f (t+P.eval (u j)) = ∑ j, f (t+P.eval (v j)) := by
  have he' : ∑ j, P.eval (u j) = ∑ j, P.eval (v j) := by
    simpa only [Finset.sum_add_distrib,add_right_inj] using he
  have hcoords := progression_cell_relation_lifts P hP u v hcell he'
  obtain ⟨b,l,haffine⟩ := translated_progression_coordinate_affine P t f hf
  simp_rw [haffine]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm,Finset.sum_comm (f := fun j i => ((v j i : Nat) : ZMod N)*l i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_mul,← Finset.sum_mul]
  congr 1
  have h := congrArg (fun n : Int => (n : ZMod N)) (hcoords i)
  simpa only [Int.cast_sum,Int.cast_natCast] using h

end LeanProofs.GowersSzemeredi
