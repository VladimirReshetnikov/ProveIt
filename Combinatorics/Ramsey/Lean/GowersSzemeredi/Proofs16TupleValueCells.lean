import GowersSzemeredi.Proofs16TupleValueCompression
import GowersSzemeredi.Proofs16EvenModelCells
import Mathlib.Data.Nat.Log

/-! A logarithmic set of characters and one popular value cell force
all balanced 16-tuple maps to vanish at a prescribed common point. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- A cell for every character retains at least `40^(-m)` of the columns.
The factor 40 is five cells per pair in a balanced 16-tuple. -/
theorem exists_tuple_zero_value_cell {N M : Nat} [NeZero N] [Fact N.Prime]
    (h7 : 7 ≤ N) (V : Finset (ZMod N)) (f : ZMod N → ZMod N)
    (hvalues : ((columnAnchorFibre V 15 0).image
      (fun a => columnAnchorEval f (columnAnchorList a))).card ≤ M) :
    ∃ (Gamma U : Finset (ZMod N)), Gamma.card ≤ Nat.clog 2 (M+1) ∧ U ⊆ V ∧
      (V.card : Real)/(40 : Real)^(Nat.clog 2 (M+1)) ≤ (U.card : Real) ∧
      ∀ a ∈ columnAnchorFibre U 15 0, columnAnchorEval f (columnAnchorList a) = 0 := by
  let D := ((columnAnchorFibre V 15 0).image (fun a => columnAnchorEval f (columnAnchorList a))).erase 0
  have hD : D.card < 2^(Nat.clog 2 (M+1)) := by
    have hd : D.card ≤ M := (Finset.card_erase_le).trans hvalues
    exact (Nat.lt_succ_of_le hd).trans_le (Nat.le_pow_clog (by norm_num) (M+1))
  obtain ⟨Gamma, hGamma, hsep⟩ := separating_frequencies h7 (Nat.clog 2 (M+1)) D
    (Finset.notMem_erase 0 _) hD
  let cell : ZMod N → (Gamma → Fin 40) := fun x gamma => dirichletCell 40 ((gamma : ZMod N)*f x)
  have hcard : Fintype.card (Gamma → Fin 40) = 40^Gamma.card := by simp
  have hden : (0 : Real) < (40 : Real)^Gamma.card := by positivity
  obtain ⟨s, _, hs⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s := V) (t := (Finset.univ : Finset (Gamma → Fin 40))) (f := cell)
    (b := (V.card : Real)/(40 : Real)^Gamma.card) (fun _ _ => Finset.mem_univ _)
    Finset.univ_nonempty (by
      rw [Finset.card_univ, hcard, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      rw [mul_div_cancel₀ _ hden.ne'])
  let U := V.filter fun x => cell x = s
  refine ⟨Gamma, U, hGamma, Finset.filter_subset _ _, ?_, ?_⟩
  · have hpow : (40 : Real)^Gamma.card ≤ (40 : Real)^(Nat.clog 2 (M+1)) :=
      pow_le_pow_right₀ (by norm_num) hGamma
    exact (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hden hpow).trans hs
  · intro a ha
    by_contra hv
    have haV : a ∈ columnAnchorFibre V 15 0 := columnAnchorFibre_mono (Finset.filter_subset _ _) 0 ha
    have hvD : columnAnchorEval f (columnAnchorList a) ∈ D :=
      Finset.mem_erase.mpr ⟨hv, Finset.mem_image_of_mem _ haV⟩
    obtain ⟨gamma, hg, hgamma⟩ := hsep _ hvD
    have hcells : ∀ x ∈ columnAnchorList a, dirichletCell 40 (gamma*f x) = s ⟨gamma, hg⟩ := by
      intro x hx
      have hxU := (Finset.mem_filter.mp ha).2.1 x hx
      exact congrFun (Finset.mem_filter.mp hxU).2 ⟨gamma, hg⟩
    exact same_cell_even_not_separates (k := 8) gamma f (s ⟨gamma, hg⟩)
      (columnAnchorList a) (by rw [columnAnchorList_length]) hcells hgamma

end LeanProofs.GowersSzemeredi
