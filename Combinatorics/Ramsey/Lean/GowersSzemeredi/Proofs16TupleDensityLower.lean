import GowersSzemeredi.Proofs16AffineTupleRows
import GowersSzemeredi.Proofs16BoxDensityLower
import GowersSzemeredi.Proofs16TupleBohrQuasirandom

/-! Positive density for tuple Bohr graphs, uniformly in the parameter
Bohr domain. A smaller common Bohr set lies in every vertex degree. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Every degree has relative density at least Q^(-r) in the fixed base. -/
theorem tuple_bohr_degree_lower {N Q : Nat} [NeZero N] [NeZero Q]
    {κ : Type*} [Fintype κ] (F : Finset (ZMod N)) (L : κ → ZMod N → ZMod N)
    (y : ZMod N) (r : Nat) {rho nu : Real} (hnu : nu ≤ rho) (hQ : 1 ≤ nu * Q)
    (hr : F.card + Fintype.card κ ≤ r) :
    (1 / (Q : Real)^r) * (bohr F rho).card ≤
      ((bohr F rho ∩ bohr (Finset.univ.image fun j => L j y) nu).card : Real) := by
  let K := F ∪ Finset.univ.image (fun j => L j y)
  have hcard : K.card ≤ r := (affine_fixed_frequencies_card_le F (fun j => L j y)).trans hr
  have hsub : bohr K nu ⊆ bohr F rho ∩ bohr (Finset.univ.image fun j => L j y) nu := by
    rw [show K = F ∪ Finset.univ.image (fun j => L j y) from rfl, bohr_union]
    intro x hx
    exact Finset.mem_inter.mpr ⟨bohr_mono_radius F hnu (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx).2⟩
  have hQpos : (0 : Real) < Q := by exact_mod_cast NeZero.pos Q
  have hlow : (N : Real) ≤ (Q : Real)^K.card * (bohr K nu).card := by
    exact_mod_cast bohr_card_lower K Q hQ
  have hp : (Q : Real)^K.card ≤ (Q : Real)^r := by
    exact_mod_cast Nat.pow_le_pow_right (NeZero.pos Q) hcard
  have hsize : ((bohr K nu).card : Real) ≤ (bohr F rho ∩ bohr (Finset.univ.image fun j => L j y) nu).card :=
    Nat.cast_le.mpr (Finset.card_le_card hsub)
  have hN : ((bohr F rho).card : Real) ≤ N := by
    exact_mod_cast (show (bohr F rho).card ≤ N by simpa using Finset.card_le_univ (bohr F rho))
  rw [one_div_mul_eq_div]
  apply (div_le_iff₀ (by positivity)).mpr
  calc
    ((bohr F rho).card : Real) ≤ N := hN
    _ ≤ (Q : Real)^K.card * (bohr K nu).card := hlow
    _ ≤ (Q : Real)^r * (bohr F rho ∩ bohr (Finset.univ.image fun j => L j y) nu).card :=
      mul_le_mul hp hsize (by positivity) (by positivity)
    _ = _ := by ring

/-- The approximating density inherits the explicit degree lower bound. -/
theorem tuple_bohr_density_lower {N Q : Nat} [NeZero N] [NeZero Q]
    {κ : Type*} [Fintype κ] (F C : Finset (ZMod N)) (hC : C.Nonempty)
    (L : κ → ZMod N → ZMod N) (r : Nat) {rho nu delta epsilon : Real}
    (hrho : 0 ≤ rho) (hnu : nu ≤ rho) (hQ : 1 ≤ nu * Q)
    (hr : F.card + Fintype.card κ ≤ r) (heps : 0 ≤ epsilon)
    (hbox : boxSum (fun (x : ↥(bohr F rho)) (y : ↥C) =>
      (if (x : ZMod N) ∈ bohr (Finset.univ.image fun j => L j y) nu then (1 : Real) else 0) - delta) ≤
        epsilon^4 * ((bohr F rho).card : Real)^2 * (C.card : Real)^2) :
    1 / (Q : Real)^r - epsilon ≤ delta := by
  apply density_lower_of_box
    (fun (x : ↥(bohr F rho)) (y : ↥C) =>
      if (x : ZMod N) ∈ bohr (Finset.univ.image fun j => L j y) nu then (1 : Real) else 0)
    (by rw [Fintype.card_coe]; exact Finset.card_pos.mpr ⟨0, zero_mem_bohr F hrho⟩)
    (by rw [Fintype.card_coe]; exact hC.card_pos) heps
  · intro y
    rw [sum_subtype_indicator, Fintype.card_coe]
    exact tuple_bohr_degree_lower F L y r hnu hQ hr
  · simpa only [Fintype.card_coe] using hbox

end LeanProofs.GowersSzemeredi
