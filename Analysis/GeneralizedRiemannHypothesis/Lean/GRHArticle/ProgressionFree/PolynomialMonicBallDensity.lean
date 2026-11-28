import GRHArticle.ProgressionFree.PolynomialPrimePowerDensity
import GRHArticle.ProgressionFree.PolynomialRoughWeightLimit

/-!
# From monic degree-layer limits to polynomial ball density

Each monic polynomial contributes once for every nonzero leading scalar.
The normalized ball count is the geometric average of the exact-degree
monic proportions and has the same limit.
-/

namespace GRHArticle.ProgressionFree

open Polynomial Filter Topology
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F]

/-- All nonzero scalar multiples of the monic members of a polynomial family. -/
def polynomialScalarClosure (B : Set F[X]) : Set F[X] :=
  {f | ∃ g ∈ B, g.Monic ∧ ∃ a : F, a ≠ 0 ∧ f = C a * g}

theorem card_polynomialDegreeLTFinset_scalarClosure (B : Set F[X]) (N : ℕ) :
    ((polynomialDegreeLTFinset F (N+1)).filter (· ∈ polynomialScalarClosure B)).card =
      (Fintype.card F - 1) * ∑ t ∈ Finset.range (N+1), (monicFamilyLayer B (N-t)).card := by
  let E := (Finset.range (N+1)).sigma fun t ↦
    (Finset.univ.erase (0:F)) ×ˢ monicFamilyLayer B (N-t)
  have hcard : E.card =
      ((polynomialDegreeLTFinset F (N+1)).filter (· ∈ polynomialScalarClosure B)).card := by
    apply Finset.card_bij (fun s _ ↦ C s.2.1 * s.2.2)
    · rintro ⟨t,a,g⟩ h
      obtain ⟨ht,hag⟩ := Finset.mem_sigma.mp h
      obtain ⟨ha,hg⟩ := Finset.mem_product.mp hag
      have ha₀ : a ≠ 0 := (Finset.mem_erase.mp ha).1
      obtain ⟨hm,hd,hB⟩ := mem_monicFamilyLayer.mp hg
      refine Finset.mem_filter.mpr ⟨mem_polynomialDegreeLTFinset.mpr ?_, g,hB,hm,a,ha₀,rfl⟩
      rw [degree_eq_natDegree (mul_ne_zero (C_ne_zero.mpr ha₀) hm.ne_zero),
        natDegree_C_mul ha₀, hd, Nat.cast_lt]
      omega
    · rintro ⟨t,a,g⟩ h ⟨s,b,k⟩ h' he
      obtain ⟨ht,hag⟩ := Finset.mem_sigma.mp h
      obtain ⟨hs,hbk⟩ := Finset.mem_sigma.mp h'
      obtain ⟨ha,hg⟩ := Finset.mem_product.mp hag
      obtain ⟨_,hk⟩ := Finset.mem_product.mp hbk
      obtain ⟨hm,hd,_⟩ := mem_monicFamilyLayer.mp hg
      obtain ⟨hm',hd',_⟩ := mem_monicFamilyLayer.mp hk
      have hcoeff := congrArg leadingCoeff he
      change (C a*g).leadingCoeff = (C b*k).leadingCoeff at hcoeff
      rw [hm.leadingCoeff_C_mul, hm'.leadingCoeff_C_mul] at hcoeff
      subst b
      have hEq : g = k := mul_left_cancel₀ (C_ne_zero.mpr (Finset.mem_erase.mp ha).1) he
      subst k
      have htn := Finset.mem_range.mp ht
      have hsn := Finset.mem_range.mp hs
      change t < N+1 at htn
      change s < N+1 at hsn
      change g.natDegree = N-t at hd
      change g.natDegree = N-s at hd'
      obtain rfl : t = s := by omega
      rfl
    · rintro f hf
      obtain ⟨hn,g,hg,hm,a,ha,rfl⟩ := Finset.mem_filter.mp hf
      have hd := mem_polynomialDegreeLTFinset.mp hn
      rw [degree_eq_natDegree (mul_ne_zero (C_ne_zero.mpr ha) hm.ne_zero),
        natDegree_C_mul ha, Nat.cast_lt] at hd
      refine ⟨⟨N-g.natDegree,a,g⟩, Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr
        (show N-g.natDegree < N+1 by omega), Finset.mem_product.mpr ⟨by simpa,
        mem_monicFamilyLayer.mpr ⟨hm, ?_, hg⟩⟩⟩, rfl⟩
      change g.natDegree = N-(N-g.natDegree)
      omega
  rw [← hcard]
  simp [E, Finset.card_sigma, Finset.card_product, Finset.mul_sum]

/-- Exact degree-layer density and ball density coincide for scalar closures. -/
theorem tendsto_polynomialBallProportion_scalarClosure {B : Set F[X]} {c : ℝ}
    (hB : Tendsto (monicFamilyProportion B) atTop (𝓝 c)) :
    Tendsto (polynomialBallProportion (polynomialScalarClosure B)) atTop (𝓝 c) := by
  let q : ℝ := Fintype.card F
  let z := q⁻¹
  have hq : 1 < q := by dsimp [q]; exact_mod_cast Fintype.one_lt_card
  have hz : 0 ≤ z := inv_nonneg.mpr (by linarith)
  have hz' : z < 1 := inv_lt_one_of_one_lt₀ hq
  have hconv := tendsto_weighted_rough_convolution (z^·) (summable_geometric_of_lt_one hz hz')
    (pow_nonneg hz) (monicFamilyProportion_mem_unitInterval B) hB
  have he : (1-z) * (c * ∑' t : ℕ, z^t) = c := by
    rw [tsum_geometric_of_lt_one hz hz']
    field_simp [ne_of_gt (sub_pos.mpr hz')]
  rw [← he]
  refine (tendsto_const_nhds.mul hconv).congr fun N ↦ ?_
  unfold polynomialBallProportion
  rw [card_polynomialDegreeLTFinset_scalarClosure]
  simpa [monicFamilyProportion, z, q] using (polynomial_weighted_convolution_scale F N
    (fun n ↦ (monicFamilyLayer B n).card) (fun _ ↦ 1)).symm

end GRHArticle.ProgressionFree
