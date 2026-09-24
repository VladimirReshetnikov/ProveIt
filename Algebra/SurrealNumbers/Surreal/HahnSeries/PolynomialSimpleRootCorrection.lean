import Surreal.HahnSeries.PolynomialSimpleRootLifting
import Surreal.HahnSeries.PolynomialFirstRootCorrection

/-!
# Supported simple roots and their first correction coefficient

This combines support-controlled simple-root lifting with the finite Taylor
coefficient identity in `polynomial:cor:simpleroot` and
`polynomial:eq:firstrootcorrection`. A positive common lower bound for the
input error supports is also a lower bound for every nonzero member of their
additive closure. Consequently the constructed correction satisfies the
first-coefficient formula at every such bound, in particular at the least
input error exponent. Cancellation and the identically zero error are allowed.
-/

namespace Surreal.HahnSeries

open Polynomial
open _root_.HahnSeries

noncomputable section

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ] [Field K]

omit [Field K] in
/-- A nonnegative lower bound for the generators bounds every nonzero
element of their additive closure. No Archimedean property is used. -/
theorem le_of_mem_additive_closure_ne_zero {S : Set Γ} (e : Γ) (he : 0 ≤ e)
    (hS : ∀ g ∈ S, e ≤ g) {g : Γ} (hg : g ∈ AddSubmonoid.closure S)
    (hg0 : g ≠ 0) : e ≤ g := by
  have h : g = 0 ∨ e ≤ g := by
    clear hg0
    induction hg using AddSubmonoid.closure_induction with
    | mem g hg => exact Or.inr (hS g hg)
    | zero => exact Or.inl rfl
    | add a b _ _ ha hb =>
      rcases ha with rfl | ha
      · simpa only [zero_add] using hb
      rcases hb with rfl | hb
      · simpa only [add_zero] using Or.inr ha
      exact Or.inr (ha.trans (le_add_of_nonneg_right (he.trans hb)))
  exact h.resolve_left hg0

/-- Support in the generated monoid with zero removed gives an actual
Hahn order lower bound. -/
theorem orderTop_ge_of_support_subset_additive_closure {S : Set Γ}
    (e : Γ) (he : 0 ≤ e) (hS : ∀ g ∈ S, e ≤ g)
    (η : K⟦Γ⟧) (hη : η.support ⊆ (AddSubmonoid.closure S : Set Γ) \ {0}) :
    (e : WithTop Γ) ≤ η.orderTop := by
  apply le_orderTop_iff_forall.mpr
  intro g hg
  by_contra hcoeff
  obtain ⟨hmem, hne⟩ := hη ((mem_support _ _).mpr hcoeff)
  have hge : e ≤ g := le_of_mem_additive_closure_ne_zero e he hS hmem
    (by simpa only [Set.mem_singleton_iff] using hne)
  exact (not_lt_of_ge (WithTop.coe_le_coe.mpr hge)) hg

/-- The input polynomial minus its constant residue, in the ambient Hahn field. -/
def residueErrorPolynomial (H : Polynomial (nonnegativeSubring Γ K)) : Polynomial K⟦Γ⟧ :=
  (H - (H.map (standardPart Γ K)).map constantNonnegative).map
    (nonnegativeSubring Γ K).subtype

@[simp] theorem coeff_residueErrorPolynomial
    (H : Polynomial (nonnegativeSubring Γ K)) (n : ℕ) :
    (residueErrorPolynomial H).coeff n =
      (H.coeff n : K⟦Γ⟧) - single 0 (standardPart Γ K (H.coeff n)) := by
  simp only [residueErrorPolynomial, Polynomial.coeff_map, Polynomial.coeff_sub]
  rfl

/-- The original ambient polynomial is its constant residue plus its error. -/
theorem map_eq_constant_residue_add_error (H : Polynomial (nonnegativeSubring Γ K)) :
    H.map (nonnegativeSubring Γ K).subtype =
      (H.map (standardPart Γ K)).map (_root_.HahnSeries.C : K →+* K⟦Γ⟧) +
        residueErrorPolynomial H := by
  have hc : (nonnegativeSubring Γ K).subtype.comp constantNonnegative =
      (_root_.HahnSeries.C : K →+* K⟦Γ⟧) := by
    ext a
    rfl
  have hconst : ((H.map (standardPart Γ K)).map constantNonnegative).map
      (nonnegativeSubring Γ K).subtype =
      (H.map (standardPart Γ K)).map (_root_.HahnSeries.C : K →+* K⟦Γ⟧) := by
    rw [Polynomial.map_map, hc]
  rw [residueErrorPolynomial, Polynomial.map_sub, hconst, add_sub_cancel]

/-- Every error coefficient is of positive order, including zero coefficients. -/
theorem orderTop_residueErrorPolynomial_coeff_pos
    (H : Polynomial (nonnegativeSubring Γ K)) (n : ℕ) :
    0 < ((residueErrorPolynomial H).coeff n).orderTop := by
  rw [coeff_residueErrorPolynomial]
  exact orderTop_sub_standardPart_pos (H.coeff n)

/-- The generated input support is exactly the support used by the finite
factor-lifting and simple-root theorems. -/
theorem residueErrorSupport_eq_closure_support_residueErrorPolynomial
    (H : Polynomial (nonnegativeSubring Γ K)) :
    residueErrorSupport H =
      AddSubmonoid.closure (⋃ n, ((residueErrorPolynomial H).coeff n).support) := by
  simp only [residueErrorSupport, residueErrorPolynomial, Polynomial.coeff_map]
  rfl

/-- The common order bound on the input errors transfers to every correction
whose support lies in the prescribed generated monoid with zero removed. -/
theorem orderTop_supported_correction_ge
    (H : Polynomial (nonnegativeSubring Γ K)) (η : K⟦Γ⟧)
    (hη : η.support ⊆ (residueErrorSupport H : Set Γ) \ {0})
    (e : Γ) (he : 0 ≤ e)
    (hE : ∀ n, (e : WithTop Γ) ≤ ((residueErrorPolynomial H).coeff n).orderTop) :
    (e : WithTop Γ) ≤ η.orderTop := by
  rw [residueErrorSupport_eq_closure_support_residueErrorPolynomial] at hη
  apply orderTop_ge_of_support_subset_additive_closure e he _ η hη
  intro g hg
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hg
  exact WithTop.coe_le_coe.mp
    ((hE n).trans (orderTop_le_of_coeff_ne_zero ((mem_support _ _).mp hn)))

/-- A nonzero Hahn polynomial has a least exponent among all its coefficient
supports: only finitely many polynomial coefficients can be nonzero. -/
theorem exists_least_coefficient_support (E : Polynomial K⟦Γ⟧) (hE : E ≠ 0) :
    ∃ e : Γ, IsLeast (⋃ n, (E.coeff n).support) e := by
  have hfin : (⋃ n ∈ E.support, (E.coeff n).support).IsWF :=
    E.support.isWF_bUnion.mpr (fun n _ => (E.coeff n).isWF_support)
  have hWF : (⋃ n, (E.coeff n).support).IsWF := hfin.mono <| by
    intro g hg
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hg
    have hn0 : E.coeff n ≠ 0 := ne_zero_of_coeff_ne_zero ((mem_support _ _).mp hn)
    exact Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr
      ⟨Polynomial.mem_support_iff.mpr hn0, hn⟩⟩
  have hne : (⋃ n, (E.coeff n).support).Nonempty := by
    obtain ⟨n, hn⟩ := Polynomial.support_nonempty.mpr hE
    obtain ⟨g, hg⟩ := _root_.HahnSeries.support_nonempty_iff.mpr
      (Polynomial.mem_support_iff.mp hn)
    exact ⟨g, Set.mem_iUnion.mpr ⟨n, hg⟩⟩
  exact ⟨hWF.min hne, hWF.min_mem hne, fun g hg => hWF.min_le hne hg⟩

/-- The complete supported simple-root lift, with its first-coefficient
formula at every positive common lower bound for the error orders.
Uniqueness already holds among all positive-order root corrections. -/
theorem existsUnique_supported_root_correction_with_coefficients
    (H : Polynomial (nonnegativeSubring Γ K)) (hH : H.Monic) (c : K)
    (hc : (H.map (standardPart Γ K)).IsRoot c)
    (hd : (H.map (standardPart Γ K)).derivative.eval c ≠ 0) :
    ∃! η : K⟦Γ⟧,
      (0 < η.orderTop ∧ (H.map (nonnegativeSubring Γ K).subtype).IsRoot (single 0 c + η)) ∧
      (η.support ⊆ (residueErrorSupport H : Set Γ) \ {0}) ∧
      ∀ e : Γ, 0 < e →
        (∀ n, (e : WithTop Γ) ≤ ((residueErrorPolynomial H).coeff n).orderTop) →
        η.coeff e = -((residueErrorPolynomial H).eval (single 0 c)).coeff e /
          (H.map (standardPart Γ K)).derivative.eval c := by
  obtain ⟨η, ⟨hη, hS⟩, huniq⟩ := existsUnique_supported_root_correction H hH c hc hd
  refine ⟨η, ⟨hη, hS, ?_⟩, ?_⟩
  · intro e he hE
    apply first_root_correction_coeff (H.map (standardPart Γ K)) c hc hd
      (residueErrorPolynomial H) e he hE η
      (orderTop_supported_correction_ge H η hS e he.le hE)
    rw [← map_eq_constant_residue_add_error]
    exact hη.2
  · intro ε hε
    exact huniq ε ⟨hε.1, hε.2.1⟩

/-- The exact least-error-exponent form of `polynomial:cor:simpleroot` and
`polynomial:eq:firstrootcorrection`. The least exponent's positivity and all
required order bounds follow from the error supports themselves. -/
theorem existsUnique_supported_root_correction_at_least_error_exponent
    (H : Polynomial (nonnegativeSubring Γ K)) (hH : H.Monic) (c : K)
    (hc : (H.map (standardPart Γ K)).IsRoot c)
    (hd : (H.map (standardPart Γ K)).derivative.eval c ≠ 0)
    (e : Γ) (he : IsLeast (⋃ n, ((residueErrorPolynomial H).coeff n).support) e) :
    ∃! η : K⟦Γ⟧,
      (0 < η.orderTop ∧ (H.map (nonnegativeSubring Γ K).subtype).IsRoot (single 0 c + η)) ∧
      (η.support ⊆ (residueErrorSupport H : Set Γ) \ {0}) ∧
      η.coeff e = -((residueErrorPolynomial H).eval (single 0 c)).coeff e /
        (H.map (standardPart Γ K)).derivative.eval c := by
  have hepos : 0 < e := by
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp he.1
    have h := (orderTop_residueErrorPolynomial_coeff_pos H n).trans_le
      (orderTop_le_of_coeff_ne_zero ((mem_support _ _).mp hn))
    exact WithTop.coe_lt_coe.mp h
  have hE (n : ℕ) : (e : WithTop Γ) ≤ ((residueErrorPolynomial H).coeff n).orderTop := by
    apply le_orderTop_iff_forall.mpr
    intro g hg
    by_contra hcoeff
    have hge := he.2 (Set.mem_iUnion.mpr ⟨n, (mem_support _ _).mpr hcoeff⟩)
    exact (not_lt_of_ge (WithTop.coe_le_coe.mpr hge)) hg
  obtain ⟨η, ⟨hη, hS, hcoeff⟩, _⟩ :=
    existsUnique_supported_root_correction_with_coefficients H hH c hc hd
  obtain ⟨ζ, _, huniq⟩ := existsUnique_infinitesimal_root_correction H hH c hc hd
  refine ⟨η, ⟨hη, hS, hcoeff e hepos hE⟩, ?_⟩
  intro ε hε
  exact (huniq ε hε.1).trans (huniq η hη).symm

end

end Surreal.HahnSeries
