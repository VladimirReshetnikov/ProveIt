import Surreal.Algebra.FineDerivative
import Surreal.Surcomplex.Modulus

/-!
# Fine derivatives on the actual scalar fields

The native punctured-neighborhood definition is exactly the scalar-valued
ε–δ condition in `found:eq:derivative`, on both real and complex surreals.
All positive surreal tolerances are retained. A locally bounded quadratic
remainder suffices to prove a derivative, as used in the Taylor-lifting
argument of `trigonometry:prop:lift`.
-/

universe u

open Filter Topology

namespace Surreal.Foundations.SignSequence

/-- The native limit uses every positive surreal absolute-value tolerance. -/
theorem fineHasDerivAt_iff (f : SignSequence.{u} → SignSequence.{u}) (d a : SignSequence.{u}) :
    FineHasDerivAt f d a ↔ ∀ ε : SignSequence.{u}, 0 < ε →
      ∃ δ : SignSequence.{u}, 0 < δ ∧ ∀ h : SignSequence.{u}, h ≠ 0 → |h| < δ →
        |(f (a + h) - f a) / h - d| < ε := by
  rw [FineHasDerivAt, (nhdsWithin_hasBasis (nhds_hasBasis_abs_sub 0) {0}ᶜ).tendsto_iff
    (nhds_hasBasis_abs_sub d)]
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, sub_zero, Set.mem_compl_iff,
    Set.mem_singleton_iff]
  constructor
  · intro H ε hε
    obtain ⟨δ, hδ, h⟩ := H ε hε
    exact ⟨δ, hδ, fun x hx hlt => h x ⟨hlt, hx⟩⟩
  · intro H ε hε
    obtain ⟨δ, hδ, h⟩ := H ε hε
    exact ⟨δ, hδ, fun x hx => h x hx.2 hx.1⟩

/-- The fine derivative on the sign carrier is unique. -/
theorem fineHasDerivAt_unique {f : SignSequence.{u} → SignSequence.{u}}
    {d e a : SignSequence.{u}} (hd : FineHasDerivAt f d a) (he : FineHasDerivAt f e a) : d = e := by
  letI := punctured_nhds_neBot (0 : SignSequence.{u})
  exact hd.unique he

/-- A bounded quadratic remainder gives the fine derivative at the center. -/
theorem fineHasDerivAt_of_quadratic_remainder (f : SignSequence.{u} → SignSequence.{u})
    (d a M : SignSequence.{u}) (hM : 0 < M)
    (hR : ∀ᶠ h in 𝓝 0, ∃ R : SignSequence.{u},
      f (a + h) = f a + d * h + h ^ 2 * R ∧ |R| ≤ M) : FineHasDerivAt f d a := by
  apply (fineHasDerivAt_iff f d a).mpr
  intro ε hε
  obtain ⟨r, hr, hR⟩ := (nhds_hasBasis_abs_sub (0 : SignSequence.{u})).mem_iff.mp hR
  refine ⟨min r (ε / M), lt_min hr (div_pos hε hM), ?_⟩
  intro h hne hh
  obtain ⟨R, hEq, hbound⟩ := hR (by simpa only [Set.mem_setOf_eq, sub_zero] using (lt_min_iff.mp hh).1)
  have hquot : (f (a + h) - f a) / h - d = h * R := by
    rw [hEq]
    field_simp [hne]
    ring
  rw [hquot, abs_mul]
  exact (mul_le_mul_of_nonneg_left hbound (abs_nonneg h)).trans_lt
    ((lt_div_iff₀ hM).mp (lt_min_iff.mp hh).2)

end Surreal.Foundations.SignSequence

namespace Surreal.Surcomplex

open Foundations

/-- The native limit uses every positive surreal modulus tolerance. -/
theorem fineHasDerivAt_iff (f : Surcomplex.{u} → Surcomplex.{u}) (d a : Surcomplex.{u}) :
    FineHasDerivAt f d a ↔ ∀ ε : SignSequence.{u}, 0 < ε →
      ∃ δ : SignSequence.{u}, 0 < δ ∧ ∀ h : Surcomplex.{u}, h ≠ 0 → modulus h < δ →
        modulus ((f (a + h) - f a) / h - d) < ε := by
  rw [FineHasDerivAt, (nhdsWithin_hasBasis (nhds_hasBasis_modulus 0) {0}ᶜ).tendsto_iff
    (nhds_hasBasis_modulus d)]
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, sub_zero, Set.mem_compl_iff,
    Set.mem_singleton_iff]
  constructor
  · intro H ε hε
    obtain ⟨δ, hδ, h⟩ := H ε hε
    exact ⟨δ, hδ, fun x hx hlt => h x ⟨hlt, hx⟩⟩
  · intro H ε hε
    obtain ⟨δ, hδ, h⟩ := H ε hε
    exact ⟨δ, hδ, fun x hx => h x hx.2 hx.1⟩

/-- The fine derivative on the actual surcomplex field is unique. -/
theorem fineHasDerivAt_unique {f : Surcomplex.{u} → Surcomplex.{u}}
    {d e a : Surcomplex.{u}} (hd : FineHasDerivAt f d a) (he : FineHasDerivAt f e a) : d = e := by
  letI := punctured_nhds_neBot (0 : Surcomplex.{u})
  exact hd.unique he

/-- A locally bounded quadratic remainder suffices for every fine tolerance. -/
theorem fineHasDerivAt_of_quadratic_remainder (f : Surcomplex.{u} → Surcomplex.{u})
    (d a : Surcomplex.{u}) (M : SignSequence.{u}) (hM : 0 < M)
    (hR : ∀ᶠ h in 𝓝 0, ∃ R : Surcomplex.{u},
      f (a + h) = f a + d * h + h ^ 2 * R ∧ modulus R ≤ M) : FineHasDerivAt f d a := by
  apply (fineHasDerivAt_iff f d a).mpr
  intro ε hε
  obtain ⟨r, hr, hR⟩ := (nhds_hasBasis_modulus (0 : Surcomplex.{u})).mem_iff.mp hR
  refine ⟨min r (ε / M), lt_min hr (div_pos hε hM), ?_⟩
  intro h hne hh
  obtain ⟨R, hEq, hbound⟩ := hR (by simpa only [Set.mem_setOf_eq, sub_zero] using (lt_min_iff.mp hh).1)
  have hquot : (f (a + h) - f a) / h - d = h * R := by
    rw [hEq]
    field_simp [hne]
    ring
  rw [hquot, modulus_mul]
  exact (mul_le_mul_of_nonneg_left hbound (modulus_nonneg h)).trans_lt
    ((lt_div_iff₀ hM).mp (lt_min_iff.mp hh).2)

end Surreal.Surcomplex
