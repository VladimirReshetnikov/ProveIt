import OAI.Combinatorics.Progressions.Estimates.AllocatedFullAmbientSiteFactor
import OAI.Combinatorics.Progressions.Estimates.AllocatedNaturalFullSiteScale

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite

variable {m : ℕ} {G : Type*} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R : Fin m → ℝ}
variable {A S : Type*} [Fintype A] (e : A → ScalarSiteExpansion S)
variable (selected : A → Σ j : Fin m, Fin (n j))

local notation "index" => fun a : A => (Sigma.mk (Sigma.fst (selected a)) (Sum.inr (Sigma.snd (selected a))) : LayerSamplerAxis I n)
local notation "ratio" => fun a : A => allocatedNaturalFullSiteRatio (G := G) B U b (R := R)
  (Sigma.fst (selected a)) (Sigma.snd (selected a))
local notation "scale" => fun a : A => allocatedPrincipalGridScale (G := G) B U b (R := R)
  (Sigma.fst (selected a)) (Sigma.snd (selected a))

noncomputable def allocatedFullGridSiteFactor (k : ∀ a, (e a).Term) (s : S)
    (r : ∀ a, ZMod ((e a).period (k a))) (x : LayerSamplerAxis I n → ℝ) : ℂ :=
  scaledSiteFamilyFactor e (index) (ratio) k s r x

theorem allocatedFullGridSiteFactor_bounds (hR : ∀ j, 0 < R j)
    {T V C H : A → ℝ} {L : ℝ≥0}
    (h : ∀ a, (e a).Bounds (T a) (V a) (C a) L (H a))
    (Q : ℝ≥0) (hQ : ∀ a, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (selected a).1 (selected a).2) : ℝ) + 1) ≤ Q)
    (k : ∀ a, (e a).Term) (s : S) (r : ∀ a, ZMod ((e a).period (k a))) :
    (∀ x, ‖allocatedFullGridSiteFactor (G := G) B U b (R := R) e selected k s r x‖ ≤ 1) ∧
      LipschitzWith ((Fintype.card A * L) * Q)
        (allocatedFullGridSiteFactor (G := G) B U b (R := R) e selected k s r) := by
  apply scaledSiteFamilyFactor_bounds e (index) (ratio) h Q _ k s r
  intro a
  rw [abs_of_pos (allocatedNaturalFullSiteRatio_pos B U b hR (selected a).1 (selected a).2)]
  exact (allocatedNaturalFullSiteRatio_le B U b hR (selected a).1 (selected a).2).trans (hQ a)

omit [∀ j, Fintype (I j)] in
theorem allocatedFullGridSiteFactor_support (hR : ∀ j, 0 < R j)
    {T V C H : A → ℝ} {L : ℝ≥0}
    (h : ∀ a, (e a).Bounds (T a) (V a) (C a) L (H a))
    (k : ∀ a, (e a).Term) (s : S) (r : ∀ a, ZMod ((e a).period (k a)))
    (x : LayerSamplerAxis I n → ℝ)
    (hx : ∃ a, H a / (ratio) a ≤ |x ((index) a)|) :
    allocatedFullGridSiteFactor (G := G) B U b (R := R) e selected k s r x = 0 :=
  scaledSiteFamilyFactor_support e (index) (ratio) h
    (fun a => allocatedNaturalFullSiteRatio_pos B U b hR (selected a).1 (selected a).2) k s r x hx

omit [∀ j, Fintype (I j)] in
theorem allocatedFullGridSiteFactor_point (hR : ∀ j, 0 < R j)
    (k : ∀ a, (e a).Term) (s : S) (r : ∀ a, ZMod ((e a).period (k a)))
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) :
    allocatedFullGridSiteFactor (G := G) B U b (R := R) e selected k s r
        (allocatedFullMixedSiteValue (R := R) U b w) =
      siteFamilyFactor e k s r (fun a => ((w (selected a).1).2 (selected a).2 : ℝ) / (scale) a) := by
  apply congrArg (siteFamilyFactor e k s r)
  funext a
  exact allocatedNaturalFullSiteRatio_coordinate B U b hR (selected a).1 (selected a).2 _

omit [∀ j, Fintype (I j)] in
theorem allocatedFullGridSiteFactor_eval [Fintype S] (hR : ∀ j, 0 < R j)
    (w : S → ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) :
    (∑ k, siteFamilyCoefficient e k * ∏ s,
      allocatedFullGridSiteFactor (G := G) B U b (R := R) e selected k s
        (fun a => ((w s (selected a).1).2 (selected a).2 : ZMod ((e a).period (k a))))
        (allocatedFullMixedSiteValue (R := R) U b (w s))) =
      siteFamilyEval e (fun s a => (w s (selected a).1).2 (selected a).2)
        (fun s a => ((w s (selected a).1).2 (selected a).2 : ℝ) / (scale) a) := by
  unfold siteFamilyEval
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  exact Finset.prod_congr rfl (fun s _ => allocatedFullGridSiteFactor_point B U b e selected hR k s _ (w s))

theorem exists_allocated_full_grid_ambient_factor (hR : ∀ j, 0 < R j)
    {T V C H : A → ℝ} {L : ℝ≥0}
    (h : ∀ a, (e a).Bounds (T a) (V a) (C a) L (H a))
    (Q : ℝ≥0) (hQ : ∀ a, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (selected a).1 (selected a).2) : ℝ) + 1) ≤ Q)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (k : ∀ a, (e a).Term) (s : S) (r : ∀ a, ZMod ((e a).period (k a))) :
    ∃ g : (JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) → ℂ,
      LipschitzWith (2 * (((Fintype.card A * L) * Q) *
        (K * ∑ j, Cforward j * Fintype.card (J j)))) g ∧
      (∀ z, ‖g z‖ ≤ 2) ∧
      ∀ v : JetAmbientIndex (fun _ : Fin m => Unit) J → ℝ, (∀ i, |v i| ≤ 1 / 4) →
        g (fun i => (v i : UnitAddCircle)) =
          allocatedFullGridSiteFactor (G := G) B U b (R := R) e selected k s r
            (allocatedFullAmbientSiteCoordinates (R := R) U b o v) := by
  have hf := allocatedFullGridSiteFactor_bounds B U b e selected hR h Q hQ k s r
  exact exists_allocated_full_ambient_site_factor U b o hR Cforward hforward K hK _ _ hf.2 hf.1

end Erdos3.VectorPolynomial

end

end OAI
