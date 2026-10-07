import OAI.Combinatorics.Progressions.Estimates.BoundedRealifiedSquareOrbit
import OAI.Combinatorics.Progressions.Estimates.NativeCentralSeed

namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped TensorProduct

variable {L X ι : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  [MulAction (NilpotentLieBCHGroup L s hnil) X]

theorem central_span_character (u : ι → L) (hu : ∀ i (w : L), ⁅u i, w⁆ = 0)
    (η : L →ₗ[ℝ] ℝ) (f : X → ℂ)
    (hf : ∀ i (r : ℝ) x, f (realBCHLine (hnil := hnil) (u i) r • x) =
      CircleFourier.character ((r * η (u i) : ℝ) : CircleFourier.Circle) * f x)
    {v : L} (hv : v ∈ Submodule.span ℝ (Set.range u)) (x : X) :
    f ((⟨v⟩ : NilpotentLieBCHGroup L s hnil) • x) =
      CircleFourier.character ((η v : ℝ) : CircleFourier.Circle) * f x := by
  have h : (∀ w : L, ⁅v, w⁆ = 0) ∧ ∀ (r : ℝ) x,
      f (realBCHLine (hnil := hnil) v r • x) =
        CircleFourier.character ((r * η v : ℝ) : CircleFourier.Circle) * f x := by
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨i, rfl⟩ := hv
      exact ⟨hu i, hf i⟩
    | zero =>
      refine ⟨fun w => zero_lie w, ?_⟩
      intro r x
      have he : realBCHLine (hnil := hnil) (0 : L) r = 1 := by
        apply ext
        exact smul_zero r
      simp [he]
    | @add v w hv hw ihv ihw =>
      refine ⟨fun z => by rw [add_lie, ihv.1, ihw.1, add_zero], ?_⟩
      intro r x
      have he : realBCHLine (hnil := hnil) (v + w) r =
          realBCHLine v r * realBCHLine w r := by
        apply ext
        change r • (v + w) = lieBCH s (r • v) (r • w)
        rw [lieBCH_eq_add_of_lie_eq_zero hnil (by rw [smul_lie, ihv.1, smul_zero]), smul_add]
      rw [he, mul_smul, ihv.2, ihw.2, map_add, mul_add,
        AddCircle.coe_add, CircleFourier.character_add, mul_assoc]
    | @smul a v hv ih =>
      refine ⟨fun w => by rw [smul_lie, ih.1, smul_zero], ?_⟩
      intro r x
      have he : realBCHLine (hnil := hnil) (a • v) r = realBCHLine v (r * a) := by
        apply ext
        exact (mul_smul r a v).symm
      rw [he, ih.2, map_smul, smul_eq_mul, mul_assoc]
  simpa only [realBCHLine_one, one_mul] using h.2 1 x

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (Γ : Subgroup F.Group)

theorem realSquareObservable_relative_character (ε : F.realification.Group)
    (u : F.realification.Group ⧸ Γ.map realificationHom → ℂ)
    (χ : F.realification.Group → CircleFourier.Circle)
    (hu : ∀ z ∈ F.realification.subgroup s, ∀ x, u (z • x) = character (χ z) * u x)
    (k : F.squareFiltration.realification.Group)
    (hk : F.realSquareFstHom k ∈ F.realification.subgroup s)
    (hs : F.realSquareSndHom k = 1)
    (x : F.squareFiltration.realification.Group ⧸ (F.squareLattice Γ).map realificationHom) :
    F.realSquareObservable Γ ε u (k • x) =
      character (χ (F.realSquareFstHom k)) * F.realSquareObservable Γ ε u x := by
  have hcomm (y : F.realification.Group ⧸ Γ.map realificationHom) :
      ε • (F.realSquareFstHom k • y) = F.realSquareFstHom k • (ε • y) := by
    rw [← mul_smul, ← mul_smul, (F.realification.top_commutes _ hk ε).eq]
  simp only [realSquareObservable, cosetMap_smul, hs, one_smul]
  rw [hcomm, hu _ hk]
  exact mul_assoc _ _ _

variable (F : NilpotentLieFiltration L (s + 1)) (Γ : Subgroup F.Group)

theorem realSquare_descent_relative_character (ε : F.realification.Group)
    (u : F.realification.Group ⧸ Γ.map realificationHom → ℂ)
    (χ : F.realification.Group → CircleFourier.Circle)
    (hu : ∀ z ∈ F.realification.subgroup (s + 1), ∀ x, u (z • x) = character (χ z) * u x)
    (v : F.squareFiltration.quotientTop.realification.Group ⧸
      ((F.squareLattice Γ).map (F.squareFiltration.quotientStepHom
        (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl)).map realificationHom → ℂ)
    (hv : ∀ g, v (QuotientGroup.mk (F.squareFiltration.realQuotientStepHom
        (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl g)) =
      F.realSquareObservable Γ ε u (QuotientGroup.mk g))
    (k : F.squareFiltration.realification.Group)
    (hk : F.realSquareFstHom k ∈ F.realification.subgroup (s + 1))
    (hs : F.realSquareSndHom k = 1)
    (x : F.squareFiltration.quotientTop.realification.Group ⧸
      ((F.squareLattice Γ).map (F.squareFiltration.quotientStepHom
        (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl)).map realificationHom) :
    v (F.squareFiltration.realQuotientStepHom
        (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl k • x) =
      character (χ (F.realSquareFstHom k)) * v x := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y, rfl⟩ := F.squareFiltration.realQuotientStepHom_surjective
    (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl g
  change v (QuotientGroup.mk
    (F.squareFiltration.realQuotientStepHom _ (t := s) le_rfl k *
      F.squareFiltration.realQuotientStepHom _ (t := s) le_rfl y)) = _
  rw [← map_mul, hv, hv]
  exact F.realSquareObservable_relative_character Γ ε u χ hu k hk hs (QuotientGroup.mk y)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)
  (Γ : Subgroup F.realification.Group)

theorem vertical_frequency_integral_on_lattice (η : L →ₗ[ℚ] ℚ)
    (f : F.realification.Group ⧸ Γ → ℂ)
    (hf : ∀ z : F.realification.Group, z ∈ F.realification.subgroup s → ∀ x,
      f (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * f x)
    (hne : ∃ x, f x ≠ 0) (z : F.realification.Group)
    (hz : z ∈ F.realification.subgroup s) (hΓ : z ∈ Γ) :
    ∃ n : ℤ, realifyFunctional η z.coord = n := by
  obtain ⟨x, hx⟩ := hne
  have hc : ∀ a : F.realification.Group, Commute z a := by
    intro a
    exact commute_of_lie_eq_zero z a (F.realification.top_layer_central hz a.coord)
  have he : character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) = 1 := by
    apply mul_right_cancel₀ hx
    calc
      _ = f (z • x) := (hf z hz x).symm
      _ = f x := by rw [central_smul_eq_self_of_mem Γ hΓ hc x]
      _ = 1 * f x := (one_mul _).symm
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp ((character_eq_one_iff _).mp he)
  exact ⟨n, by simpa only [zsmul_eq_mul, mul_one] using hn.symm⟩

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct

theorem real_frequency_eq_of_character_multiples (a b : ℝ)
    (h : ∀ t : ℝ, character ((t * a : ℝ) : CircleFourier.Circle) =
      character ((t * b : ℝ) : CircleFourier.Circle)) : a = b := by
  have hinj : Function.Injective character := by
    intro x y hxy
    apply AddCircle.injective_toCircle one_ne_zero
    exact Subtype.ext hxy
  have hzero (t : ℝ) : ((t * (a - b) : ℝ) : CircleFourier.Circle) = 0 := by
    rw [mul_sub, AddCircle.coe_sub]
    exact sub_eq_zero.mpr (hinj (h t))
  by_contra hne
  have hab : a - b ≠ 0 := sub_ne_zero.mpr hne
  have ht : (1 / (2 * (a - b))) * (a - b) = (1 : ℝ) / 2 := by
    field_simp
  have hhalf := hzero (1 / (2 * (a - b)))
  rw [ht] at hhalf
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hhalf
  have hn' : (n : ℝ) = 1 / 2 := by simpa only [zsmul_eq_mul, mul_one] using hn
  have hn0 : (0 : ℤ) < n := by exact_mod_cast (show (0 : ℝ) < n by linarith)
  have hn1 : n < (1 : ℤ) := by exact_mod_cast (show (n : ℝ) < 1 by linarith)
  omega

theorem vertical_frequency_on_real_direction
    {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (Γ : Subgroup F.realification.Group)
    (ξ : L →ₗ[ℚ] ℚ) (f : F.realification.Group ⧸ Γ → ℂ)
    (hvert : ∀ z ∈ F.realification.subgroup s, ∀ x,
      f (z • x) = character ((realifyFunctional ξ z.coord : ℝ) : CircleFourier.Circle) * f x)
    (hne : ∃ x, f x ≠ 0) (y : L) (hy : y ∈ F.layer s) (a : ℝ)
    (hcharacter : ∀ t : ℝ, ∀ x,
      f ((⟨t ⊗ₜ[ℚ] y⟩ : F.realification.Group) • x) =
        character ((t * a : ℝ) : CircleFourier.Circle) * f x) :
    (ξ y : ℝ) = a := by
  obtain ⟨x, hx⟩ := hne
  apply real_frequency_eq_of_character_multiples
  intro t
  apply mul_right_cancel₀ hx
  have hz : (⟨t ⊗ₜ[ℚ] y⟩ : F.realification.Group) ∈ F.realification.subgroup s :=
    Submodule.tmul_mem_baseChange_of_mem t hy
  have heq := (hvert _ hz x).symm.trans (hcharacter t x)
  simpa only [realifyFunctional_tmul] using heq

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))

theorem square_mode_relative_frequency (hs : 1 ≤ s)
    (Γ : Subgroup F.squareFiltration.quotientTop.realification.Group)
    (η : L →ₗ[ℚ] ℚ)
    (ξ : (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)) →ₗ[ℚ] ℚ)
    (f : F.squareFiltration.quotientTop.realification.Group ⧸ Γ → ℂ)
    (hvert : ∀ z ∈ F.squareFiltration.quotientTop.realification.subgroup s, ∀ y,
      f (z • y) = character ((realifyFunctional ξ z.coord : ℝ) : CircleFourier.Circle) * f y)
    (hne : ∃ y, f y ≠ 0)
    (hrelative : ∀ k : F.squareFiltration.realification.Group,
      F.realSquareFstHom k ∈ F.realification.subgroup (s + 1) →
      F.realSquareSndHom k = 1 → ∀ y,
      f (F.squareFiltration.realQuotientStepHom
          (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl k • y) =
        character ((realifyFunctional η (F.realSquareFstHom k).coord : ℝ) : CircleFourier.Circle) * f y)
    (x : F.layer (s + 1)) :
    ξ (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1))
      (F.squareRelativeLayer s hs x).val) = η x := by
  let z : F.squareLieSubalgebra := (F.squareRelativeLayer s hs x).val
  let q := lieQuotientMap (F.squareFiltration.layerIdeal (s + 1)) z
  have hq : q ∈ F.squareFiltration.quotientTop.layer s :=
    F.squareFiltration.quotientLie_mem _ le_rfl (F.squareRelativeLayer s hs x).property
  have h := vertical_frequency_on_real_direction F.squareFiltration.quotientTop Γ ξ f
    hvert hne q hq (η x : ℝ) (by
      intro t y
      let k : F.squareFiltration.realification.Group := ⟨t ⊗ₜ[ℚ] z⟩
      have hf : F.realSquareFstHom k = (⟨t ⊗ₜ[ℚ] (x : L)⟩ : F.realification.Group) :=
        NilpotentLieBCHGroup.ext rfl
      have hk : F.realSquareFstHom k ∈ F.realification.subgroup (s + 1) := by
        rw [hf]
        exact Submodule.tmul_mem_baseChange_of_mem t x.property
      have hkzero : F.realSquareSndHom k = 1 := by
        apply NilpotentLieBCHGroup.ext
        change t ⊗ₜ[ℚ] (0 : L) = 0
        simp only [TensorProduct.tmul_zero]
      have hπ : F.squareFiltration.realQuotientStepHom
          (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl k =
          (⟨t ⊗ₜ[ℚ] q⟩ : F.squareFiltration.quotientTop.realification.Group) :=
        NilpotentLieBCHGroup.ext rfl
      have he := hrelative k hk hkzero y
      rw [hπ, hf] at he
      simpa only [realifyFunctional_tmul] using he)
  exact_mod_cast h

theorem descended_square_mode_frequency_restriction (hs : 1 ≤ s)
    (Γ : Subgroup F.Group) (ε : F.realification.Group)
    (η : L →ₗ[ℚ] ℚ) (u : F.realification.Group ⧸ Γ.map realificationHom → ℂ)
    (hu : ∀ z ∈ F.realification.subgroup (s + 1), ∀ y,
      u (z • y) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * u y)
    (v f : F.squareFiltration.quotientTop.realification.Group ⧸
      ((F.squareLattice Γ).map (F.squareFiltration.quotientStepHom
        (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl)).map realificationHom → ℂ)
    (hv : ∀ g, v (QuotientGroup.mk (F.squareFiltration.realQuotientStepHom
        (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl g)) =
      F.realSquareObservable Γ ε u (QuotientGroup.mk g))
    (ξ : (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)) →ₗ[ℚ] ℚ)
    (hvert : ∀ z ∈ F.squareFiltration.quotientTop.realification.subgroup s, ∀ y,
      f (z • y) = character ((realifyFunctional ξ z.coord : ℝ) : CircleFourier.Circle) * f y)
    (hne : ∃ y, f y ≠ 0)
    (hpres : ∀ (z : F.squareFiltration.quotientTop.realification.Group) (c : ℂ),
      (∀ y, v (z • y) = c * v y) → ∀ y, f (z • y) = c * f y)
    (x : F.layer (s + 1)) :
    ξ (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1))
      (F.squareRelativeLayer s hs x).val) = η x := by
  apply F.square_mode_relative_frequency hs _ η ξ f hvert hne
  intro k hk hkzero y
  exact hpres _ _
    (fun z => F.realSquare_descent_relative_character Γ ε u
      (fun a => ((realifyFunctional η a.coord : ℝ) : CircleFourier.Circle))
      hu v hv k hk hkzero z) y

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

theorem vertical_frequency_eq_of_real_line
    (F : NilpotentLieFiltration L s) (Γ : Subgroup F.realification.Group)
    (η : L →ₗ[ℚ] ℚ) (f : F.realification.Group ⧸ Γ → ℂ)
    (hvert : ∀ z ∈ F.realification.subgroup s, ∀ x,
      f (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * f x)
    (hne : ∃ x, f x ≠ 0) (c : L) (hc : c ∈ F.layer s) (a : ℚ)
    (hline : ∀ t : ℝ, ∀ x,
      f ((⟨t ⊗ₜ[ℚ] c⟩ : F.realification.Group) • x) =
        character ((t * a : ℝ) : CircleFourier.Circle) * f x) :
    η c = a := by
  exact_mod_cast vertical_frequency_on_real_direction F Γ η f hvert hne c hc (a : ℝ) hline

theorem vertical_frequency_eq_one_of_real_line
    (F : NilpotentLieFiltration L s) (Γ : Subgroup F.realification.Group)
    (η : L →ₗ[ℚ] ℚ) (f : F.realification.Group ⧸ Γ → ℂ)
    (hvert : ∀ z ∈ F.realification.subgroup s, ∀ x,
      f (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * f x)
    (hne : ∃ x, f x ≠ 0) (c : L) (hc : c ∈ F.layer s)
    (hline : ∀ t : ℝ, ∀ x,
      f ((⟨t ⊗ₜ[ℚ] c⟩ : F.realification.Group) • x) =
        character (t : CircleFourier.Circle) * f x) :
    η c = 1 := by
  apply vertical_frequency_eq_of_real_line F Γ η f hvert hne c hc 1
  simpa only [Rat.cast_one, mul_one] using hline

end Erdos3

end

end OAI
