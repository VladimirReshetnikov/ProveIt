import OAI.Combinatorics.Progressions.Polynomial.MarkedPolynomialGenerators
import OAI.Combinatorics.Progressions.Polynomial.PolynomialShiftStructure

namespace OAI

section

namespace Erdos3

open VectorPolynomial

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)

noncomputable def markedShiftSubalgebra (t : ℕ) :
    LieSubalgebra ℚ (F.associatedDegree.PolynomialShiftAlgebra t) where
  carrier := {x | x.left.val ∈ markedPolynomialLayer v w marked 0 0 0}
  zero_mem' := (markedPolynomialLayer v w marked 0 0 0).zero_mem
  add_mem' hx hy := (markedPolynomialLayer v w marked 0 0 0).add_mem hx hy
  smul_mem' c _ hx := (markedPolynomialLayer v w marked 0 0 0).smul_mem c hx
  lie_mem' := by
    intro x y hx hy
    change ⁅x.left.val, y.left.val⁆ + directionalDerivative x.right y.left.val -
      directionalDerivative y.right x.left.val ∈ markedPolynomialLayer v w marked 0 0 0
    have hder (h : Fin t → ℚ) (p : VectorPolynomial (Fin t) ℚ L)
        (hp : p ∈ markedPolynomialLayer v w marked 0 0 0) :
        directionalDerivative h p ∈ markedPolynomialLayer v w marked 0 0 0 :=
      markedPolynomialLayer_antitone v w marked le_rfl (Nat.zero_le 1) le_rfl
        (markedPolynomialLayer_directionalDerivative v w marked h (d := 0) (k := 0) (l := 0) hp)
    exact (markedPolynomialLayer v w marked 0 0 0).sub_mem
      ((markedPolynomialLayer v w marked 0 0 0).add_mem
        (markedPolynomialLayer_lie_mem v w marked
          (d := 0) (e := 0) (k := 0) (m := 0) (l := 0) (n := 0) hx hy)
        (hder x.right y.left.val hy)) (hder y.right x.left.val hx)

theorem markedShiftSubalgebra_contains_direction (t : ℕ) (h : RationalTorus.Algebra t) :
    (⟨0, h⟩ : F.associatedDegree.PolynomialShiftAlgebra t) ∈ markedShiftSubalgebra F v w marked t :=
  (markedPolynomialLayer v w marked 0 0 0).zero_mem

theorem markedShiftSubalgebra_contains_polynomial (hw : ∀ i, 0 < w i)
    (hv : ∀ i, v i ∈ F.layer (w i) 1) (t : ℕ)
    (p : markedPolynomialAlgebra (σ := Fin t) v w marked) :
    (⟨⟨p.val, markedPolynomialAlgebra_le_adapted F v w marked hw hv p.property⟩, 0⟩ :
      F.associatedDegree.PolynomialShiftAlgebra t) ∈ markedShiftSubalgebra F v w marked t := p.property

noncomputable def markedShiftFiltration (t : ℕ) :
    NilpotentLieFiltration (markedShiftSubalgebra F v w marked t) (max 1 (2 * s)) :=
  (F.associatedDegree.polynomialShiftFiltration t).restrictLieSubalgebra
    (markedShiftSubalgebra F v w marked t)

theorem markedShift_lowerCentralSeries_eq_bot (t : ℕ) :
    LieModule.lowerCentralSeries ℚ (markedShiftSubalgebra F v w marked t)
      (markedShiftSubalgebra F v w marked t) (max 1 (2 * s)) = ⊥ :=
  (markedShiftFiltration F v w marked t).lowerCentralSeries_eq_bot

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)

noncomputable def markedShiftPolynomialSubmodule (t d k l : ℕ) :
    Submodule ℚ (markedShiftSubalgebra F v w marked t) where
  carrier := {x | x.val.right = 0 ∧ x.val.left.val ∈ markedPolynomialLayer v w marked d k l}
  zero_mem' := ⟨rfl, (markedPolynomialLayer v w marked d k l).zero_mem⟩
  add_mem' := by
    intro x y hx hy
    constructor
    · change x.val.right + y.val.right = (0 : RationalTorus.Algebra t)
      rw [hx.1, hy.1, add_zero]
    · exact (markedPolynomialLayer v w marked d k l).add_mem hx.2 hy.2
  smul_mem' c x hx := by
    constructor
    · change c • x.val.right = 0
      rw [hx.1, smul_zero]
    · exact (markedPolynomialLayer v w marked d k l).smul_mem c hx.2

noncomputable def markedShiftSecondIdeal (t : ℕ) :
    LieIdeal ℚ (markedShiftSubalgebra F v w marked t) :=
  { markedShiftPolynomialSubmodule F v w marked t 0 2 0 with
    lie_mem := by
      intro x y hy
      constructor
      · rfl
      · change ⁅x.val.left.val, y.val.left.val⁆ + directionalDerivative x.val.right y.val.left.val -
          directionalDerivative y.val.right x.val.left.val ∈ markedPolynomialLayer v w marked 0 2 0
        rw [hy.1]
        have hz : directionalDerivative (0 : Fin t → ℚ) x.val.left.val = 0 := by
          simp only [directionalDerivative, Pi.zero_apply, zero_smul, Finset.sum_const_zero,
            LinearMap.zero_apply]
        change ⁅x.val.left.val, y.val.left.val⁆ + directionalDerivative x.val.right y.val.left.val -
          directionalDerivative (0 : Fin t → ℚ) x.val.left.val ∈ markedPolynomialLayer v w marked 0 2 0
        rw [hz, sub_zero]
        apply (markedPolynomialLayer v w marked 0 2 0).add_mem
        · exact markedPolynomialLayer_lie_mem v w marked
            (d := 0) (e := 0) (k := 0) (m := 2) (l := 0) (n := 0) x.property hy.2
        · exact markedPolynomialLayer_antitone v w marked le_rfl (by omega : 2 ≤ 2 + 1) le_rfl
            (markedPolynomialLayer_directionalDerivative v w marked x.val.right
              (d := 0) (k := 2) (l := 0) hy.2) }

abbrev MarkedShiftQuotient (t : ℕ) :=
  markedShiftSubalgebra F v w marked t ⧸ markedShiftSecondIdeal F v w marked t

theorem markedShiftQuotient_lowerCentralSeries_eq_bot (t : ℕ) :
    LieModule.lowerCentralSeries ℚ (MarkedShiftQuotient F v w marked t)
      (MarkedShiftQuotient F v w marked t) (max 1 (2 * s)) = ⊥ :=
  lie_quotient_lowerCentralSeries_eq_bot (markedShift_lowerCentralSeries_eq_bot F v w marked t)
    (markedShiftSecondIdeal F v w marked t)

abbrev MarkedShiftQuotientGroup (t : ℕ) :=
  NilpotentLieBCHGroup (MarkedShiftQuotient F v w marked t) (max 1 (2 * s))
    (markedShiftQuotient_lowerCentralSeries_eq_bot F v w marked t)

noncomputable def markedShiftEval (t : ℕ) (a : Fin t → ℚ) :
    markedShiftSubalgebra F v w marked t →ₗ[ℚ] L where
  toFun x := eval a x.val.left.val
  map_add' x y := (eval a).map_add x.val.left.val y.val.left.val
  map_smul' c x := (eval a).map_smul c x.val.left.val

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)

noncomputable def markedShiftBiLayer (t h n : ℕ) :
    Submodule ℚ (markedShiftSubalgebra F v w marked t) where
  carrier := {x | x.val.left.val ∈ markedPolynomialLayer v w marked n h 0 ∧
    (n ≠ 0 ∨ 1 < h → x.val.right = 0)}
  zero_mem' := ⟨(markedPolynomialLayer v w marked n h 0).zero_mem, fun _ => rfl⟩
  add_mem' := by
    intro x y hx hy
    refine ⟨(markedPolynomialLayer v w marked n h 0).add_mem hx.1 hy.1, ?_⟩
    intro hc
    change x.val.right + y.val.right = 0
    rw [hx.2 hc, hy.2 hc, add_zero]
  smul_mem' c x hx := by
    refine ⟨(markedPolynomialLayer v w marked n h 0).smul_mem c hx.1, ?_⟩
    intro hc
    change c • x.val.right = 0
    rw [hx.2 hc, smul_zero]

theorem markedShiftBiLayer_antitone (t : ℕ) {h k n m : ℕ} (hh : h ≤ k) (hn : n ≤ m) :
    markedShiftBiLayer F v w marked t k m ≤ markedShiftBiLayer F v w marked t h n := by
  intro x hx
  refine ⟨markedPolynomialLayer_antitone v w marked hn hh le_rfl hx.1, ?_⟩
  intro hc
  exact hx.2 (by omega)

theorem markedShiftBiLayer_zero (t : ℕ) : markedShiftBiLayer F v w marked t 0 0 = ⊤ := by
  apply top_unique
  intro x _
  refine ⟨x.property, ?_⟩
  intro hc
  omega

theorem markedPolynomialLayer_shiftDerivative {t h n k m : ℕ} (u : Fin t → ℚ)
    (hu : n ≠ 0 ∨ 1 < h → u = 0) {p : VectorPolynomial (Fin t) ℚ L}
    (hp : p ∈ markedPolynomialLayer v w marked m k 0) :
    directionalDerivative u p ∈ markedPolynomialLayer v w marked (n + m) (h + k) 0 := by
  by_cases ha : n = 0 ∧ h ≤ 1
  · obtain ⟨rfl, hh⟩ := ha
    have hd := markedPolynomialLayer_directionalDerivative v w marked u hp
    simpa only [Nat.zero_add] using
      markedPolynomialLayer_antitone v w marked le_rfl (by omega : h + k ≤ k + 1) le_rfl hd
  · have hz := hu (by omega)
    rw [hz]
    simp only [directionalDerivative, Pi.zero_apply, zero_smul, Finset.sum_const_zero,
      LinearMap.zero_apply, Submodule.zero_mem]

theorem markedShiftBiLayer_lie_mem (t : ℕ) {h k n m : ℕ}
    {x y : markedShiftSubalgebra F v w marked t}
    (hx : x ∈ markedShiftBiLayer F v w marked t h n)
    (hy : y ∈ markedShiftBiLayer F v w marked t k m) :
    ⁅x, y⁆ ∈ markedShiftBiLayer F v w marked t (h + k) (n + m) := by
  constructor
  · change ⁅x.val.left.val, y.val.left.val⁆ + directionalDerivative x.val.right y.val.left.val -
      directionalDerivative y.val.right x.val.left.val ∈ markedPolynomialLayer v w marked (n + m) (h + k) 0
    apply (markedPolynomialLayer v w marked (n + m) (h + k) 0).sub_mem
    · exact (markedPolynomialLayer v w marked (n + m) (h + k) 0).add_mem
        (markedPolynomialLayer_lie_mem v w marked (l := 0) (n := 0) hx.1 hy.1)
        (markedPolynomialLayer_shiftDerivative v w marked x.val.right hx.2 hy.1)
    · simpa only [Nat.add_comm] using
        markedPolynomialLayer_shiftDerivative v w marked y.val.right hy.2 hx.1
  · intro _
    rfl

theorem markedShiftBiLayer_eq_polynomialSubmodule (t h n : ℕ) (hc : n ≠ 0 ∨ 1 < h) :
    markedShiftBiLayer F v w marked t h n = markedShiftPolynomialSubmodule F v w marked t n h 0 := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.2 hc, hx.1⟩
  · intro hx
    exact ⟨hx.2, fun _ => hx.1⟩

theorem markedShiftBiLayer_second (t : ℕ) :
    markedShiftBiLayer F v w marked t 2 0 = (markedShiftSecondIdeal F v w marked t).toSubmodule :=
  markedShiftBiLayer_eq_polynomialSubmodule F v w marked t 2 0 (Or.inr (by decide))

theorem markedShiftBiLayer_positive (hw : ∀ i, 0 < w i) (t : ℕ) :
    markedShiftBiLayer F v w marked t 0 1 ⊔ markedShiftBiLayer F v w marked t 1 0 = ⊤ := by
  apply top_unique
  intro x _
  let p : markedShiftSubalgebra F v w marked t := ⟨⟨x.val.left, 0⟩, x.property⟩
  let q : markedShiftSubalgebra F v w marked t :=
    ⟨⟨0, x.val.right⟩, (markedPolynomialLayer v w marked 0 0 0).zero_mem⟩
  have hp : p ∈ markedShiftBiLayer F v w marked t 0 1 := by
    exact ⟨(markedPolynomialLayer_degree_zero_eq_one v w marked hw 0 0).le x.property,
      fun _ => rfl⟩
  have hq : q ∈ markedShiftBiLayer F v w marked t 1 0 := by
    refine ⟨(markedPolynomialLayer v w marked 0 1 0).zero_mem, ?_⟩
    intro hc
    omega
  have he : p + q = x := by
    apply Subtype.ext
    apply LieAlgebra.SemiDirectSum.ext
    · change x.val.left + 0 = x.val.left
      exact add_zero _
    · change 0 + x.val.right = x.val.right
      exact zero_add _
  have hx := Submodule.add_mem _ (Submodule.mem_sup_left hp) (Submodule.mem_sup_right hq)
  rwa [he] at hx

theorem markedShiftBiLayer_degree_terminal
    (hv : ∀ i, v i ∈ F.layer (w i) 1) (t h : ℕ) :
    markedShiftBiLayer F v w marked t h (s + 1) = ⊥ := by
  apply bot_unique
  intro x hx
  have hp : x.val.left.val = 0 := by
    simpa only [markedPolynomialLayer_degree_terminal F v w marked hv, Submodule.mem_bot] using hx.1
  have hq : x.val.right = 0 := hx.2 (Or.inl (by omega))
  change x = 0
  apply Subtype.ext
  apply LieAlgebra.SemiDirectSum.ext
  · apply Subtype.ext
    change x.val.left.val = 0
    exact hp
  · change x.val.right = 0
    exact hq

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial NilpotentLieBCHGroup

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (t : ℕ)

noncomputable def markedShiftDirection (h : Fin t → ℚ) : markedShiftSubalgebra F v w marked t :=
  ⟨⟨0, h⟩, markedShiftSubalgebra_contains_direction F v w marked t h⟩

theorem markedShiftDirection_lie_left (h : Fin t → ℚ) (x : markedShiftSubalgebra F v w marked t) :
    (⁅markedShiftDirection F v w marked t h, x⁆).val.left.val =
      directionalDerivative h x.val.left.val := by
  change ⁅(0 : VectorPolynomial (Fin t) ℚ L), x.val.left.val⁆ +
    directionalDerivative h x.val.left.val - directionalDerivative x.val.right 0 = _
  have hz : ⁅(0 : VectorPolynomial (Fin t) ℚ L), x.val.left.val⁆ = 0 :=
    zero_lie (L := VectorPolynomial (Fin t) ℚ L) x.val.left.val
  have hd : directionalDerivative x.val.right (0 : VectorPolynomial (Fin t) ℚ L) = 0 := map_zero _
  exact (congrArg₂ (fun a b : VectorPolynomial (Fin t) ℚ L =>
    a + directionalDerivative h x.val.left.val - b) hz hd).trans (by simp)

theorem markedShiftDirection_lie_right (h : Fin t → ℚ) (x : markedShiftSubalgebra F v w marked t) :
    (⁅markedShiftDirection F v w marked t h, x⁆).val.right = 0 := rfl

theorem markedShiftDirection_double_lie_mem (h : Fin t → ℚ)
    (x : markedShiftSubalgebra F v w marked t) :
    ⁅markedShiftDirection F v w marked t h, ⁅markedShiftDirection F v w marked t h, x⁆⁆ ∈
      markedShiftSecondIdeal F v w marked t := by
  refine ⟨rfl, ?_⟩
  rw [markedShiftDirection_lie_left, markedShiftDirection_lie_left]
  exact markedPolynomialLayer_directionalDerivative v w marked h
    (markedPolynomialLayer_directionalDerivative v w marked h x.property)

noncomputable def markedQuotientDirection (h : Fin t → ℚ) : MarkedShiftQuotient F v w marked t :=
  lieQuotientMap (markedShiftSecondIdeal F v w marked t) (markedShiftDirection F v w marked t h)

theorem markedQuotientDirection_double_lie (h : Fin t → ℚ) (x : MarkedShiftQuotient F v w marked t) :
    ⁅markedQuotientDirection F v w marked t h, ⁅markedQuotientDirection F v w marked t h, x⁆⁆ = 0 := by
  obtain ⟨z, rfl⟩ := lieQuotientMap_surjective (markedShiftSecondIdeal F v w marked t) x
  change ⁅lieQuotientMap _ _, ⁅lieQuotientMap _ _, lieQuotientMap _ z⁆⁆ = 0
  rw [← LieHom.map_lie, ← LieHom.map_lie]
  exact (lieQuotientMap_eq_zero _ _).mpr (markedShiftDirection_double_lie_mem F v w marked t h z)

theorem markedQuotientDirection_conjugation (hs : 1 ≤ s) (h : Fin t → ℚ)
    (x : MarkedShiftQuotient F v w marked t) :
    conjugationCoord (⟨markedQuotientDirection F v w marked t h⟩ : MarkedShiftQuotientGroup F v w marked t) x =
      x + ⁅markedQuotientDirection F v w marked t h, x⁆ :=
  conjugationCoord_eq_add_lie (by omega) _ x (markedQuotientDirection_double_lie F v w marked t h x)

end Erdos3

end

section

namespace Erdos3

open Module

variable {I ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (hω : ∀ i, ω i ≤ s)

include b hF hω in
theorem markedShiftQuotient_finiteDimensional (t : ℕ) :
    FiniteDimensional ℚ (MarkedShiftQuotient F v w marked t) := by
  let _ := F.associatedDegree.polynomialShift_finiteDimensional b ω hF hω t
  let _ : FiniteDimensional ℚ (markedShiftSubalgebra F v w marked t) :=
    inferInstanceAs (FiniteDimensional ℚ (markedShiftSubalgebra F v w marked t).toSubmodule)
  exact inferInstanceAs
    (FiniteDimensional ℚ ((markedShiftSubalgebra F v w marked t) ⧸
      (markedShiftSecondIdeal F v w marked t).toSubmodule))

include hF hω in
theorem markedShiftQuotient_finrank_le (t : ℕ) :
    finrank ℚ (MarkedShiftQuotient F v w marked t) ≤
      Fintype.card ι * (s + 1) * (t + 1) ^ s + t := by
  let _ := F.associatedDegree.polynomialShift_finiteDimensional b ω hF hω t
  let _ : FiniteDimensional ℚ (markedShiftSubalgebra F v w marked t) :=
    inferInstanceAs (FiniteDimensional ℚ (markedShiftSubalgebra F v w marked t).toSubmodule)
  exact ((markedShiftSecondIdeal F v w marked t).toSubmodule.finrank_quotient_le).trans
    ((markedShiftSubalgebra F v w marked t).toSubmodule.finrank_le.trans
      (F.associatedDegree.polynomialShift_finrank_le b ω hF hω t))

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped BigOperators

variable {I L : Type*} [Fintype I] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)

noncomputable def markedPolynomialGeneratorFamily (t d k l : ℕ)
    (p : finiteMarkedPolynomialValues (σ := Fin t) v w marked s d k l) :
    markedPolynomialLayer (σ := Fin t) v w marked d k l :=
  ⟨p.val, finiteMarkedPolynomialValues_mem v w marked s d k l p.property⟩

include hw hv in
theorem markedPolynomialGeneratorFamily_span (t d k l : ℕ) :
    Submodule.span ℚ (Set.range (markedPolynomialGeneratorFamily (s := s) v w marked t d k l)) = ⊤ := by
  apply (Submodule.span_range_subtype_eq_top_iff _ _).mpr
  have hrange : Set.range (fun p : finiteMarkedPolynomialValues (σ := Fin t) v w marked s d k l =>
      (p.val : VectorPolynomial (Fin t) ℚ L)) =
      (finiteMarkedPolynomialValues (σ := Fin t) v w marked s d k l : Set (VectorPolynomial (Fin t) ℚ L)) := by
    ext p
    exact ⟨fun ⟨q, hq⟩ => hq ▸ q.property, fun hp => ⟨⟨p, hp⟩, rfl⟩⟩
  change Submodule.span ℚ (Set.range (fun p : finiteMarkedPolynomialValues (σ := Fin t) v w marked s d k l =>
    (p.val : VectorPolynomial (Fin t) ℚ L))) = _
  rw [hrange]
  exact (markedPolynomialLayer_eq_finite_span F v w marked hw hv d k l).symm

noncomputable def markedShiftLayerPolynomialMap (t d k l : ℕ) :
    markedPolynomialLayer (σ := Fin t) v w marked d k l →ₗ[ℚ] markedShiftSubalgebra F v w marked t where
  toFun p :=
    let hp := markedPolynomialLayer_antitone v w marked (Nat.zero_le d) (Nat.zero_le k) (Nat.zero_le l) p.property
    ⟨⟨⟨p.val, markedPolynomialAlgebra_le_adapted F v w marked hw hv hp⟩, 0⟩, hp⟩
  map_add' p q := by
    apply Subtype.ext
    apply LieAlgebra.SemiDirectSum.ext
    · apply Subtype.ext
      rfl
    · exact (zero_add (0 : RationalTorus.Algebra t)).symm
  map_smul' c p := by
    apply Subtype.ext
    apply LieAlgebra.SemiDirectSum.ext
    · apply Subtype.ext
      rfl
    · exact (smul_zero c : c • (0 : RationalTorus.Algebra t) = 0).symm

noncomputable def markedShiftDirectionMap (t : ℕ) :
    RationalTorus.Algebra t →ₗ[ℚ] markedShiftSubalgebra F v w marked t where
  toFun u := ⟨⟨0, u⟩, (markedPolynomialLayer v w marked 0 0 0).zero_mem⟩
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl

abbrev MarkedShiftGeneratorIndex (t h n : ℕ) :=
  (finiteMarkedPolynomialValues (σ := Fin t) v w marked s n h 0) ⊕
    {_i : Fin t // n = 0 ∧ h ≤ 1}

noncomputable def markedShiftGenerator (t h n : ℕ) :
    MarkedShiftGeneratorIndex (s := s) v w marked t h n → markedShiftSubalgebra F v w marked t
  | .inl p => markedShiftLayerPolynomialMap F v w marked hw hv t n h 0
      (markedPolynomialGeneratorFamily v w marked t n h 0 p)
  | .inr i => markedShiftDirectionMap F v w marked t (RationalTorus.basis t i.val)

theorem markedShiftGenerator_mem (t h n : ℕ)
    (i : MarkedShiftGeneratorIndex (s := s) v w marked t h n) :
    markedShiftGenerator F v w marked hw hv t h n i ∈ markedShiftBiLayer F v w marked t h n := by
  rcases i with p | i
  · exact ⟨finiteMarkedPolynomialValues_mem v w marked s n h 0 p.property, fun _ => rfl⟩
  · refine ⟨(markedPolynomialLayer v w marked n h 0).zero_mem, ?_⟩
    intro hc
    have hi := i.property
    omega

theorem markedShiftGenerator_span (t h n : ℕ) :
    Submodule.span ℚ (Set.range (markedShiftGenerator F v w marked hw hv t h n)) =
      markedShiftBiLayer F v w marked t h n := by
  classical
  apply le_antisymm
  · exact Submodule.span_le.mpr (fun _ ⟨i, hi⟩ => hi ▸ markedShiftGenerator_mem F v w marked hw hv t h n i)
  · intro x hx
    let S := Submodule.span ℚ (Set.range (markedShiftGenerator F v w marked hw hv t h n))
    have hpoly (p : markedPolynomialLayer (σ := Fin t) v w marked n h 0) :
        markedShiftLayerPolynomialMap F v w marked hw hv t n h 0 p ∈ S := by
      have hp : p ∈ Submodule.span ℚ
          (Set.range (markedPolynomialGeneratorFamily (s := s) v w marked t n h 0)) := by
        rw [markedPolynomialGeneratorFamily_span F v w marked hw hv]
        trivial
      induction hp using Submodule.span_induction with
      | mem q hq =>
        obtain ⟨i, rfl⟩ := hq
        exact Submodule.subset_span ⟨.inl i, rfl⟩
      | zero => rw [map_zero]; exact S.zero_mem
      | add p q _ _ hp hq => rw [map_add]; exact S.add_mem hp hq
      | smul c p _ hp => rw [map_smul]; exact S.smul_mem c hp
    have hdir : markedShiftDirectionMap F v w marked t x.val.right ∈ S := by
      by_cases ha : n = 0 ∧ h ≤ 1
      · rw [← (RationalTorus.basis t).sum_repr x.val.right, map_sum]
        apply S.sum_mem
        intro i _
        rw [map_smul]
        exact S.smul_mem _ (Submodule.subset_span ⟨.inr ⟨i, ha⟩, rfl⟩)
      · rw [hx.2 (by omega), map_zero]
        exact S.zero_mem
    have he : markedShiftLayerPolynomialMap F v w marked hw hv t n h 0 ⟨x.val.left.val, hx.1⟩ +
        markedShiftDirectionMap F v w marked t x.val.right = x := by
      apply Subtype.ext
      apply LieAlgebra.SemiDirectSum.ext
      · apply Subtype.ext
        change x.val.left.val + 0 = x.val.left.val
        exact add_zero _
      · change 0 + x.val.right = x.val.right
        exact zero_add _
    exact he ▸ S.add_mem (hpoly ⟨x.val.left.val, hx.1⟩) hdir

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial NilpotentLieBCHGroup

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t : ℕ)

noncomputable def markedShiftTranslate (h : Fin t → ℚ) :
    markedShiftSubalgebra F v w marked t →ₗ[ℚ] markedShiftSubalgebra F v w marked t where
  toFun x :=
    ⟨⟨⟨translate h x.val.left.val,
        markedPolynomialAlgebra_le_adapted F v w marked hw hv
          (markedPolynomialLayer_translate v w marked h x.property)⟩, x.val.right⟩,
      markedPolynomialLayer_translate v w marked h x.property⟩
  map_add' x y := by
    apply Subtype.ext
    apply LieAlgebra.SemiDirectSum.ext
    · apply Subtype.ext
      exact (VectorPolynomial.translate h).map_add x.val.left.val y.val.left.val
    · rfl
  map_smul' a x := by
    apply Subtype.ext
    apply LieAlgebra.SemiDirectSum.ext
    · apply Subtype.ext
      exact (VectorPolynomial.translate h).map_smul a x.val.left.val
    · rfl

theorem markedShiftTranslate_left (h : Fin t → ℚ) (x : markedShiftSubalgebra F v w marked t) :
    (markedShiftTranslate F v w marked hw hv t h x).val.left.val = translate h x.val.left.val := rfl

theorem markedShiftTranslate_right (h : Fin t → ℚ) (x : markedShiftSubalgebra F v w marked t) :
    (markedShiftTranslate F v w marked hw hv t h x).val.right = x.val.right := rfl

theorem markedShiftEval_translate (h a : Fin t → ℚ) (x : markedShiftSubalgebra F v w marked t) :
    markedShiftEval F v w marked t a (markedShiftTranslate F v w marked hw hv t h x) =
      markedShiftEval F v w marked t (a + h) x :=
  eval_translate h a x.val.left.val

theorem markedShiftTranslate_second_mem (h : Fin t → ℚ) {x : markedShiftSubalgebra F v w marked t}
    (hx : x ∈ markedShiftSecondIdeal F v w marked t) :
    markedShiftTranslate F v w marked hw hv t h x ∈ markedShiftSecondIdeal F v w marked t :=
  ⟨hx.1, markedPolynomialLayer_translate v w marked h hx.2⟩

theorem markedShiftTranslate_first_order (h : Fin t → ℚ) (x : markedShiftSubalgebra F v w marked t) :
    markedShiftTranslate F v w marked hw hv t h x - x - ⁅markedShiftDirection F v w marked t h, x⁆ ∈
      markedShiftSecondIdeal F v w marked t := by
  constructor
  · change x.val.right - x.val.right - (⁅markedShiftDirection F v w marked t h, x⁆).val.right = 0
    rw [markedShiftDirection_lie_right, sub_self, sub_zero]
  · change translate h x.val.left.val - x.val.left.val -
      (⁅markedShiftDirection F v w marked t h, x⁆).val.left.val ∈ _
    rw [markedShiftDirection_lie_left]
    exact markedPolynomialLayer_taylorRemainder v w marked h x.property

theorem markedShiftTranslate_quotient (h : Fin t → ℚ) (x : markedShiftSubalgebra F v w marked t) :
    lieQuotientMap (markedShiftSecondIdeal F v w marked t) (markedShiftTranslate F v w marked hw hv t h x) =
      lieQuotientMap (markedShiftSecondIdeal F v w marked t) x +
        ⁅markedQuotientDirection F v w marked t h, lieQuotientMap (markedShiftSecondIdeal F v w marked t) x⁆ := by
  have he := (lieQuotientMap_eq_zero (markedShiftSecondIdeal F v w marked t)
    (markedShiftTranslate F v w marked hw hv t h x - x - ⁅markedShiftDirection F v w marked t h, x⁆)).mpr
      (markedShiftTranslate_first_order F v w marked hw hv t h x)
  rw [map_sub, map_sub, LieHom.map_lie] at he
  exact (sub_eq_iff_eq_add.mp (sub_eq_zero.mp he)).trans (add_comm _ _)

theorem markedShiftTranslate_conjugation (hs : 1 ≤ s) (h : Fin t → ℚ)
    (x : markedShiftSubalgebra F v w marked t) :
    conjugationCoord (⟨markedQuotientDirection F v w marked t h⟩ : MarkedShiftQuotientGroup F v w marked t)
      (lieQuotientMap (markedShiftSecondIdeal F v w marked t) x) =
        lieQuotientMap (markedShiftSecondIdeal F v w marked t) (markedShiftTranslate F v w marked hw hv t h x) := by
  rw [markedQuotientDirection_conjugation F v w marked t hs]
  exact (markedShiftTranslate_quotient F v w marked hw hv t h x).symm

noncomputable def markedQuotientTranslate (h : Fin t → ℚ) :
    MarkedShiftQuotient F v w marked t →ₗ[ℚ] MarkedShiftQuotient F v w marked t :=
  (markedShiftSecondIdeal F v w marked t).toSubmodule.liftQ
    ((lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.comp
      (markedShiftTranslate F v w marked hw hv t h)) (by
        intro x hx
        exact (lieQuotientMap_eq_zero _ _).mpr (markedShiftTranslate_second_mem F v w marked hw hv t h hx))

theorem markedQuotientTranslate_map (h : Fin t → ℚ) (x : markedShiftSubalgebra F v w marked t) :
    markedQuotientTranslate F v w marked hw hv t h (lieQuotientMap (markedShiftSecondIdeal F v w marked t) x) =
      lieQuotientMap (markedShiftSecondIdeal F v w marked t) (markedShiftTranslate F v w marked hw hv t h x) := rfl

theorem markedQuotientTranslate_first_order (h : Fin t → ℚ) (x : MarkedShiftQuotient F v w marked t) :
    markedQuotientTranslate F v w marked hw hv t h x = x + ⁅markedQuotientDirection F v w marked t h, x⁆ := by
  obtain ⟨z, rfl⟩ := lieQuotientMap_surjective (markedShiftSecondIdeal F v w marked t) x
  exact markedShiftTranslate_quotient F v w marked hw hv t h z

end Erdos3

end

section

namespace Erdos3

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)

noncomputable def markedShiftQuotientLayer (t : ℕ) (a : Fin 2 → ℕ) :
    Submodule ℚ (MarkedShiftQuotient F v w marked t) :=
  (markedShiftBiLayer F v w marked t (a 0) (a 1)).map
    (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap

theorem markedShiftQuotientLayer_antitone (t : ℕ) :
    Antitone (markedShiftQuotientLayer F v w marked t) := by
  intro a b hab
  exact Submodule.map_mono (markedShiftBiLayer_antitone F v w marked t (hab 0) (hab 1))

theorem markedShiftQuotientLayer_zero (t : ℕ) : markedShiftQuotientLayer F v w marked t 0 = ⊤ := by
  change (markedShiftBiLayer F v w marked t 0 0).map _ = ⊤
  rw [markedShiftBiLayer_zero, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (lieQuotientMap_surjective _)

theorem markedShiftQuotientLayer_lie_mem (t : ℕ) {a b : Fin 2 → ℕ}
    {x y : MarkedShiftQuotient F v w marked t}
    (hx : x ∈ markedShiftQuotientLayer F v w marked t a)
    (hy : y ∈ markedShiftQuotientLayer F v w marked t b) :
    ⁅x, y⁆ ∈ markedShiftQuotientLayer F v w marked t (a + b) := by
  obtain ⟨p, hp, rfl⟩ := hx
  obtain ⟨q, hq, rfl⟩ := hy
  exact ⟨⁅p, q⁆, markedShiftBiLayer_lie_mem F v w marked t hp hq,
    (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).map_lie p q⟩

theorem markedShiftQuotientLayer_eq_bot_of_le (t : ℕ) (a : Fin 2 → ℕ)
    (ha : markedShiftBiLayer F v w marked t (a 0) (a 1) ≤
      (markedShiftSecondIdeal F v w marked t).toSubmodule) :
    markedShiftQuotientLayer F v w marked t a = ⊥ := by
  apply bot_unique
  rintro x ⟨y, hy, rfl⟩
  exact (lieQuotientMap_eq_zero _ y).mpr (ha hy)

theorem markedShiftQuotientLayer_terminal
    (hv : ∀ i, v i ∈ F.layer (w i) 1) (t : ℕ) (a : Fin 2 → ℕ)
    (ha : ¬a ≤ mixedCorrelationDegree s) : markedShiftQuotientLayer F v w marked t a = ⊥ := by
  have hnot : ¬(a 0 ≤ 1 ∧ a 1 ≤ s) := by
    intro h
    apply ha
    intro i
    fin_cases i
    · exact h.1
    · exact h.2
  have hcases : 1 < a 0 ∨ s < a 1 := by omega
  rcases hcases with hh | hn
  · apply markedShiftQuotientLayer_eq_bot_of_le F v w marked t a
    exact (markedShiftBiLayer_antitone F v w marked t (by omega : 2 ≤ a 0) (Nat.zero_le _)).trans
      (markedShiftBiLayer_second F v w marked t).le
  · have hzero : markedShiftBiLayer F v w marked t (a 0) (a 1) = ⊥ := by
      apply bot_unique
      exact (markedShiftBiLayer_antitone F v w marked t le_rfl (by omega : s + 1 ≤ a 1)).trans
        (markedShiftBiLayer_degree_terminal F v w marked hv t (a 0)).le
    unfold markedShiftQuotientLayer
    rw [hzero, Submodule.map_bot]

theorem markedShiftQuotientLayer_positive (hw : ∀ i, 0 < w i) (t : ℕ) :
    markedShiftQuotientLayer F v w marked t (correlationInput 0 1) ⊔
      markedShiftQuotientLayer F v w marked t (correlationInput 1 0) = ⊤ := by
  change (markedShiftBiLayer F v w marked t 0 1).map _ ⊔
    (markedShiftBiLayer F v w marked t 1 0).map _ = ⊤
  rw [← Submodule.map_sup, markedShiftBiLayer_positive F v w marked hw t, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (lieQuotientMap_surjective _)

theorem markedShiftQuotientLayer_total_one (hw : ∀ i, 0 < w i) (t : ℕ) :
    multidegreeTotalLayer (markedShiftQuotientLayer F v w marked t) 1 = ⊤ := by
  apply top_unique
  rw [← markedShiftQuotientLayer_positive F v w marked hw t]
  apply sup_le
  · apply layer_le_multidegreeTotalLayer _ (correlationInput 0 1) 1
    decide
  · apply layer_le_multidegreeTotalLayer _ (correlationInput 1 0) 1
    decide

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial

variable {I σ ι L : Type*} [Fintype I] [Fintype σ] [Fintype ι]
  [LieRing L] [LieAlgebra ℚ L]

theorem finiteMarkedPolynomialValues_coefficient_height
    (b : Basis ι ℚ L) (v : I → L) (w : I → ℕ) (marked : I → Bool) {H : ℕ} (hH : 1 ≤ H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
    (hv : ∀ i j, RationalHeightLE (b.repr (v i) j) H) (s d k l : ℕ)
    {p : VectorPolynomial σ ℚ L} (hp : p ∈ finiteMarkedPolynomialValues v w marked s d k l)
    (α : σ →₀ ℕ) (j : ι) :
    RationalHeightLE (b.repr (coefficients p α) j) (lieTreeHeight (Fintype.card ι) H s) := by
  classical
  obtain ⟨β, _, hβ⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hβ
  rw [coefficients_monomial]
  by_cases h : β = α
  · subst β
    rw [Finsupp.single_eq_same]
    exact finiteMarkedLieValues_coordinate_height b v w marked hc hv s d _ l hx j
  · rw [Finsupp.single_eq_of_ne (Ne.symm h), map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero (hH.trans (lieTreeHeight_ge_input _ _ _))

variable {s r : ℕ} (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (v : I → L) (w : I → ℕ) (marked : I → Bool) (hw : ∀ i, 0 < w i)
  (hv : ∀ i, v i ∈ F.layer (w i) 1) {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
  (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)

omit [Fintype σ] in
include hH hc hgen in
theorem markedShiftGenerator_coordinate_height (t h n : ℕ)
    (i : MarkedShiftGeneratorIndex (s := s) v w marked t h n)
    (j : NilpotentLieFiltration.AdaptedBasisIndex (fun _ : Fin t => 1) ω ⊕ Fin t) :
    RationalHeightLE ((F.associatedDegree.polynomialShiftBasis b ω hF t).repr
      (markedShiftGenerator F v w marked hw hv t h n i).val j)
      (lieTreeHeight (Fintype.card ι) H s) := by
  have hbound := hH.trans (lieTreeHeight_ge_input (Fintype.card ι) H s)
  rcases i with p | i
  · rcases j with z | j
    · rw [F.associatedDegree.polynomialShiftBasis_repr_inl]
      exact finiteMarkedPolynomialValues_coefficient_height b v w marked hH hc hgen s n h 0
        p.property z.val.1 z.val.2
    · rw [F.associatedDegree.polynomialShiftBasis_repr_inr]
      exact rationalHeightLE_zero hbound
  · rcases j with z | j
    · rw [F.associatedDegree.polynomialShiftBasis_repr_inl]
      change RationalHeightLE (b.repr (coefficients (0 : VectorPolynomial (Fin t) ℚ L) z.val.1) z.val.2) _
      simp only [map_zero, Finsupp.zero_apply]
      exact rationalHeightLE_zero hbound
    · rw [F.associatedDegree.polynomialShiftBasis_repr_inr]
      change RationalHeightLE ((RationalTorus.basis t).repr (RationalTorus.basis t i.val) j) _
      exact (basis_repr_height_one (RationalTorus.basis t) i.val j).mono hbound

omit [Fintype σ] in
include hw hv hH hc hgen in
theorem exists_markedShiftLayer_bounded_basis (hω : ∀ i, ω i ≤ s) (t h n : ℕ) :
    ∃ e : Basis (Fin (finrank ℚ (markedShiftBiLayer F v w marked t h n))) ℚ
        (markedShiftBiLayer F v w marked t h n),
      ∀ i j, RationalHeightLE ((F.associatedDegree.polynomialShiftBasis b ω hF t).repr
        (e i).val.val j) (lieTreeHeight (Fintype.card ι) H s) := by
  let _ := F.associatedDegree.polynomialShift_finiteDimensional b ω hF hω t
  let _ : FiniteDimensional ℚ (markedShiftSubalgebra F v w marked t) :=
    inferInstanceAs (FiniteDimensional ℚ (markedShiftSubalgebra F v w marked t).toSubmodule)
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ
    (Set.range (markedShiftGenerator F v w marked hw hv t h n))
  rw [markedShiftGenerator_span] at hex
  obtain ⟨z, hz, hzspan, hzli⟩ := hex
  refine ⟨(Basis.span hzli).map (LinearEquiv.ofEq _ _ hzspan), ?_⟩
  intro i j
  simp only [Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.coe_span_apply]
  obtain ⟨k, hk⟩ := hz i
  rw [← hk]
  exact markedShiftGenerator_coordinate_height F b ω hF v w marked hw hv hH hc hgen t h n k j

end Erdos3

end

end OAI
