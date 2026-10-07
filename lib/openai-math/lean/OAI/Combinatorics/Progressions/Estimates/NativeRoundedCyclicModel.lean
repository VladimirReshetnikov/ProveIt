import OAI.Combinatorics.Progressions.Geometry.RoundedGraphCyclicCoordinates
import OAI.Combinatorics.Progressions.Lattices.CyclicModelAffineBox
import OAI.Combinatorics.Progressions.Lattices.NativeProperAffineRecovery

namespace OAI

section

namespace Erdos3.FreimanModel

open scoped Pointwise

theorem exists_dense_cyclicProduct_model {I : Type*} [Fintype I]
    (q : I → ℕ) [∀ i, NeZero (q i)] (A : Finset (∀ i, ZMod (q i)))
    (hA : A.Nonempty) {K : ℝ} (hK : 0 < K)
    (hsmall : ((A - A).card : ℝ) ≤ K * A.card) :
    ∃ (N : ℕ) (J : Finset (∀ i, ZMod (q i))) (B : Finset (ZMod N))
      (f : (∀ i, ZMod (q i)) → ZMod N),
      0 < N ∧ J.Nonempty ∧ J ⊆ A ∧
      A.card ≤ 16 ^ (Fintype.card I + 1) * J.card ∧
      B.Nonempty ∧ B = J.image f ∧ B.card = J.card ∧
      IsAddFreimanIso 8 (J : Set _) (B : Set _) f ∧
      (N : ℝ) ≤ 2 * (K * 16 ^ Fintype.card I) ^ 16 * A.card ∧
      (32 * (K * 16 ^ Fintype.card I) ^ 16)⁻¹ ≤ (B.card : ℝ) / N := by
  classical
  obtain ⟨A₀, hA₀, hA₀A, hlarge, he⟩ := exists_large_cyclicProduct_integer_lift q A hA
  let e := cyclicProductLift q
  let X := A₀.image e
  let R : ℝ := K * 16 ^ Fintype.card I
  have hR : 0 < R := mul_pos hK (by positivity)
  have hX : X.Nonempty := hA₀.image e
  have hXcard : X.card = A₀.card := Finset.card_image_of_injOn he.bijOn.injOn
  have hdiff : (X - X).card = (A₀ - A₀).card :=
    card_difference_image_of_freiman A₀ e (he.mono (hmn := by decide))
  have hsub : A₀ - A₀ ⊆ A - A := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hx
    exact Finset.mem_sub.mpr ⟨a, hA₀A ha, b, hA₀A hb, rfl⟩
  have hlargeR : (A.card : ℝ) ≤ 16 ^ Fintype.card I * A₀.card := by
    exact_mod_cast hlarge
  have hXsmall : ((X - X).card : ℝ) ≤ R * X.card := by
    rw [hdiff, hXcard]
    calc
      ((A₀ - A₀).card : ℝ) ≤ (A - A).card := by exact_mod_cast Finset.card_le_card hsub
      _ ≤ K * A.card := hsmall
      _ ≤ K * (16 ^ Fintype.card I * A₀.card) := mul_le_mul_of_nonneg_left hlargeR hK.le
      _ = R * A₀.card := by simp only [R, mul_assoc]
  obtain ⟨N, X', B, g, hN, hX', hX'X, hsize, hB, hBimage, hBcard, hg, hNsize, hdensity⟩ :=
    exists_dense_cyclic_model_of_integer_vectors X hX hR hXsmall 8 (by decide)
  let J := A₀.filter fun x => e x ∈ X'
  have hJA₀ : J ⊆ A₀ := Finset.filter_subset _ _
  have hJimage : J.image e = X' := by
    ext z
    constructor
    · intro hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp hx).2
    · intro hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hX'X hz)
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hz⟩, rfl⟩
  have heJ : IsAddFreimanIso 8 (J : Set _) (X' : Set (I → ℤ)) e := by
    apply he.subset hJA₀
    refine ⟨?_, he.bijOn.injOn.mono hJA₀, ?_⟩
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
    · intro z hz
      rw [← hJimage] at hz
      exact Finset.mem_image.mp hz
  have hJcard : X'.card = J.card := by
    rw [← hJimage]
    exact Finset.card_image_of_injOn heJ.bijOn.injOn
  have hJ : J.Nonempty := by
    apply Finset.card_pos.mp
    rw [← hJcard]
    exact hX'.card_pos
  have hsize₀ : A₀.card ≤ 16 * J.card := by
    simpa only [hXcard, hJcard, Nat.reduceMul] using hsize
  have hsize' : A.card ≤ 16 ^ (Fintype.card I + 1) * J.card := by
    calc
      A.card ≤ 16 ^ Fintype.card I * A₀.card := hlarge
      _ ≤ 16 ^ Fintype.card I * (16 * J.card) := Nat.mul_le_mul_left _ hsize₀
      _ = _ := by rw [pow_succ, mul_assoc]
  have hBimage' : B = J.image (g ∘ e) := by
    rw [hBimage, ← hJimage, Finset.image_image]
  have hNsize' : (N : ℝ) ≤ 2 * R ^ 16 * A.card := by
    have hcard : (X.card : ℝ) ≤ A.card := by rw [hXcard]; exact_mod_cast Finset.card_le_card hA₀A
    have hn : (N : ℝ) ≤ 2 * R ^ 16 * X.card := by
      simpa only [Nat.reduceMul] using hNsize
    exact hn.trans
      (mul_le_mul_of_nonneg_left hcard (by positivity))
  refine ⟨N, J, B, g ∘ e, hN, hJ, hJA₀.trans hA₀A, hsize', hB, hBimage',
    hBcard.trans hJcard, hg.comp heJ, hNsize', ?_⟩
  norm_num only [Nat.reduceMul, Nat.cast_ofNat, mul_one] at hdensity
  simpa only [R, show (4 : ℝ) * 8 = 32 by norm_num] using hdensity

end Erdos3.FreimanModel

end

section

namespace Erdos3.FreimanModel

open scoped Pointwise

theorem exists_cyclicProduct_model_with_fourfold_lift {I : Type*} [Fintype I]
    (q : I → ℕ) [∀ i, NeZero (q i)] (A : Finset (∀ i, ZMod (q i)))
    (hA : A.Nonempty) {K : ℝ} (hK : 0 < K)
    (hsmall : ((A - A).card : ℝ) ≤ K * A.card) :
    ∃ (N : ℕ) (J : Finset (∀ i, ZMod (q i))) (B : Finset (ZMod N))
      (f : (∀ i, ZMod (q i)) → ZMod N) (L : ZMod N → (∀ i, ZMod (q i))),
      0 < N ∧ J.Nonempty ∧ J ⊆ A ∧
      A.card ≤ 16 ^ (Fintype.card I + 1) * J.card ∧
      B.Nonempty ∧ B = J.image f ∧ B.card = J.card ∧
      IsAddFreimanIso 8 (J : Set _) (B : Set _) f ∧
      (N : ℝ) ≤ 2 * (K * 16 ^ Fintype.card I) ^ 16 * A.card ∧
      (32 * (K * 16 ^ Fintype.card I) ^ 16)⁻¹ ≤ (B.card : ℝ) / N ∧
      Set.MapsTo L (2 • B - 2 • B : Finset _) (2 • J - 2 • J : Finset _) ∧
      Set.InjOn L (2 • B - 2 • B : Finset _) ∧ L 0 = 0 ∧
      ∀ x ∈ 2 • B - 2 • B, ∀ y ∈ 2 • B - 2 • B,
        ∀ z ∈ 2 • B - 2 • B, ∀ w ∈ 2 • B - 2 • B,
          L x + L y = L z + L w ↔ x + y = z + w := by
  obtain ⟨N, J, B, f, hN, hJ, hJA, hsize, hB, hBimage, hBcard, hf, hNsize, hdensity⟩ :=
    exists_dense_cyclicProduct_model q A hA hK hsmall
  obtain ⟨L, hmap, hinj, hzero, hadd⟩ := exists_fourfold_lift_of_eight_iso J B hB f hf
  exact ⟨N, J, B, f, L, hN, hJ, hJA, hsize, hB, hBimage, hBcard, hf,
    hNsize, hdensity, hmap, hinj, hzero, hadd⟩

end Erdos3.FreimanModel

end

section

namespace Erdos3.FreimanModel

open scoped Pointwise

theorem exists_roundedGraph_cyclic_model {I : Type*} [Fintype I]
    (N M : ℕ) [NeZero N] [NeZero M] (A : Finset (ZMod N × (I → ZMod M)))
    (hA : A.Nonempty) {K : ℝ} (hK : 0 < K)
    (hsmall : ((A - A).card : ℝ) ≤ K * A.card) :
    ∃ (Q : ℕ) (J : Finset (ZMod N × (I → ZMod M))) (B : Finset (ZMod Q))
      (f : (ZMod N × (I → ZMod M)) → ZMod Q) (L : ZMod Q → (ZMod N × (I → ZMod M))),
      0 < Q ∧ J.Nonempty ∧ J ⊆ A ∧
      A.card ≤ 16 ^ (Fintype.card I + 2) * J.card ∧
      B.Nonempty ∧ B = J.image f ∧ B.card = J.card ∧
      IsAddFreimanIso 8 (J : Set _) (B : Set _) f ∧
      (Q : ℝ) ≤ 2 * (K * 16 ^ (Fintype.card I + 1)) ^ 16 * A.card ∧
      (32 * (K * 16 ^ (Fintype.card I + 1)) ^ 16)⁻¹ ≤ (B.card : ℝ) / Q ∧
      Set.MapsTo L (2 • B - 2 • B : Finset _) (2 • J - 2 • J : Finset _) ∧
      Set.InjOn L (2 • B - 2 • B : Finset _) ∧ L 0 = 0 ∧
      ∀ x ∈ 2 • B - 2 • B, ∀ y ∈ 2 • B - 2 • B,
        ∀ z ∈ 2 • B - 2 • B, ∀ w ∈ 2 • B - 2 • B,
          L x + L y = L z + L w ↔ x + y = z + w := by
  classical
  let q : Option I → ℕ := roundedGraphModuli N M
  let _ : ∀ i, NeZero (q i) := roundedGraphModuli_neZero N M
  let e := roundedGraphCoordinateEquiv (I := I) N M
  let X := A.image e
  have he : IsAddFreimanIso 8 (A : Set _) (X : Set _) e :=
    isAddFreimanIso_of_injOn_iterated_sums e.toAddMonoidHom A 8
      e.injective.injOn e.injective.injOn
  have hX : X.Nonempty := hA.image e
  have hXcard : X.card = A.card := Finset.card_image_of_injOn e.injective.injOn
  have hXsmall : ((X - X).card : ℝ) ≤ K * X.card := by
    rw [card_difference_image_of_freiman A e (he.mono (hmn := by decide)), hXcard]
    exact hsmall
  obtain ⟨Q, X', B, g, hQ, hX', hX'X, hsize, hB, hBimage, hBcard, hg, hQsize, hdensity⟩ :=
    exists_dense_cyclicProduct_model q X hX hK hXsmall
  let J := A.filter fun x => e x ∈ X'
  have hJA : J ⊆ A := Finset.filter_subset _ _
  have hJimage : J.image e = X' := by
    ext z
    constructor
    · intro hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp hx).2
    · intro hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hX'X hz)
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hz⟩, rfl⟩
  have heJ : IsAddFreimanIso 8 (J : Set _) (X' : Set _) e := by
    apply he.subset hJA
    refine ⟨?_, e.injective.injOn, ?_⟩
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
    · intro z hz
      rw [← hJimage] at hz
      exact Finset.mem_image.mp hz
  have hJcard : X'.card = J.card := by
    rw [← hJimage]
    exact Finset.card_image_of_injOn e.injective.injOn
  have hJ : J.Nonempty := by
    apply Finset.card_pos.mp
    rw [← hJcard]
    exact hX'.card_pos
  have hf : IsAddFreimanIso 8 (J : Set _) (B : Set _) (g ∘ e) := hg.comp heJ
  obtain ⟨L, hmap, hinj, hzero, hadd⟩ := exists_fourfold_lift_of_eight_iso J B hB (g ∘ e) hf
  refine ⟨Q, J, B, g ∘ e, L, hQ, hJ, hJA, ?_, hB, ?_, hBcard.trans hJcard,
    hf, ?_, ?_, hmap, hinj, hzero, hadd⟩
  · simpa only [Fintype.card_option, hXcard, hJcard, Nat.add_assoc] using hsize
  · rw [hBimage, ← hJimage, Finset.image_image]
  · simpa only [Fintype.card_option, hXcard] using hQsize
  · simpa only [Fintype.card_option] using hdensity

end Erdos3.FreimanModel

end

section

namespace Erdos3.FreimanModel

open scoped Pointwise

theorem exists_variableRoundedGraph_cyclic_model {I : Type*} [Fintype I]
    (N : ℕ) (M : I → ℕ) [NeZero N] [∀ i, NeZero (M i)] (A : Finset (ZMod N × (∀ i, ZMod (M i))))
    (hA : A.Nonempty) {K : ℝ} (hK : 0 < K)
    (hsmall : ((A - A).card : ℝ) ≤ K * A.card) :
    ∃ (Q : ℕ) (J : Finset (ZMod N × (∀ i, ZMod (M i)))) (B : Finset (ZMod Q))
      (f : (ZMod N × (∀ i, ZMod (M i))) → ZMod Q) (L : ZMod Q → (ZMod N × (∀ i, ZMod (M i)))),
      0 < Q ∧ J.Nonempty ∧ J ⊆ A ∧
      A.card ≤ 16 ^ (Fintype.card I + 2) * J.card ∧
      B.Nonempty ∧ B = J.image f ∧ B.card = J.card ∧
      IsAddFreimanIso 8 (J : Set _) (B : Set _) f ∧
      (Q : ℝ) ≤ 2 * (K * 16 ^ (Fintype.card I + 1)) ^ 16 * A.card ∧
      (32 * (K * 16 ^ (Fintype.card I + 1)) ^ 16)⁻¹ ≤ (B.card : ℝ) / Q ∧
      Set.MapsTo L (2 • B - 2 • B : Finset _) (2 • J - 2 • J : Finset _) ∧
      Set.InjOn L (2 • B - 2 • B : Finset _) ∧ L 0 = 0 ∧
      ∀ x ∈ 2 • B - 2 • B, ∀ y ∈ 2 • B - 2 • B,
        ∀ z ∈ 2 • B - 2 • B, ∀ w ∈ 2 • B - 2 • B,
          L x + L y = L z + L w ↔ x + y = z + w := by
  classical
  let q : Option I → ℕ := variableRoundedGraphModuli N M
  let _ : ∀ i, NeZero (q i) := variableRoundedGraphModuli_neZero N M
  let e := variableRoundedGraphCoordinateEquiv (I := I) N M
  let X := A.image e
  have he : IsAddFreimanIso 8 (A : Set _) (X : Set _) e :=
    isAddFreimanIso_of_injOn_iterated_sums e.toAddMonoidHom A 8
      e.injective.injOn e.injective.injOn
  have hX : X.Nonempty := hA.image e
  have hXcard : X.card = A.card := Finset.card_image_of_injOn e.injective.injOn
  have hXsmall : ((X - X).card : ℝ) ≤ K * X.card := by
    rw [card_difference_image_of_freiman A e (he.mono (hmn := by decide)), hXcard]
    exact hsmall
  obtain ⟨Q, X', B, g, hQ, hX', hX'X, hsize, hB, hBimage, hBcard, hg, hQsize, hdensity⟩ :=
    exists_dense_cyclicProduct_model q X hX hK hXsmall
  let J := A.filter fun x => e x ∈ X'
  have hJA : J ⊆ A := Finset.filter_subset _ _
  have hJimage : J.image e = X' := by
    ext z
    constructor
    · intro hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp hx).2
    · intro hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hX'X hz)
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hz⟩, rfl⟩
  have heJ : IsAddFreimanIso 8 (J : Set _) (X' : Set _) e := by
    apply he.subset hJA
    refine ⟨?_, e.injective.injOn, ?_⟩
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
    · intro z hz
      rw [← hJimage] at hz
      exact Finset.mem_image.mp hz
  have hJcard : X'.card = J.card := by
    rw [← hJimage]
    exact Finset.card_image_of_injOn e.injective.injOn
  have hJ : J.Nonempty := by
    apply Finset.card_pos.mp
    rw [← hJcard]
    exact hX'.card_pos
  have hf : IsAddFreimanIso 8 (J : Set _) (B : Set _) (g ∘ e) := hg.comp heJ
  obtain ⟨L, hmap, hinj, hzero, hadd⟩ := exists_fourfold_lift_of_eight_iso J B hB (g ∘ e) hf
  refine ⟨Q, J, B, g ∘ e, L, hQ, hJ, hJA, ?_, hB, ?_, hBcard.trans hJcard,
    hf, ?_, ?_, hmap, hinj, hzero, hadd⟩
  · simpa only [Fintype.card_option, hXcard, hJcard, Nat.add_assoc] using hsize
  · rw [hBimage, ← hJimage, Finset.image_image]
  · simpa only [Fintype.card_option, hXcard] using hQsize
  · simpa only [Fintype.card_option] using hdensity

end Erdos3.FreimanModel

end

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped Pointwise
open CyclicCrootSisask

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem variable_graph_affine_model {I : Type*} [Fintype I]
    (a : ZMod N → I → ℝ) (c : I → ℝ) (M l : I → ℕ) [∀ i, NeZero (M i)] (ε : I → ℝ)
    (hsmall : ∀ i, (M i : ℝ) * l i * ε i ≤ 1)
    (hnear : ∀ t ∈ D.quadruples, ∃ q ∈ coordinateDenominatorGrid l,
      ∀ i, |c i + (a (rankQuadrupleParameters t 1) i + a (rankQuadrupleParameters t 2) i -
        a (rankQuadrupleParameters t 0) i - a (rankQuadrupleParameters t 3) i) - q i| ≤ ε i) :
    let K := Real.exp (P + 13 * Fintype.card I)
    let z := roundedModelLogBudget P (Fintype.card I)
    let δ := Real.exp (-(quarticBogolyubovProgressionConstant * (z + 1) ^ 8))
    let v := fun h => variableRoundedCoefficient M l (a h)
    ∃ J' ⊆ H, J'.Nonempty ∧
      δ * ((2 ^ 4 : ℝ)⁻¹ * K⁻¹ * H.card) ≤ 16 ^ (Fintype.card I + 2) * (J'.card : ℝ) ∧
      ∃ (r : ℕ) (R : Fin r → ℕ)
        (Φ : (Fin r → ℤ) →+ (ZMod N × (∀ i, ZMod (M i))))
        (base : ZMod N × (∀ i, ZMod (M i))),
        (r : ℝ) ≤ 2 + quarticBogolyubovConstant * (z + 1) ^ 4 ∧
        Set.InjOn Φ {x | ∀ i, |x i| ≤ (R i : ℤ)} ∧
        ∀ h ∈ J', ∃ x : Fin r → ℤ,
          (∀ i, |x i| ≤ (R i : ℤ)) ∧ (h, v h) = base + Φ x := by
  intro K z δ v
  classical
  obtain ⟨J, hJH, hJ, hsize, hsmallJ⟩ :=
    D.variable_graph_small_difference a c M l ε hsmall hnear
  let A := additiveGraph J v
  have hA : A.Nonempty := hJ.image _
  have hAsmall : ((A - A).card : ℝ) ≤ (2 ^ 14 : ℝ) * K ^ 6 * A.card := by
    simpa only [A, additiveGraph_card] using hsmallJ
  obtain ⟨Q, S, B, f, _L, hQ, hS, hSA, hASsize, hB, _hBimage, _hBcard, hf,
      _hQsize, hdensity, _hmap, _hinj, _hzero, _hadd⟩ :=
    FreimanModel.exists_variableRoundedGraph_cyclic_model N M A hA
      (by dsimp [K]; positivity) hAsmall
  let _ : NeZero Q := ⟨hQ.ne'⟩
  have hdensity' : Real.exp (-z) * Q ≤ (B.card : ℝ) := by
    apply (le_div_iff₀ (by exact_mod_cast hQ : (0 : ℝ) < Q)).mp
    exact (exp_neg_roundedModelLogBudget_le_density P (Fintype.card I)).trans hdensity
  obtain ⟨F, hFS, hF, hFsize, r, R, Φ, base, hrank, hinj, hrepr⟩ :=
    FreimanModel.exists_affine_box_of_cyclic_model S hS B hB f hf
      (roundedModelLogBudget_nonneg P (Fintype.card I)) hdensity'
  have hFA : F ⊆ A := hFS.trans hSA
  let J' := F.image Prod.fst
  have hgraph : additiveGraph J' v = F := additiveGraph_image_fst J v F hFA
  have hFcard : F.card = J'.card := by rw [← hgraph, additiveGraph_card]
  have hJ' : J' ⊆ H := by
    intro h hh
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hh
    exact hJH ((mem_additiveGraph_iff J v y).mp (hFA hy)).1
  have hJS : (J.card : ℝ) ≤ 16 ^ (Fintype.card I + 2) * (S.card : ℝ) := by
    have h : J.card ≤ 16 ^ (Fintype.card I + 2) * S.card := by
      simpa only [A, additiveGraph_card] using hASsize
    exact_mod_cast h
  have hretain : δ * (S.card : ℝ) ≤ (J'.card : ℝ) := by
    simpa only [hFcard] using hFsize
  refine ⟨J', hJ', hF.image _, ?_, r, R, Φ, base, hrank, hinj, ?_⟩
  · calc
      _ ≤ δ * (J.card : ℝ) := mul_le_mul_of_nonneg_left hsize (Real.exp_pos _).le
      _ ≤ δ * (16 ^ (Fintype.card I + 2) * (S.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hJS (Real.exp_pos _).le
      _ = 16 ^ (Fintype.card I + 2) * (δ * S.card) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hretain (by positivity)
  · intro h hh
    apply hrepr (h, v h)
    rw [← hgraph, mem_additiveGraph_iff]
    exact ⟨hh, rfl⟩

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped Pointwise

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem rounded_graph_cyclic_model {I : Type*} [Fintype I]
    (a : ZMod N → I → ℝ) (c : I → ℝ) (M l : ℕ) [NeZero M] {ε : ℝ}
    (hsmall : (M : ℝ) * l * ε ≤ 1)
    (hnear : ∀ t ∈ D.quadruples, ∃ q ∈ realDenominatorGrid l,
      ‖c + (a (rankQuadrupleParameters t 1) + a (rankQuadrupleParameters t 2) -
        a (rankQuadrupleParameters t 0) - a (rankQuadrupleParameters t 3)) - q‖ ≤ ε) :
    let K := Real.exp (P + 13 * Fintype.card I)
    let C := (2 ^ 14 : ℝ) * K ^ 6 * 16 ^ (Fintype.card I + 1)
    let v := fun h => roundedCoefficient M l (a h)
    ∃ J ⊆ H, J.Nonempty ∧
      (2 ^ 4 : ℝ)⁻¹ * K⁻¹ * H.card ≤ 16 ^ (Fintype.card I + 2) * (J.card : ℝ) ∧
      ∃ (Q : ℕ) (B : Finset (ZMod Q))
        (f : (ZMod N × (I → ZMod M)) → ZMod Q)
        (L : ZMod Q → (ZMod N × (I → ZMod M))),
        0 < Q ∧ B.Nonempty ∧ B = (additiveGraph J v).image f ∧ B.card = J.card ∧
        IsAddFreimanIso 8 (additiveGraph J v : Set _) (B : Set _) f ∧
        (Q : ℝ) ≤ 2 * C ^ 16 * H.card ∧ (32 * C ^ 16)⁻¹ ≤ (B.card : ℝ) / Q ∧
        Set.MapsTo L (2 • B - 2 • B : Finset _)
          (2 • additiveGraph J v - 2 • additiveGraph J v : Finset _) ∧
        Set.InjOn L (2 • B - 2 • B : Finset _) ∧ L 0 = 0 ∧
        ∀ x ∈ 2 • B - 2 • B, ∀ y ∈ 2 • B - 2 • B,
          ∀ z ∈ 2 • B - 2 • B, ∀ w ∈ 2 • B - 2 • B,
            L x + L y = L z + L w ↔ x + y = z + w := by
  intro K C v
  classical
  obtain ⟨J₀, hJ₀H, hJ₀, hlarge, hdiff⟩ := D.rounded_graph_small_difference a c M l hsmall hnear
  let A := additiveGraph J₀ v
  have hA : A.Nonempty := hJ₀.image _
  have hK₀ : (0 : ℝ) < (2 ^ 14 : ℝ) * K ^ 6 := by
    dsimp [K]
    positivity
  have hdiff' : ((A - A).card : ℝ) ≤ (2 ^ 14 : ℝ) * K ^ 6 * A.card := by
    simpa only [A, additiveGraph_card] using hdiff
  obtain ⟨Q, S, B, f, L, hQ, hS, hSA, hsize, hB, hBimage, hBcard, hf,
      hQsize, hdensity, hmap, hinj, hzero, hadd⟩ :=
    FreimanModel.exists_roundedGraph_cyclic_model N M A hA hK₀ hdiff'
  let J := S.image Prod.fst
  have hgraph : additiveGraph J v = S := additiveGraph_image_fst J₀ v S hSA
  have hcard : S.card = J.card := by rw [← hgraph, additiveGraph_card]
  have hJH : J ⊆ H := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact hJ₀H ((mem_additiveGraph_iff J₀ v y).mp (hSA hy)).1
  have hsizeR : (J₀.card : ℝ) ≤ 16 ^ (Fintype.card I + 2) * (J.card : ℝ) := by
    have hh : J₀.card ≤ 16 ^ (Fintype.card I + 2) * J.card := by
      simpa only [A, additiveGraph_card, hcard] using hsize
    exact_mod_cast hh
  have hQsize' : (Q : ℝ) ≤ 2 * C ^ 16 * H.card := by
    have hh : (A.card : ℝ) ≤ H.card := by
      rw [show A.card = J₀.card from additiveGraph_card J₀ v]
      exact_mod_cast Finset.card_le_card hJ₀H
    exact hQsize.trans (mul_le_mul_of_nonneg_left hh (by positivity))
  refine ⟨J, hJH, hS.image _, hlarge.trans hsizeR, Q, B, f, L, hQ, hB, ?_,
    hBcard.trans hcard, ?_, hQsize', hdensity, ?_, hinj, hzero, hadd⟩
  · simpa only [hgraph] using hBimage
  · simpa only [hgraph] using hf
  · simpa only [hgraph] using hmap

end Erdos3.NativeRankRelation.CommonData

end

end OAI
