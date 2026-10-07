/- Modified for ProveIt: Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Combinatorics.Progressions.Estimates.ShiftedVerticalExpansion

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open scoped TensorProduct NNReal

variable {L I σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {T : Subgroup D.RealGroup} {p : ℝ}
  (V : D.UnitVerticalObservable T I p)

noncomputable def coordinateProduct (i j : I) (x : D.Space) : ℂ :=
  V.observable i x * star (V.observable j x)

theorem coordinateProduct_norm (i j : I) (x : D.Space) :
    ‖V.coordinateProduct i j x‖ ≤ 1 := by
  simpa only [coordinateProduct, norm_mul, norm_star, mul_one] using
    mul_le_mul (V.norm i x) (V.norm j x) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

theorem coordinateProduct_lipschitz (i j : I) :
    letI := D.metricSpace
    LipschitzWith (2 * V.lipBound) (V.coordinateProduct i j) := by
  let := D.metricSpace
  exact (lipschitz_mul_star_of_bounds (V.observable i) (V.observable j)
    (Bf := 1) (Bg := 1) (V.lipschitz i) (V.lipschitz j) (V.norm i) (V.norm j)).weaken
      (by simp only [one_mul, two_mul]; exact le_rfl)

theorem coordinateProduct_invariant (i j : I) (z : D.RealGroup) (hz : z ∈ T) (x : D.Space) :
    V.coordinateProduct i j (z • x) = V.coordinateProduct i j x := by
  let c := CircleFourier.character ((realifyFunctional V.frequency z.coord : ℝ) : CircleFourier.Circle)
  have hc : c * star c = 1 := by
    change CircleFourier.character ((realifyFunctional V.frequency z.coord : ℝ) : CircleFourier.Circle) *
      star (CircleFourier.character ((realifyFunctional V.frequency z.coord : ℝ) : CircleFourier.Circle)) = 1
    rw [← CircleFourier.character_neg, ← CircleFourier.character_add,
      add_neg_cancel, CircleFourier.character_zero]
  unfold coordinateProduct
  rw [V.vertical i z hz, V.vertical j z hz, star_mul]
  change (c * V.observable i x) * (star (V.observable j x) * star c) = _
  calc
    _ = (c * star c) * (V.observable i x * star (V.observable j x)) := by ring
    _ = _ := by rw [hc, one_mul]

noncomputable def productNiltest {w : σ → ℕ}
    (g : D.filtration.realification.PolynomialOrbit w) (i j : I) : D.Niltest w where
  orbit := g
  observable := V.coordinateProduct i j
  normBound := 1
  lipBound := 2 * V.lipBound
  norm_le := V.coordinateProduct_norm i j
  lipschitz := V.coordinateProduct_lipschitz i j

theorem productNiltest_complexity {w : σ → ℕ}
    (g : D.filtration.realification.PolynomialOrbit w) (i j : I)
    (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) :
    (V.productNiltest g i j).ComplexityLE (p + 4) := by
  refine ⟨hD.mono D (by linarith), ?_⟩
  change Real.log (2 + (1 : ℝ) + ((2 * V.lipBound : ℝ≥0) : ℝ)) ≤ p + 4
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  simp only [NNReal.coe_mul, NNReal.coe_ofNat]
  calc
    _ ≤ 5 * Real.exp p := by nlinarith [V.lip_bound, Real.one_le_exp hp]
    _ ≤ Real.exp 4 * Real.exp p := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (4 : ℝ)]) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, add_comm]

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open scoped TensorProduct

theorem exists_lower_product_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L I σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d) {p : ℝ}
      (V : D.UnitVerticalObservable (D.filtration.realification.subgroup (s + 1)) I p)
      {w : σ → ℕ} (g : D.filtration.realification.PolynomialOrbit w),
      0 ≤ p → D.GeometryComplexityLE p →
      ∃ n : ℕ, n ≤ d ∧
        ∃ Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n,
          ∃ hQF : Q.filtration = D.filtration.quotientTop,
          Q.lattice = D.lattice.map
            (D.filtration.quotientStepHom (D.filtration.layerIdeal (s + 1)) le_rfl) ∧
          Q.GeometryComplexityLE ((p + C) ^ C) ∧
          letI := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))
          letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1))) :=
            IsModuleTopology.topologicalAddGroup ℝ _
          letI : T2Space (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1))) :=
            realification_moduleTopology_t2 Q.basis
          ∃ S : I → I → Q.Niltest w,
            (∀ i j, (S i j).orbit = D.topQuotientOrbit Q hQF g) ∧
            (∀ i j, (S i j).normBound = 1) ∧
            (∀ i j, (S i j).ComplexityLE ((p + C) ^ C)) ∧
            ∀ i j x, (S i j).eval x = V.coordinateProduct i j
              (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x g)) := by
  obtain ⟨a, _, hdescent⟩ := exists_topInvariant_niltest_budget s
  let X : Polynomial ℕ := Polynomial.X
  let R := (X + 7) ^ 11
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget ((R + Polynomial.C a) ^ a + R)
  refine ⟨C, hC, ?_⟩
  intro L I σ _ _ _ _ _ _ _ d D p V w g hp hD
  let q := (p + 7) ^ 11
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hp4q : p + 4 ≤ q := by
    apply (show p + 4 ≤ p + 7 by linarith).trans
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ p + 7) (by decide : 1 ≤ 11)
  have hbudget : (q + a) ^ a + q ≤ (p + C) ^ C := by
    simpa [q, R, X, Polynomial.eval₂_pow] using hpoly p hp
  have hqa : 0 ≤ (q + a) ^ a := by positivity
  have hqC : q ≤ (p + C) ^ C := (by linarith : q ≤ (q + a) ^ a + q).trans hbudget
  have haC : (q + a) ^ a ≤ (p + C) ^ C := (by linarith : (q + a) ^ a ≤ (q + a) ^ a + q).trans hbudget
  obtain ⟨n, hn, Q, hQF, hQL, hQ, he, _⟩ := D.exists_controlled_top_quotient
    (by linarith : 0 ≤ p + 4) (hD.mono D (by linarith : p ≤ p + 4))
  have hQg : Q.GeometryComplexityLE q := by
    simpa only [show p + 4 + 3 = p + 7 by ring] using hQ
  have heq : ∀ i j, rationalLogHeight (Q.basis.repr
      (lieQuotientMap (D.filtration.layerIdeal (s + 1)) (D.basis j)) i) ≤ q := by
    intro i j
    apply (he j i).trans
    change (p + 4 + 3) ^ 5 ≤ (p + 7) ^ 11
    rw [show p + 4 + 3 = p + 7 by ring]
    exact pow_le_pow_right₀ (by linarith) (by decide)
  refine ⟨n, hn, Q, hQF, hQL, hQg.mono Q hqC, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1))) :=
    realification_moduleTopology_t2 Q.basis
  have hS := fun i j => hdescent D Q hQF hQL (V.productNiltest g i j) q hq
    ((V.productNiltest_complexity g i j hp hD).mono hp4q) hQg heq
    (fun z hz x => V.coordinateProduct_invariant i j z hz x)
  choose S hSo hSn hSc hSe using hS
  exact ⟨S, hSo, hSn, fun i j => (hSc i j).mono haC, hSe⟩

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

namespace NativeNilsequenceExpansion

noncomputable def ofNiltest {L : Type} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d N : ℕ} [NeZero N] {p : ℝ} (D : RationalFilteredNilmanifold L s d)
    (T : D.Niltest (fun _ : Unit => 1)) (hT : T.ComplexityLE p) :
    NativeNilsequenceExpansion s N p (fun x => T.evalCyclic N (fun _ => x)) := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hT.1.1
  have he : 1 ≤ Real.exp p := Real.one_le_exp hp
  exact ofFamily (I := Unit) (fun _ => D) (fun _ => T) (fun _ => 1)
    (by simpa only [Fintype.card_unique, Nat.cast_one] using he) (fun _ => hT)
    (by simpa using he) (fun _ => by simp)

end NativeNilsequenceExpansion

namespace RationalFilteredNilmanifold.UnitVerticalObservable

theorem exists_self_equivalence_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} {I : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d N : ℕ} [NeZero N] (D : RationalFilteredNilmanifold L (s + 1) d) {p : ℝ}
      (V : D.UnitVerticalObservable (D.filtration.realification.subgroup (s + 1)) I p)
      (g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1)),
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card I : ℝ) ≤ Real.exp p →
      NativeVectorEquivalence s N ((p + C) ^ C)
        (fun i x => V.observable i (QuotientGroup.mk
          (D.filtration.realification.polynomialOrbitEval (fun _ => 1) (fun _ => (x.val : ℤ)) g)))
        (fun i x => V.observable i (QuotientGroup.mk
          (D.filtration.realification.polynomialOrbitEval (fun _ => 1) (fun _ => (x.val : ℤ)) g))) := by
  obtain ⟨C, hC, hfamily⟩ := exists_lower_product_family s
  refine ⟨C, hC, ?_⟩
  intro L I _ _ _ _ _ _ _ d N _ D p V g hp hD hI
  have hCr : (2 : ℝ) ≤ C := by exact_mod_cast hC
  have hpC : p ≤ (p + C) ^ C := by
    apply (show p ≤ p + C by linarith).trans
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ p + C)
      (by omega : 1 ≤ C)
  have hd := hI.trans (Real.exp_le_exp.mpr hpC)
  obtain ⟨n, _, Q, _, _, _, hS⟩ := hfamily D V g hp hD
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1))) :=
    realification_moduleTopology_t2 Q.basis
  obtain ⟨S, _, _, hSc, hSe⟩ := hS
  refine ⟨hd, hd, ?_⟩
  intro i j
  have heq : (fun x : ZMod N => (S i j).evalCyclic N (fun _ => x)) =
      (fun x => V.observable i (QuotientGroup.mk
        (D.filtration.realification.polynomialOrbitEval (fun _ => 1) (fun _ => (x.val : ℤ)) g)) *
        star (V.observable j (QuotientGroup.mk
          (D.filtration.realification.polynomialOrbitEval (fun _ => 1) (fun _ => (x.val : ℤ)) g)))) := by
    funext x
    exact hSe i j (fun _ => (x.val : ℤ))
  exact ⟨heq ▸ NativeNilsequenceExpansion.ofNiltest Q (S i j) (hSc i j)⟩

end RationalFilteredNilmanifold.UnitVerticalObservable

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_self_equivalence_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (N : ℕ) [NeZero N] {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : Unit => s + 1) p),
      NativeVectorEquivalence s N ((p + C) ^ C)
        (fun i x => W.evalCyclic N i (fun _ => x))
        (fun i x => W.evalCyclic N i (fun _ => x)) := by
  obtain ⟨C, hC, hself⟩ := RationalFilteredNilmanifold.UnitVerticalObservable.exists_self_equivalence_budget s
  refine ⟨C, hC, ?_⟩
  intro N _ p W
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have htop : W.multi.realSubgroup (fun _ : Unit => s + 1) =
      W.model.filtration.realification.subgroup (s + 1) := by
    simpa only [Fintype.sum_unique] using W.multi.realSubgroup_top
  let V : W.model.UnitVerticalObservable
      (W.model.filtration.realification.subgroup (s + 1)) (Fin W.outputDim) p :=
    { W.vertical with
      vertical := fun i z hz x => W.vertical.vertical i z (htop.symm ▸ hz) x
      integral := fun z hz hL => W.vertical.integral z (htop.symm ▸ hz) hL }
  have hI : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_fin] using W.output_bound
  have h := hself (N := N) W.model V (W.multi.orbitToOrdinary W.orbit) hp W.complexity.1 hI
  have heval (i : Fin W.outputDim) (x : ZMod N) :
      V.observable i (QuotientGroup.mk
        (W.model.filtration.realification.polynomialOrbitEval (fun _ => 1)
          (fun _ => (x.val : ℤ)) (W.multi.orbitToOrdinary W.orbit))) =
      W.evalCyclic N i (fun _ => x) := by
    rw [W.multi.orbitToOrdinary_eval]
    rfl
  convert h using 1 <;> funext i x <;> exact (heval i x).symm

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open scoped TensorProduct BigOperators

theorem exists_translation_equivalence_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} {I : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d N : ℕ} [NeZero N] (D : RationalFilteredNilmanifold L (s + 1) d) {p : ℝ}
      (V : D.UnitVerticalObservable (D.filtration.realification.subgroup (s + 1)) I p)
      (g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1)),
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card I : ℝ) ≤ Real.exp p → ∀ a b : ℤ,
      NativeVectorEquivalence s N ((p + C) ^ C)
        (fun i x => V.observable i (D.integerOrbitPoint g ((x.val : ℤ) + a)))
        (fun i x => V.observable i (D.integerOrbitPoint g ((x.val : ℤ) + b))) := by
  obtain ⟨A, _, hexpand⟩ := exists_shifted_product_expansion s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A) ^ A + X + 4)
  refine ⟨C, hC, ?_⟩
  intro L I _ _ _ _ _ _ _ d N _ D p V g hp hD hI a b
  let r := (p + A) ^ A
  let q := r + p + 4
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hrq : r ≤ q := by dsimp [q]; linarith
  have hq : 0 ≤ q := hp.trans hpq
  have hbound : q ≤ (p + C) ^ C := by
    simpa [q, r, X, Polynomial.eval₂_pow] using hbudget p hp
  have hd := hI.trans (Real.exp_le_exp.mpr (hpq.trans hbound))
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra) :=
    realification_moduleTopology_t2 (Module.finBasis ℚ D.filtration.squareLieSubalgebra)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1))) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1))) :=
    realification_moduleTopology_t2 (Module.finBasis ℚ (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))
  refine ⟨hd, hd, ?_⟩
  intro i j
  obtain ⟨n, Q, S, _, hSc, hSe⟩ := hexpand D V g hp hD (fun _ => Nat.zero_lt_one)
    i j (fun _ => a) (fun _ => b)
  have hcard : (Fintype.card (Fin 4) : ℝ) ≤ Real.exp q := by
    simp only [Fintype.card_fin, Nat.cast_ofNat]
    have h4 : 4 ≤ q := by dsimp [q]; linarith
    linarith [Real.add_one_le_exp q]
  have hcost : (∑ k, ‖polarizationWeight k‖) ≤ Real.exp q := by
    rw [polarizationWeight_cost]
    exact Real.one_le_exp hq
  have E : NativeNilsequenceExpansion s N q
      (fun x => V.observable i (D.integerOrbitPoint g ((x.val : ℤ) + a)) *
        star (V.observable j (D.integerOrbitPoint g ((x.val : ℤ) + b)))) :=
    NativeNilsequenceExpansion.ofFamily Q S polarizationWeight hcard
      (fun k => (hSc k).mono hrq) hcost (fun x => hSe (fun _ => (x.val : ℤ)))
  exact ⟨E.mono hbound⟩

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_translation_equivalence_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (N : ℕ) [NeZero N] {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : Unit => s + 1) p) (a b : ℤ),
      NativeVectorEquivalence s N ((p + C) ^ C)
        (fun i x => W.eval i (fun _ => (x.val : ℤ) + a))
        (fun i x => W.eval i (fun _ => (x.val : ℤ) + b)) := by
  obtain ⟨C, hC, htranslate⟩ :=
    RationalFilteredNilmanifold.UnitVerticalObservable.exists_translation_equivalence_budget s
  refine ⟨C, hC, ?_⟩
  intro N _ p W a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have htop : W.multi.realSubgroup (fun _ : Unit => s + 1) =
      W.model.filtration.realification.subgroup (s + 1) := by
    simpa only [Fintype.sum_unique] using W.multi.realSubgroup_top
  let V : W.model.UnitVerticalObservable
      (W.model.filtration.realification.subgroup (s + 1)) (Fin W.outputDim) p :=
    { W.vertical with
      vertical := fun i z hz x => W.vertical.vertical i z (htop.symm ▸ hz) x
      integral := fun z hz hL => W.vertical.integral z (htop.symm ▸ hz) hL }
  have hI : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_fin] using W.output_bound
  have h := htranslate (N := N) W.model V (W.multi.orbitToOrdinary W.orbit)
    hp W.complexity.1 hI a b
  have heval (i : Fin W.outputDim) (x : ZMod N) (c : ℤ) :
      V.observable i (W.model.integerOrbitPoint (W.multi.orbitToOrdinary W.orbit) ((x.val : ℤ) + c)) =
      W.eval i (fun _ => (x.val : ℤ) + c) := by
    unfold RationalFilteredNilmanifold.integerOrbitPoint
    rw [W.multi.orbitToOrdinary_eval]
    rfl
  convert h using 1 <;> funext i x <;> exact (heval i x _).symm

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
