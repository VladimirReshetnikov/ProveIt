import OAI.Combinatorics.Progressions.Estimates.OrthogonalBlockGram
import OAI.Combinatorics.Progressions.Estimates.QuotientTranslatePartition
import OAI.Combinatorics.Progressions.Linear.NormalHyperplaneProjection
import OAI.Combinatorics.Progressions.Polynomial.SchmidtHyperplaneTransfer

namespace OAI

section

namespace Erdos3

open Module

theorem zspan_covolume_sq_eq_det_gram_fintype
    {ι E : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (b : Basis ι ℝ E) :
    ZLattice.covolume (Submodule.span ℤ (Set.range b)) ^ 2 = (Matrix.gram ℝ b).det := by
  classical
  let e := Fintype.equivFin ι
  let b' := b.reindex e
  have hspan : Submodule.span ℤ (Set.range b') = Submodule.span ℤ (Set.range b) := by
    congr 1
    simp [b', Basis.coe_reindex]
  have hgram : Matrix.gram ℝ b' = (Matrix.gram ℝ b).submatrix e.symm e.symm := by
    ext i j
    simp [b', Matrix.gram_apply]
  have h := zspan_covolume_sq_eq_det_gram b'
  rw [hspan, hgram, Matrix.det_submatrix_equiv_self] at h
  exact h

theorem lattice_covolume_sq_eq_gram
    {ι E : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (b : Basis ι ℤ Λ) :
    ZLattice.covolume Λ ^ 2 = (Matrix.gram ℝ (b.ofZLatticeBasis ℝ Λ)).det := by
  have h := zspan_covolume_sq_eq_det_gram_fintype (b.ofZLatticeBasis ℝ Λ)
  simpa only [b.ofZLatticeBasis_span ℝ] using h

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem latticeHyperplane_covolume_sq (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (ξ : E) (hξ : ξ ≠ 0)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, inner ℝ ξ x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : inner ℝ ξ w = 1) :
    ZLattice.covolume Λ ^ 2 =
      ZLattice.covolume (latticeHyperplane Λ (normalFunctional ξ)) ^ 2 * (‖ξ‖⁻¹) ^ 2 := by
  classical
  let f := normalFunctional ξ
  let K := latticeHyperplane Λ f
  let : IsZLattice ℝ K := latticeHyperplane_isZLattice Λ f hint w hwΛ hw
  let bK := Module.Free.chooseBasis ℤ K
  let b := latticeHyperplaneBasis Λ f hint w hwΛ hw bK
  let bR := b.ofZLatticeBasis ℝ Λ
  let bKR := bK.ofZLatticeBasis ℝ K
  have hinl (i) : bR (Sum.inl i) = (bKR i : E) := by
    simpa only [bR, bKR, Module.Basis.ofZLatticeBasis_apply, b] using
      latticeHyperplaneBasis_inl Λ f hint w hwΛ hw bK i
  have hinr (j : Unit) : bR (Sum.inr j) = w := by
    simpa only [bR, Module.Basis.ofZLatticeBasis_apply, b] using
      latticeHyperplaneBasis_inr Λ f hint w hwΛ hw bK j
  have hspan : Submodule.span ℝ (Set.range (fun i => bR (Sum.inl i))) = f.ker := by
    rw [show (fun i => bR (Sum.inl i)) = (fun i => (bKR i : E)) from funext hinl]
    change Submodule.span ℝ (Set.range (f.ker.subtype ∘ bKR)) = _
    rw [Set.range_comp, ← Submodule.map_span, bKR.span_eq,
      Submodule.map_top, Submodule.range_subtype]
  have hkernel : (Matrix.gram ℝ (fun i => bR (Sum.inl i))).det = ZLattice.covolume K ^ 2 := by
    have he : Matrix.gram ℝ (fun i => bR (Sum.inl i)) = Matrix.gram ℝ bKR := by
      ext i j
      simp only [Matrix.gram_apply, hinl]
      rfl
    rw [he]
    exact (lattice_covolume_sq_eq_gram K bK).symm
  have hblock := gram_det_orthogonal_block bR
  dsimp only at hblock
  rw [hspan, hkernel, Matrix.det_unique (n := Unit), Matrix.gram_apply, hinr,
    real_inner_self_eq_norm_sq, normalHyperplane_height ξ w hξ hw] at hblock
  rw [lattice_covolume_sq_eq_gram Λ b]
  exact hblock

theorem latticeHyperplane_covolume (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (ξ : E) (hξ : ξ ≠ 0)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, inner ℝ ξ x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : inner ℝ ξ w = 1) :
    ZLattice.covolume (latticeHyperplane Λ (normalFunctional ξ)) =
      ‖ξ‖ * ZLattice.covolume Λ := by
  let := latticeHyperplane_isZLattice Λ (normalFunctional ξ) hint w hwΛ hw
  have h := latticeHyperplane_covolume_sq Λ ξ hξ hint w hwΛ hw
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have hc := ZLattice.covolume_pos Λ MeasureTheory.volume
  have hk := ZLattice.covolume_pos (latticeHyperplane Λ (normalFunctional ξ)) MeasureTheory.volume
  have hs : (‖ξ‖ * ZLattice.covolume Λ) ^ 2 =
      ZLattice.covolume (latticeHyperplane Λ (normalFunctional ξ)) ^ 2 := by
    rw [mul_pow, h]
    field_simp
  nlinarith [mul_pos hn hc]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] in
theorem basis_equivFun_measurePreserving (b : Basis ι ℝ E) :
    MeasurePreserving b.equivFunL b.addHaar volume := by
  classical
  refine ⟨b.equivFunL.continuous.measurable, ?_⟩
  rw [Basis.map_addHaar]
  have hb : b.map b.equivFun = Pi.basisFun ℝ ι := by
    ext i j
    simp [Basis.equivFun_self, Pi.basisFun_apply, Pi.single_apply, eq_comm]
  change (b.map b.equivFun).addHaar = volume
  rw [hb, Basis.addHaar_def, Basis.parallelepiped_basisFun,
    addHaarMeasure_eq_volume_pi]

theorem volume_eq_covolume_smul_basis_addHaar (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (b : Basis ι ℤ Λ) :
    (volume : Measure E) = ENNReal.ofReal (ZLattice.covolume Λ) •
      (b.ofZLatticeBasis ℝ Λ).addHaar := by
  let bR := b.ofZLatticeBasis ℝ Λ
  have hcov : ZLattice.covolume Λ = volume.real (parallelepiped bR) := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain Λ volume
      (ZLattice.isAddFundamentalDomain b volume)]
    exact measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped bR volume)
  have h := Measure.addHaarMeasure_unique (volume : Measure E) bR.parallelepiped
  have hfinite : volume (parallelepiped bR) ≠ ⊤ := by
    simpa only [Basis.coe_parallelepiped] using bR.parallelepiped.isCompact.measure_ne_top (μ := volume)
  rw [Basis.addHaar_def]
  rw [hcov, measureReal_def, ENNReal.ofReal_toReal hfinite]
  exact h

theorem latticeBasis_integral_cube (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (b : Basis ι ℤ Λ) (f : E → ℂ) :
    (ZLattice.covolume Λ : ℂ) *
        (∫ x : ι → ℝ in Set.pi Set.univ (fun _ => Set.Ico (0 : ℝ) 1),
          f ((b.ofZLatticeBasis ℝ Λ).equivFun.symm x)) =
      ∫ x in ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ Λ), f x := by
  let bR := b.ofZLatticeBasis ℝ Λ
  have hp := basis_equivFun_measurePreserving bR
  have hpre : bR.equivFunL ⁻¹' Set.pi Set.univ (fun _ => Set.Ico (0 : ℝ) 1) =
      ZSpan.fundamentalDomain bR := by
    ext x
    simp [ZSpan.fundamentalDomain]
  have hi := hp.setIntegral_preimage_emb bR.equivFunL.toHomeomorph.measurableEmbedding
    (f ∘ bR.equivFun.symm) (Set.pi Set.univ (fun _ => Set.Ico (0 : ℝ) 1))
  simp only [hpre, Function.comp_apply] at hi
  have hi' : (∫ x in ZSpan.fundamentalDomain bR, f x ∂bR.addHaar) =
      ∫ x : ι → ℝ in Set.pi Set.univ (fun _ => Set.Ico (0 : ℝ) 1), f (bR.equivFun.symm x) := by
    convert hi using 1
    congr 1
    funext x
    exact congrArg f (bR.equivFun.symm_apply_apply x).symm
  conv_rhs => rw [volume_eq_covolume_smul_basis_addHaar Λ b, Measure.restrict_smul,
    integral_smul_measure, ENNReal.toReal_ofReal (ZLattice.covolume_pos Λ volume).le]
  change _ = (ZLattice.covolume Λ : ℂ) * _
  rw [hi']

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def latticeGaussianNormalizer (Λ : Submodule ℤ E) (t : ℝ) : ℝ :=
  (Real.sqrt t) ^ Module.finrank ℝ E * ZLattice.covolume Λ

noncomputable def normalizedLatticeGaussian (Λ : Submodule ℤ E) (t : ℝ) (x : E) : ℝ :=
  latticeGaussianNormalizer Λ t * latticeGaussianMass Λ t x

theorem latticeGaussianNormalizer_nonneg (Λ : Submodule ℤ E) (t : ℝ) :
    0 ≤ latticeGaussianNormalizer Λ t :=
  mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) ENNReal.toReal_nonneg

theorem latticeGaussianNormalizer_pos (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] {t : ℝ} (ht : 0 < t) : 0 < latticeGaussianNormalizer Λ t :=
  mul_pos (pow_pos (Real.sqrt_pos.mpr ht) _) (ZLattice.covolume_pos Λ MeasureTheory.volume)

theorem normalizedLatticeGaussian_nonneg (Λ : Submodule ℤ E) (t : ℝ) (x : E) :
    0 ≤ normalizedLatticeGaussian Λ t x :=
  mul_nonneg (latticeGaussianNormalizer_nonneg Λ t) (latticeGaussianMass_nonneg Λ t x)

theorem normalizedLatticeGaussian_pos (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] {t : ℝ} (ht : 0 < t) (x : E) :
    0 < normalizedLatticeGaussian Λ t x :=
  mul_pos (latticeGaussianNormalizer_pos Λ ht) (latticeGaussianMass_pos Λ ht x)

theorem latticeGaussianNormalizer_hyperplane (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (ξ : E) (hξ : ξ ≠ 0)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, inner ℝ ξ x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : inner ℝ ξ w = 1)
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ 1 + ε) :
    Real.sqrt t * latticeGaussianNormalizer (latticeHyperplane Λ (normalFunctional ξ))
        (t * (1 + ε) ^ 2) =
      ‖ξ‖ * (1 + ε) ^ Module.finrank ℝ (normalFunctional ξ).ker *
        latticeGaussianNormalizer Λ t := by
  unfold latticeGaussianNormalizer
  rw [Real.sqrt_mul ht, Real.sqrt_sq hε,
    latticeHyperplane_covolume Λ ξ hξ hint w hwΛ hw,
    ← hyperplane_finrank (normalFunctional ξ) w hw, pow_succ, mul_pow]
  ring

theorem normalizedLatticeGaussian_transfer (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (ξ : E) (hξ : ξ ≠ 0)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, inner ℝ ξ x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : inner ℝ ξ w = 1)
    {t ε c : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ 1 + ε)
    (x : E) (y : (normalFunctional ξ).ker)
    (htransfer : c * latticeGaussianMass (latticeHyperplane Λ (normalFunctional ξ))
      (t * (1 + ε) ^ 2) y ≤ latticeGaussianMass Λ t x) :
    c * Real.sqrt t * normalizedLatticeGaussian (latticeHyperplane Λ (normalFunctional ξ))
        (t * (1 + ε) ^ 2) y ≤
      ‖ξ‖ * (1 + ε) ^ Module.finrank ℝ (normalFunctional ξ).ker *
        normalizedLatticeGaussian Λ t x := by
  have h := mul_le_mul_of_nonneg_left htransfer
    (mul_nonneg (mul_nonneg (norm_nonneg ξ)
      (pow_nonneg hε (Module.finrank ℝ (normalFunctional ξ).ker)))
      (latticeGaussianNormalizer_nonneg Λ t))
  have hid := latticeGaussianNormalizer_hyperplane Λ ξ hξ hint w hwΛ hw ht hε
  unfold normalizedLatticeGaussian
  calc
    _ = (Real.sqrt t * latticeGaussianNormalizer (latticeHyperplane Λ (normalFunctional ξ))
          (t * (1 + ε) ^ 2)) *
        (c * latticeGaussianMass (latticeHyperplane Λ (normalFunctional ξ))
          (t * (1 + ε) ^ 2) y) := by ring
    _ = (‖ξ‖ * (1 + ε) ^ Module.finrank ℝ (normalFunctional ξ).ker *
          latticeGaussianNormalizer Λ t) *
        (c * latticeGaussianMass (latticeHyperplane Λ (normalFunctional ξ))
          (t * (1 + ε) ^ 2) y) := by rw [hid]
    _ ≤ _ := by simpa only [mul_assoc] using h

theorem exists_normalized_schmidt_hyperplane_transfer (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (ξ : E) (hξ : ξ ≠ 0)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, inner ℝ ξ x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : inner ℝ ξ w = 1)
    (α : E) {N k : ℕ} {t ε : ℝ} (ht : 0 < t) (hε : 0 ≤ ε) (hεone : ε ≤ 1)
    (hsmall : Real.sqrt t * ((N : ℝ) ^ k *
      (CircleFourier.integerDistance ((inner ℝ ξ α : ℝ) : CircleFourier.Circle) / ‖ξ‖)) ≤ ε) :
    ∃ β : (normalFunctional ξ).ker, ∀ n : ℤ, |n| ≤ (N : ℤ) →
      Real.exp (-4 * Real.pi) * Real.sqrt t *
          normalizedLatticeGaussian (latticeHyperplane Λ (normalFunctional ξ))
            (t * (1 + ε) ^ 2) ((n : ℝ) ^ k • β) ≤
        ‖ξ‖ * (1 + ε) ^ Module.finrank ℝ (normalFunctional ξ).ker *
          normalizedLatticeGaussian Λ t ((n : ℝ) ^ k • α) := by
  obtain ⟨β, hβ⟩ := exists_schmidt_hyperplane_transfer_at_temperature Λ ξ hξ w hwΛ hw
    α ht hε hεone hsmall
  exact ⟨β, fun n hn => normalizedLatticeGaussian_transfer Λ ξ hξ hint w hwΛ hw ht.le
    (by linarith) _ _ (hβ n hn)⟩

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I]

theorem lattice_fundamentalDomain_volume (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (b : Basis I ℤ Λ) :
    volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ Λ)) =
      ENNReal.ofReal (ZLattice.covolume Λ) := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain Λ volume
    (ZLattice.isAddFundamentalDomain b volume), measureReal_def,
    ENNReal.ofReal_toReal (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne]

theorem lattice_quotient_scaled_haar (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (b : Basis I ℤ Λ)
    (μ : Measure (E ⧸ Λ.toAddSubgroup)) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant] :
    ENNReal.ofReal (ZLattice.covolume Λ) • μ =
      Measure.map (QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup)
        (volume.restrict (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ Λ))) := by
  let F := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ Λ)
  let : Countable Λ.toAddSubgroup := b.repr.injective.countable
  let : Countable Λ.toAddSubgroup.op := Λ.toAddSubgroup.equivOp.symm.injective.countable
  have hF : IsAddFundamentalDomain Λ.toAddSubgroup F volume :=
    ZLattice.isAddFundamentalDomain b volume
  have hop := additiveFundamentalDomain_op Λ.toAddSubgroup hF
  let : HasAddFundamentalDomain Λ.toAddSubgroup.op E volume := ⟨F, hop⟩
  have hclosed : IsClosed (Λ.toAddSubgroup : Set E) := AddSubgroup.isClosed_of_discreteTopology
  let : IsClosed (Λ.toAddSubgroup : Set E) := hclosed
  let c := ENNReal.ofReal (ZLattice.covolume Λ)
  let : IsFiniteMeasure (c • μ) := μ.smul_finite ENNReal.ofReal_ne_top
  have hscale : addCovolume Λ.toAddSubgroup.op E volume = (c • μ) Set.univ := by
    rw [hop.covolume_eq_volume volume, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    exact lattice_fundamentalDomain_volume Λ b
  let : AddQuotientMeasureEqMeasurePreimage volume (c • μ) :=
    leftInvariantIsAddQuotientMeasureEqMeasurePreimage (ν := volume) hscale
  exact hop.addProjection_respects_measure (c • μ)

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
theorem latticeGaussianMass_antitone (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (x : E) :
    latticeGaussianMass Λ t x ≤ latticeGaussianMass Λ s x := by
  apply (lattice_gaussian_summable Λ (hs.trans_le hst) x).tsum_le_tsum
    _ (lattice_gaussian_summable Λ hs x)
  intro m
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonpos_left hst (neg_nonpos.mpr Real.pi_pos.le)) (sq_nonneg _)

theorem normalizedLatticeGaussian_hyperplane_origin_le (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (ξ : E) (hξ : ξ ≠ 0)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, inner ℝ ξ x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : inner ℝ ξ w = 1)
    {t ε : ℝ} (ht : 0 < t) (hε : 0 ≤ ε) :
    Real.sqrt t * normalizedLatticeGaussian (latticeHyperplane Λ (normalFunctional ξ))
        (t * (1 + ε) ^ 2) 0 ≤
      ‖ξ‖ * (1 + ε) ^ Module.finrank ℝ (normalFunctional ξ).ker *
        normalizedLatticeGaussian Λ t 0 := by
  have htemp : t ≤ t * (1 + ε) ^ 2 := by nlinarith [mul_nonneg ht.le (sq_nonneg ε)]
  have hmass := (latticeGaussianMass_antitone (latticeHyperplane Λ (normalFunctional ξ))
    ht htemp 0).trans (latticeGaussianMass_hyperplane_le Λ (normalFunctional ξ) ht 0)
  simpa only [one_mul] using normalizedLatticeGaussian_transfer Λ ξ hξ hint w hwΛ hw
    ht.le (by linarith) 0 0 (c := 1) (by simpa only [one_mul, Submodule.coe_zero] using hmass)

theorem lattice_covolume_of_finrank_zero (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hd : Module.finrank ℝ E = 0) : ZLattice.covolume Λ = 1 := by
  classical
  let b := Module.Free.chooseBasis ℤ Λ
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ Λ) = 0 := by
    rw [← Module.finrank_eq_card_basis b, ZLattice.rank ℝ Λ, hd]
  let : IsEmpty (Module.Free.ChooseBasisIndex ℤ Λ) := Fintype.card_eq_zero_iff.mp hcard
  have h := lattice_covolume_sq_eq_gram Λ b
  rw [Matrix.det_isEmpty] at h
  nlinarith [ZLattice.covolume_pos Λ MeasureTheory.volume]

theorem normalizedLatticeGaussian_of_finrank_zero (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hd : Module.finrank ℝ E = 0) (t : ℝ) (x : E) :
    normalizedLatticeGaussian Λ t x = 1 := by
  let : Subsingleton E := Module.finrank_zero_iff.mp hd
  have hx : x = 0 := Subsingleton.elim _ _
  let : Unique Λ := ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩
  simp [normalizedLatticeGaussian, latticeGaussianNormalizer, hd,
    lattice_covolume_of_finrank_zero Λ hd, latticeGaussianMass, hx]
  exact Or.inr (Subsingleton.elim _ _)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Set

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I]

theorem lattice_quotient_haar_image (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (b : Basis I ℤ Λ)
    (μ : Measure (E ⧸ Λ.toAddSubgroup)) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    {A : Set E} (hAm : MeasurableSet A)
    (hA : InjOn (QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup) A) :
    μ ((QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup) '' A) =
      volume A / ENNReal.ofReal (ZLattice.covolume Λ) := by
  let : Countable Λ.toAddSubgroup := b.repr.injective.countable
  let : IsClosed (Λ.toAddSubgroup : Set E) := AddSubgroup.isClosed_of_discreteTopology
  have hq : Continuous (QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup) :=
    continuous_quotient_mk'
  have him := hAm.image_of_continuousOn_injOn hq.continuousOn hA
  have he := congrArg
    (fun ν : Measure (E ⧸ Λ.toAddSubgroup) => ν
      ((QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup) '' A))
    (lattice_quotient_scaled_haar Λ b μ)
  rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply hq.measurable him,
    Measure.restrict_apply (him.preimage hq.measurable)] at he
  rw [quotient_injective_lift_measure Λ.toAddSubgroup volume
    (ZLattice.isAddFundamentalDomain b volume)
    (ZSpan.fundamentalDomain_measurableSet _) hAm hA] at he
  exact (ENNReal.eq_div_iff (ENNReal.ofReal_pos.mpr (ZLattice.covolume_pos Λ volume)).ne'
    ENNReal.ofReal_ne_top).mpr he

theorem lattice_quotient_haar_translated_image (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (b : Basis I ℤ Λ)
    (μ : Measure (E ⧸ Λ.toAddSubgroup)) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (v : E) {A : Set E} (hAm : MeasurableSet A)
    (hA : InjOn (fun x => (QuotientAddGroup.mk (x - v) : E ⧸ Λ.toAddSubgroup)) A) :
    μ ((fun x => (QuotientAddGroup.mk (x - v) : E ⧸ Λ.toAddSubgroup)) '' A) =
      volume A / ENNReal.ofReal (ZLattice.covolume Λ) := by
  have hBm : MeasurableSet ((fun x : E => x - v) '' A) :=
    hAm.image_of_continuousOn_injOn (continuous_id.sub continuous_const).continuousOn
      (fun _ _ _ _ he => sub_left_inj.mp he)
  have hB : InjOn (QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup)
      ((fun x : E => x - v) '' A) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ he
    exact congrArg (fun z => z - v) (hA hx hy he)
  have hset : ((fun x : E => x - v) '' A) = (fun x => x + v) ⁻¹' A := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [mem_preimage, sub_add_cancel] using hy
    · intro hx
      exact ⟨x + v, hx, add_sub_cancel_right x v⟩
  have he := lattice_quotient_haar_image Λ b μ hBm hB
  rw [image_image] at he
  rw [he, hset, measure_preimage_add_right]

theorem lattice_quotient_haar_countable_sheets {T : Type*} [Countable T]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (b : Basis I ℤ Λ)
    (μ : Measure (E ⧸ Λ.toAddSubgroup)) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (v : T → E) (A : T → Set E) (hAm : ∀ t, MeasurableSet (A t))
    (hA : ∀ t, InjOn (fun x => (QuotientAddGroup.mk (x - v t) : E ⧸ Λ.toAddSubgroup)) (A t))
    (hdisj : Pairwise (fun s t => Disjoint
      ((fun x => (QuotientAddGroup.mk (x - v s) : E ⧸ Λ.toAddSubgroup)) '' A s)
      ((fun x => (QuotientAddGroup.mk (x - v t) : E ⧸ Λ.toAddSubgroup)) '' A t))) :
    μ (⋃ t, (fun x => (QuotientAddGroup.mk (x - v t) : E ⧸ Λ.toAddSubgroup)) '' A t) =
      (∑' t, volume (A t)) / ENNReal.ofReal (ZLattice.covolume Λ) := by
  let : IsClosed (Λ.toAddSubgroup : Set E) := AddSubgroup.isClosed_of_discreteTopology
  rw [measure_iUnion hdisj (fun t => (hAm t).image_of_continuousOn_injOn
    (continuous_quotient_mk'.comp (continuous_id.sub continuous_const)).continuousOn (hA t))]
  simp_rw [lattice_quotient_haar_translated_image Λ b μ _ (hAm _) (hA _)]
  simpa only [div_eq_mul_inv] using ENNReal.tsum_mul_right

end Erdos3

end

section

namespace Erdos3

open Module Submodule MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem orthogonalLattice_covolume_sq (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (W : Submodule ℝ E)
    [IsZLattice ℝ (latticeSection Λ Wᗮ)]
    [DiscreteTopology (orthogonalLatticeImage Λ W)] [IsZLattice ℝ (orthogonalLatticeImage Λ W)] :
    ZLattice.covolume Λ ^ 2 = ZLattice.covolume (latticeSection Λ Wᗮ) ^ 2 *
      ZLattice.covolume (orthogonalLatticeImage Λ W) ^ 2 := by
  classical
  let bK := Free.chooseBasis ℤ (latticeSection Λ Wᗮ)
  let bP := Free.chooseBasis ℤ (orthogonalLatticeImage Λ W)
  obtain ⟨b, hbK, hbP⟩ := exists_orthogonal_lattice_split_basis Λ W bK bP
  let B := b.ofZLatticeBasis ℝ Λ
  let K := bK.ofZLatticeBasis ℝ (latticeSection Λ Wᗮ)
  let P := bP.ofZLatticeBasis ℝ (orthogonalLatticeImage Λ W)
  have hleft (i) : B (Sum.inl i) = (K i : E) := by
    simpa only [B, K, Basis.ofZLatticeBasis_apply] using hbK i
  have hspan : span ℝ (Set.range (fun i => B (Sum.inl i))) = Wᗮ := by
    rw [show (fun i => B (Sum.inl i)) = (fun i => (K i : E)) from funext hleft]
    change span ℝ (Set.range (Wᗮ.subtype ∘ K)) = Wᗮ
    rw [Set.range_comp, ← Submodule.map_span, K.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  have hright (j) : B (Sum.inr j) - Wᗮ.starProjection (B (Sum.inr j)) = (P j : E) := by
    have hp : W.starProjection (B (Sum.inr j)) = (P j : E) := by
      simpa only [B, P, Basis.ofZLatticeBasis_apply, Submodule.coe_orthogonalProjectionOnto_apply]
        using congrArg Subtype.val (hbP j)
    have hsum := W.starProjection_add_starProjection_orthogonal (B (Sum.inr j))
    rw [hp] at hsum
    exact (eq_sub_iff_add_eq.mpr hsum).symm
  have hKGram : (Matrix.gram ℝ (fun i => B (Sum.inl i))).det =
      ZLattice.covolume (latticeSection Λ Wᗮ) ^ 2 := by
    have hg : Matrix.gram ℝ (fun i => B (Sum.inl i)) = Matrix.gram ℝ K := by
      ext i j
      simp only [Matrix.gram_apply, hleft]
      rfl
    rw [hg]
    exact (lattice_covolume_sq_eq_gram (latticeSection Λ Wᗮ) bK).symm
  have hPGram : (Matrix.gram ℝ (fun j => B (Sum.inr j) -
      Wᗮ.starProjection (B (Sum.inr j)))).det =
      ZLattice.covolume (orthogonalLatticeImage Λ W) ^ 2 := by
    have hg : Matrix.gram ℝ (fun j => B (Sum.inr j) - Wᗮ.starProjection (B (Sum.inr j))) =
        Matrix.gram ℝ P := by
      ext i j
      simp only [Matrix.gram_apply, hright]
      rfl
    rw [hg]
    exact (lattice_covolume_sq_eq_gram (orthogonalLatticeImage Λ W) bP).symm
  have hblock := gram_det_orthogonal_block B
  dsimp only at hblock
  rw [hspan, hKGram, hPGram] at hblock
  rw [lattice_covolume_sq_eq_gram Λ b]
  exact hblock

theorem orthogonalLattice_covolume (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (W : Submodule ℝ E)
    [IsZLattice ℝ (latticeSection Λ Wᗮ)]
    [DiscreteTopology (orthogonalLatticeImage Λ W)] [IsZLattice ℝ (orthogonalLatticeImage Λ W)] :
    ZLattice.covolume Λ = ZLattice.covolume (latticeSection Λ Wᗮ) *
      ZLattice.covolume (orthogonalLatticeImage Λ W) := by
  apply (sq_eq_sq₀ (ZLattice.covolume_pos Λ volume).le
    (mul_nonneg (ZLattice.covolume_pos (latticeSection Λ Wᗮ) volume).le
      (ZLattice.covolume_pos (orthogonalLatticeImage Λ W) volume).le)).mp
  simpa only [mul_pow] using orthogonalLattice_covolume_sq Λ W

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Set

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I]

theorem lattice_sheet_haar_formula (Λ : Submodule ℤ E) [DiscreteTopology Λ] [Countable Λ]
    (W : Submodule ℝ E) [IsZLattice ℝ (latticeSection Λ W)]
    (b : Basis I ℤ (latticeSection Λ W))
    (μ : Measure (W ⧸ (latticeSection Λ W).toAddSubgroup))
    [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    {Ω : Set E} (hΩm : MeasurableSet Ω)
    (hΩ : ∀ x ∈ Ω, ∀ y ∈ Ω, x - y ∈ Λ → x = y) :
    μ (⋃ z : orthogonalLatticeImage Λ Wᗮ,
      latticeSheetQuotient Λ W z '' {u | latticeSheetPoint W z.val u ∈ Ω}) =
      (∑' z : orthogonalLatticeImage Λ Wᗮ,
        volume {u : W | latticeSheetPoint W z.val u ∈ Ω}) /
          ENNReal.ofReal (ZLattice.covolume (latticeSection Λ W)) := by
  let : Countable (orthogonalLatticeImage Λ Wᗮ) :=
    (orthogonalLatticeProjection_surjective Λ Wᗮ).countable
  apply lattice_quotient_haar_countable_sheets (latticeSection Λ W) b μ
    (projectedLatticeShift Λ W) (fun z => {u | latticeSheetPoint W z.val u ∈ Ω})
  · intro z
    exact hΩm.preimage (continuous_subtype_val.add continuous_const).measurable
  · intro z u hu v hv h
    exact (latticeSheetQuotient_injective_on_region Λ W hΩ hu hv h).2
  · intro z w hzw
    apply Set.disjoint_left.mpr
    rintro q ⟨u, hu, rfl⟩ ⟨v, hv, he⟩
    exact hzw (latticeSheetQuotient_injective_on_region Λ W hΩ hu hv he.symm).1

end Erdos3

end

end OAI
