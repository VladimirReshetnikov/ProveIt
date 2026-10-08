/- Modified for ProveIt: Use IsModuleTopology.topologicalAddGroup and explicit norm congruence on Lean 4.32; statements unchanged. -/
import OAI.Combinatorics.Progressions.Estimates.LowTaggedRationalLiftRewrite
import OAI.Combinatorics.Progressions.Estimates.TranslationMajorCorrelationDecomposition
import OAI.Combinatorics.Progressions.Fourier.MajorPhaseLowFourierExtraction
import OAI.Combinatorics.Progressions.Lattices.LowTaggedAffineCoordinates
import OAI.Combinatorics.Progressions.Polynomial.MajorPhaseVectorDecomposition

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem majorPhase_residue_lowTagged_rank {m : ℕ} {X : Type*}
    (J : Fin m → Type*) [∀ j, Fintype (J j)] (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (N lengths : X → ℕ) (hN : ∀ i, 0 < (N i : ℝ))
    (hlengths : ∀ i, 0 < lengths i) (q : ℕ) (hq : 0 < q) (start : X → ℤ)
    (p E D B Rrank : ℝ) (hp : 0 ≤ p) (hE : 0 ≤ E)
    (hqbound : (q : ℝ) ≤ Real.exp p)
    (hcomparison : ∀ i, (N i : ℝ) ≤ Real.exp E * q * lengths i)
    (hrow : D ≤ B) (hden : (m : ℝ) * p + D ≤ B)
    (hslow : (m : ℝ) * E + D ≤ B) (hRrank : Real.exp B ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j)) :
    ∀ h : Fin d, HasLayerSamplingRank (h.val + 1)
      (fun i => (lengths i : ℝ)) (Real.exp D) (lowTaggedRetained J d U h)
      (lowTaggedTopPolynomial J d (fun j => residueAffine q start (poly j))) := by
  have hsliced (j : Fin m) : HasLayerSamplingRank (j.val + 1)
      (fun i => (lengths i : ℝ)) (Real.exp D) (U j)
      (residueAffine q start (poly j)) := by
    apply (hrank j).residueAffine (hpoly j) hN
      (fun i => Nat.cast_pos.mpr (hlengths i)) q hq start (Real.exp E) hcomparison
    · exact (Real.exp_le_exp.mpr hrow).trans hRrank
    · exact (pow_mul_exp_le_exp_of_le_budget (Nat.cast_nonneg q) hqbound hp
        (Nat.succ_le_of_lt j.isLt) hden).trans hRrank
    · exact (pow_mul_exp_le_exp_of_le_budget (Real.exp_nonneg E) le_rfl hE
        (Nat.succ_le_of_lt j.isLt) hslow).trans hRrank
  exact lowTaggedTopPolynomial_hasLayerSamplingRank J d _ U _ _ hsliced

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

variable {m : ℕ} {X L : Type} [LieRing L] [LieAlgebra ℚ L] {t e : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (J : Fin m → Type) [∀ j, Fintype (J j)] (d : ℕ)
  (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
  (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J d)))
  (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
  (F : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℝ)
  (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J d)) → ℤ)
  {D : RationalFilteredNilmanifold L t e} (R : D.Niltest (fun _ : X => 1))
  (start : X → ℤ) (q M : ℕ) (hM : 0 < M) (a : (Σ j, J j) → ℤ)
  (hhigh : ∀ j, d < j.val + 1 → ∀ i, a ⟨j, i⟩ = 0)

include hM hhigh in

theorem majorPhase_affine_integrand (v : X → ℤ) :
    let u := fun i => start i + (q : ℤ) * v i
    let A := fun i => residueAffinePolynomial q start
      (lowTaggedPolynomial J d poly i - MvPolynomial.C (c i))
    let y := fun i => MvPolynomial.eval (fun x => (v x : ℝ)) (A i) - (β u i : ℝ)
    (Real.fourierChar (MvPolynomial.eval
      (fun i => (start i : ℝ) + (q : ℝ) * v i)
      (normalizedTwistFrequencyPolynomial M a poly)) : ℂ) *
      majorPhaseSample J d poly Ψ c F β R.eval u =
    rationalLiftCharacterTwist M (lowTaggedFrequency J d a) c y
        (fun i => (β u i : ZMod M)) * (Ψ.value y : ℂ) *
      (Real.fourierChar (MvPolynomial.eval
        (Sum.elim (fun i => (v i : ℝ)) (fun i => (β u i : ℝ)))
        (jointResidueAffinePolynomial q start F)) : ℂ) *
      (R.scalarAffinePullback (q : ℚ) (fun i => (start i : ℚ))).eval v := by
  have htrunc : truncateTaggedFrequency d a = a := by
    funext i
    rcases i with ⟨j, i⟩
    by_cases hj : j.val + 1 ≤ d
    · simp only [truncateTaggedFrequency, hj, ite_true]
    · simp only [truncateTaggedFrequency, hj, ite_false,
        hhigh j (Nat.lt_of_not_ge hj) i]
  let u : X → ℤ := fun i => start i + (q : ℤ) * v i
  have hfreq := normalizedTwistFrequencyPolynomial_low_rationalLiftCharacterTwist_affine
    J M d hM a poly start q v c (β u)
  rw [htrunc] at hfreq
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast] at hfreq
  have hR : (R.scalarAffinePullback (q : ℚ) (fun i => (start i : ℚ))).eval v = R.eval u := by
    simpa only [Int.cast_natCast, add_comm] using
      R.scalarAffinePullback_eval_integer (q : ℤ) start v
  have hjoint : MvPolynomial.eval
      (Sum.elim (fun i => (v i : ℝ)) (fun i => (β u i : ℝ)))
      (jointResidueAffinePolynomial q start F) =
      MvPolynomial.eval (fun j => ((Sum.elim u (β u) j : ℤ) : ℝ)) F := by
    rw [jointResidueAffinePolynomial_eval]
    apply congrArg (fun x => MvPolynomial.eval x F)
    funext j
    cases j <;> simp only [Sum.elim_inl, Sum.elim_inr, u,
      Int.cast_add, Int.cast_mul, Int.cast_natCast]
  dsimp only
  simp only [residueAffinePolynomial_eval_real, map_sub, eval_C]
  rw [hfreq, hR, hjoint]
  simp only [majorPhaseSample, u, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module RationalFilteredNilmanifold PolynomialTranslationLie
open scoped TensorProduct NNReal BigOperators

theorem exists_majorPhase_residue_detection (d : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {m : ℕ} {X L : Type} [Fintype X] [DecidableEq X]
      [LieRing L] [LieAlgebra ℚ L] {t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (J : Fin m → Type) [∀ j, Fintype (J j)]
      [Fintype (WeightedBasisIndex (lowTaggedWeight J d) d)]
      (D : RationalFilteredNilmanifold L t e) (_htd : t < d)
      (R : D.Niltest (fun _ : X => 1))
      (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (_hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
      (W : ∀ j, Submodule ℝ (J j → ℝ))
      (_hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ W j)
      (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J d)))
      (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
      (F : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℝ)
      (_hF : F ∈ weightedSupportLE (Sum.elim (fun _ : X => 1) (lowTaggedWeight J d)) d)
      (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J d)) → ℤ)
      (start : X → ℤ) (q : ℕ) (_hq : 0 < q) (M : ℕ) (_hM : 0 < M)
      (a : (Σ j, J j) → ℤ)
      (_hhigh : ∀ j, d < j.val + 1 → ∀ i, a ⟨j, i⟩ = 0)
      (lengths : X → ℕ) (_hlengths : ∀ i, 0 < lengths i)
      (p : ℝ), 0 ≤ p → R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ p →
      (M : ℝ) ≤ Real.exp p → (Ψ.lip : ℝ) ≤ Real.exp p →
      (∀ i, |(a i : ℝ)| ≤ Real.exp p) →
      (∀ i, Real.exp ((p+C)^C) ≤ (lengths i : ℝ)) →
      (∀ v ∈ integerBox lengths, ∀ i,
        |MvPolynomial.eval (fun x => (start x : ℝ) + (q : ℝ) * v x)
          (lowTaggedPolynomial J d poly i) - c i -
          (β (fun x => start x + (q : ℤ) * v x) i : ℝ)| ≤ 1/2) →
      Real.exp (-p) ≤ ‖𝔼 v ∈ integerBox lengths,
        (Real.fourierChar (MvPolynomial.eval
          (fun i => (start i : ℝ) + (q : ℝ) * v i)
          (normalizedTwistFrequencyPolynomial M a poly)) : ℂ) *
          majorPhaseSample J d poly Ψ c F β R.eval
            (fun i => start i + (q : ℤ) * v i)‖ →
      (∀ h : Fin d, HasLayerSamplingRank (h.val + 1) (fun i => (lengths i : ℝ))
        (Real.exp ((p+C)^C)) (lowTaggedRetained J d W h)
        (lowTaggedTopPolynomial J d (fun j => residueAffine q start (poly j)))) →
      ∃ (fast : LieSubalgebra ℚ (weightedSubalgebra (lowTaggedWeight J d) d))
        (g : Fin (finrank ℚ (PairAlgebra (weightedSubalgebra (lowTaggedWeight J d) d) L)) →
          weightedSubalgebra (lowTaggedWeight J d) d)
        (Slow : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℝ)
        (RatPart : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℚ)
        (qOut : ℕ),
        (finrank ℚ (PairAlgebra (weightedSubalgebra (lowTaggedWeight J d) d) L) : ℝ) ≤ (p+C)^C ∧
        Submodule.span ℚ (Set.range g) = fast.toSubmodule ∧
        BasisGradedSubmodule (weightedBasis (lowTaggedWeight J d) d (lowTaggedWeight_pos J d))
          (weightedBasisGrade (lowTaggedWeight J d) d) fast.toSubmodule ∧
        (∀ j i, rationalLogHeight
          ((weightedBasis (lowTaggedWeight J d) d (lowTaggedWeight_pos J d)).repr (g j) i) ≤ (p+C)^C) ∧
        BasisGradedSubmodule (Pi.basisFun ℝ _) (lowTaggedWeight J d)
          ((fast.toSubmodule.baseChange ℝ).map
            (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra (lowTaggedWeight J d) d).subtype))) ∧
        (∀ h, lowTaggedRetained J d W h ≤ (fast.toSubmodule.baseChange ℝ).map
          (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra (lowTaggedWeight J d) d).subtype))) ∧
        realPolynomialMass Slow ≤ Real.exp ((p+C)^C) ∧
        (∀ α, |Slow.coeff α| ≤ Real.exp ((p+C)^C)) ∧
        0 < qOut ∧ (qOut : ℝ) ≤ Real.exp ((p+C)^C) ∧
        (fun α => RatPart.coeff α) ∈ denominatorGrid qOut ∧
        (∀ α, (RatPart.coeff α).den ≤ qOut) ∧
        Slow ∈ weightedSupportLE (Sum.elim (fun _ : X => 1) (lowTaggedWeight J d)) d ∧
        RatPart ∈ weightedSupportLE (Sum.elim (fun _ : X => 1) (lowTaggedWeight J d)) d ∧
        ∀ (u : X → ℝ) (z : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ),
          z ∈ (fast.toSubmodule.baseChange ℝ).map
            (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra (lowTaggedWeight J d) d).subtype)) →
          MvPolynomial.eval (Sum.elim u z)
            (weightedHomogeneousComponent (Sum.elim (fun _ : X => 1) (lowTaggedWeight J d)) d
              (jointResidueAffinePolynomial q start F)) =
            MvPolynomial.eval (Sum.elim (fun i => u i / (lengths i : ℝ))
              (fun j => z j - MvPolynomial.eval u
                (majorTranslationTopCoordinates (lowTaggedWeight J d)
                  (fun i => residueAffinePolynomial q start
                    (lowTaggedPolynomial J d poly i - MvPolynomial.C (c i))) j))) Slow +
              MvPolynomial.eval₂ (algebraMap ℚ ℝ) (Sum.elim u z) RatPart := by
  obtain ⟨aC, _, hprimitive⟩ := exists_majorRationalLift_detection_budget d
  obtain ⟨bC, _, hdetect⟩ :=
    exists_reduced_majorPolynomial_degree_twisted_correlation_decomposition d hd
  obtain ⟨C, hC, hbudget⟩ := exists_majorPhaseLowFourierExtraction_budget aC bC
  refine ⟨C, hC, ?_⟩
  intro m X L _ _ _ _ t e _ _ _ _ J _ _ D htd R poly hpoly W hcoeff Ψ c F hF β
    start q hq M hM a hhigh lengths hlengths p hp hR hcap hdim hMexp hΨ ha hlarge hβ hcorr hrank
  let w := lowTaggedWeight J d
  let hw := lowTaggedWeight_pos J d
  let hwd := lowTaggedWeight_le J d
  let := moduleTopology ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d) :=
    realification_moduleTopology_t2 (weightedBasis w d hw)
  let A := fun i => residueAffinePolynomial q start
    (lowTaggedPolynomial J d poly i - MvPolynomial.C (c i))
  let F' := jointResidueAffinePolynomial q start F
  let R' := R.scalarAffinePullback (q : ℚ) (fun i => (start i : ℚ))
  let β' := fun (v : X → ℤ) i => β (fun x => start x + (q : ℤ) * v x) i
  let T := rationalLiftCharacterTwist M (lowTaggedFrequency J d a) c
  let K := rationalLiftCharacterTwistLip M (lowTaggedFrequency J d a)
  let p' : ℝ := (p+aC)^aC+p+1
  have hpow : 0 ≤ (p+aC)^aC := by positivity
  have hpp' : p ≤ p' := by dsimp only [p']; linarith
  have hp' : 0 ≤ p' := hp.trans hpp'
  have hprimitive' : (p+aC)^aC ≤ p' := by dsimp only [p']; linarith
  have hfinal : (p'+bC)^bC ≤ (p+C)^C := (hbudget p hp).2.1
  have hdim' : ((Fintype.card X + Fintype.card (LowTaggedIndex J d) : ℕ) : ℝ) ≤ p := by
    apply le_trans _ hdim
    exact_mod_cast Nat.add_le_add_left (lowTaggedIndex_card_le J d) _
  obtain ⟨hgeometry, hlog⟩ := hprimitive (U := X) w hw hwd M hM Ψ
    (lowTaggedFrequency J d a) p hp hdim' hMexp hΨ (lowTaggedFrequency_bound J d a _ ha)
  have hA : ∀ i, (A i).totalDegree ≤ w i := fun i =>
    residueAffinePolynomial_totalDegree_le q start _ _
      ((MvPolynomial.totalDegree_sub_C_le _ _).trans (lowTaggedPolynomial_degree J d poly hpoly i))
  have hF' : F' ∈ weightedSupportLE (Sum.elim (fun _ : X => 1) w) d :=
    jointResidueAffinePolynomial_degree w q start hF
  have hzero : translatedIntegerBox (0 : X → ℤ) lengths = integerBox lengths := by
    ext v
    simp only [mem_translatedIntegerBox, mem_integerBox, Pi.zero_apply, zero_add]
  have hβ' : ∀ v ∈ translatedIntegerBox (0 : X → ℤ) lengths, ∀ i,
      |MvPolynomial.eval (fun x => (v x : ℝ)) (A i) - (β' v i : ℝ)| ≤ 1/2 := by
    rw [hzero]
    intro v hv i
    simpa only [A, β', residueAffinePolynomial_eval_real, map_sub, eval_C] using hβ v hv i
  have hcorr' : Real.exp (-p') ≤ ‖𝔼 v ∈ translatedIntegerBox (0 : X → ℤ) lengths,
      T (fun i => MvPolynomial.eval (fun x => (v x : ℝ)) (A i) - (β' v i : ℝ))
          (fun i => (β' v i : ZMod M)) *
        (Ψ.value (fun i => MvPolynomial.eval (fun x => (v x : ℝ)) (A i) - (β' v i : ℝ)) : ℂ) *
        (Real.fourierChar (MvPolynomial.eval (fun j => ((Sum.elim v (β' v) j : ℤ) : ℝ)) F') : ℂ) *
        R'.eval v‖ := by
    rw [hzero]
    apply (Real.exp_le_exp.mpr (neg_le_neg hpp')).trans
    convert hcorr using 1
    congr 1
    apply congrArg (fun z : ℂ => ‖z‖)
    apply Finset.expect_congr rfl
    intro v _
    have hcast : (fun j => ((Sum.elim v (β' v) j : ℤ) : ℝ)) =
        Sum.elim (fun i => (v i : ℝ)) (fun i => (β' v i : ℝ)) := by
      funext j
      cases j <;> rfl
    rw [hcast]
    simpa only [T, A, β', F', R', Function.comp_def] using
      (majorPhase_affine_integrand J d poly Ψ c F β R start q M hM a hhigh v).symm
  have htop : ofCoordinates (R := ℝ) (Pi.basisFun ℝ _)
      (fun i => weightedHomogeneousComponent (fun _ : X => 1) (w i) (A i)) =
      lowTaggedTopPolynomial J d (fun j => residueAffine q start (poly j)) := by
    exact lowTaggedTopPolynomial_centered_residueAffine J d poly q start c
  have hTpos (i : X) : 0 < (lengths i : ℝ) := by exact_mod_cast hlengths i
  have hrank' (h : Fin d) : HasLayerSamplingRank (h.val+1) (fun i => (lengths i : ℝ))
      (Real.exp ((p'+bC)^bC)) (lowTaggedRetained J d W h)
      (ofCoordinates (R := ℝ) (Pi.basisFun ℝ _)
        (fun i => weightedHomogeneousComponent (fun _ : X => 1) (w i) (A i))) := by
    rw [htop]
    exact (hrank h).mono (Real.exp_le_exp.mpr hfinal) hTpos
  have hcoeff' α : coefficients (ofCoordinates (R := ℝ) (Pi.basisFun ℝ _)
      (fun i => weightedHomogeneousComponent (fun _ : X => 1) (w i) (A i))) α ∈
      ⨆ h, lowTaggedRetained J d W h := by
    rw [htop]
    exact lowTaggedTopPolynomial_residueAffine_coeff_mem_iSup J d poly W hcoeff q start α
  have hX : (Fintype.card X : ℝ) ≤ p' := by
    apply le_trans _ (hdim'.trans hpp')
    exact_mod_cast Nat.le_add_right (Fintype.card X) (Fintype.card (LowTaggedIndex J d))
  obtain ⟨fast, g, Slow, RatPart, qOut, hdimOut, hg, hgraded, hheight, hbasegraded,
      hret, hmass, hslow, hqOut, hqbound, hgrid, hden, hSlowW, hRatW, hidentity⟩ :=
    hdetect w hw hwd M hM D htd Ψ F' hF' A hA K T
      (fun x r => (rationalLiftCharacterTwist_norm M (lowTaggedFrequency J d a) c x r).le)
      (rationalLiftCharacterTwist_lipschitz M (lowTaggedFrequency J d a) c)
      R' p' hp' (GeometryComplexityLE.mono _ hgeometry hprimitive') (hlog.trans hprimitive')
      (hR.mono hpp') hcap 0 lengths hlengths hX
      (fun i => (Real.exp_le_exp.mpr hfinal).trans (hlarge i)) β' hβ' hcorr'
      (lowTaggedRetained J d W) hrank' hcoeff'
  exact ⟨fast, g, Slow, RatPart, qOut, hdimOut.trans hfinal, hg, hgraded,
    (fun j i => (hheight j i).trans hfinal), hbasegraded, hret,
    hmass.trans (Real.exp_le_exp.mpr hfinal),
    (fun α => (hslow α).trans (Real.exp_le_exp.mpr hfinal)), hqOut,
    hqbound.trans (Real.exp_le_exp.mpr hfinal), hgrid, hden, hSlowW, hRatW, hidentity⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module RationalFilteredNilmanifold PolynomialTranslationLie
open scoped TensorProduct NNReal BigOperators

theorem exists_majorPhase_detected_decomposition (m d : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X L : Type} [Fintype X] [DecidableEq X]
      [LieRing L] [LieAlgebra ℚ L] {t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (J : Fin m → Type) [∀ j, Fintype (J j)]
      {periodCap coverCap : ℝ} {Lip : ℝ≥0}
      (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
      (D : RationalFilteredNilmanifold L t e) (_htd : t < d)
      (R : D.Niltest (fun _ : X => 1))
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (_hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (_hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
      (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J d)))
      (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
      (F : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℝ)
      (_hF : F ∈ weightedSupportLE
        (Sum.elim (fun _ : X => 1) (lowTaggedWeight J d)) d)
      (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J d)) → ℤ)
      (_hβ : ∀ u ∈ integerBox N, ∀ i,
        |MvPolynomial.eval (fun x => (u x : ℝ)) (lowTaggedPolynomial J d poly i) -
          c i - (β u i : ℝ)| ≤ 1 / 2)
      (p Rrank : ℝ), 0 ≤ p → R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ p →
      (W.modulus : ℝ) ≤ Real.exp p → (W.cover : ℝ) ≤ Real.exp p →
      (Lip : ℝ) ≤ Real.exp p → (Ψ.lip : ℝ) ≤ Real.exp p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (N i : ℝ)) →
      Real.exp ((p + C) ^ C) ≤ Rrank →
      (∀ j, HasLayerSamplingRank (j.val + 1)
        (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
      Real.exp (-p) ≤ ‖𝔼 u ∈ integerBox N,
        W.eval N poly u * majorPhaseSample J d poly Ψ c F β R.eval u‖ →
      MajorPhaseDetectedConclusion (L := L) J d U poly c F N ((p + C) ^ C) := by
  obtain ⟨aC, _, hextract⟩ := exists_majorPhase_low_localized_correlating_frequency m d
  obtain ⟨bC, _, hdetect⟩ := exists_majorPhase_residue_detection d hd
  obtain ⟨C, hC, hbudget⟩ := exists_majorPhaseDetectedDecomposition_budget aC bC 1 m d
  refine ⟨C, hC, ?_⟩
  intro X L _ _ _ _ t e _ _ _ _ J _ periodCap coverCap Lip W D htd R N poly hpoly U hcoeff
    Ψ c F hF β hβ p Rrank hp hR hcap hdim hmod hcover hLip hΨ hN hRrank hrank hcorr
  let E : ℝ := (p+aC)^aC
  let Q : ℝ := E+p+1
  let G : ℝ := (Q+bC)^bC
  let B : ℝ := (p+C)^C
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hpQ : p ≤ Q := by dsimp [Q]; linarith
  have hEQ : E ≤ Q := by dsimp [Q]; linarith
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hb : E ≤ B ∧ E+(G+Q+1) ≤ B ∧ (m : ℝ)*p+(G+Q+1) ≤ B ∧
    (m : ℝ)*E+(G+Q+1) ≤ B ∧ (d : ℝ)*E+(G+Q+1) ≤ B ∧
    (d : ℝ)*p+(G+Q+1) ≤ B ∧ G+Q+1 ≤ B := by
      simpa only [E, Q, G, B, Nat.cast_one, pow_one] using hbudget p hp
  obtain ⟨hEB, hEGB, hmp, hmE, hdE, hdp, hGB⟩ := hb
  have hGle : G ≤ B := by linarith
  have hEGle : E+G ≤ B := by linarith
  have hNpos (i : X) : 0 < (N i : ℝ) := (Real.exp_pos B).trans_le (hN i)
  obtain ⟨start, lengths, a, hlengths, hlengthLower, hcomparison, hinside,
      ha, hselected, hhigh, _⟩ :=
    hextract J W D htd.le R hd N poly hpoly U hcoeff Ψ c F hF β hβ p Rrank hp hR hcap
      hdim hmod hcover hLip hΨ
      (fun i => (Real.exp_le_exp.mpr hEB).trans (hN i))
      ((Real.exp_le_exp.mpr hEB).trans hRrank) (fun j _ => hrank j) hcorr
  have hlong (i : X) : Real.exp G ≤ (lengths i : ℝ) := by
    calc
      Real.exp G = Real.exp (E+G) * Real.exp (-E) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp B * Real.exp (-E) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hEGle) (Real.exp_nonneg _)
      _ ≤ (N i : ℝ) * Real.exp (-E) :=
        mul_le_mul_of_nonneg_right (hN i) (Real.exp_nonneg _)
      _ ≤ _ := hlengthLower i
  let startInt := fun i => (start i : ℤ)
  have hsliceRank := majorPhase_residue_lowTagged_rank J d poly hpoly U N lengths
    hNpos hlengths W.modulus W.modulus_pos startInt p E G B Rrank hp hE hmod hcomparison
    hGle (by linarith) (by linarith) hRrank hrank
  have hβslice : ∀ v ∈ integerBox lengths, ∀ i,
      |MvPolynomial.eval (fun x => (startInt x : ℝ) + (W.modulus : ℝ) * v x)
        (lowTaggedPolynomial J d poly i) - c i -
        (β (fun x => startInt x + (W.modulus : ℤ) * v x) i : ℝ)| ≤ 1/2 := by
    intro v hv i
    simpa only [startInt, Int.cast_add, Int.cast_mul, Int.cast_natCast] using
      hβ _ (hinside v hv) i
  have hselectedQ : Real.exp (-Q) ≤ ‖𝔼 v ∈ integerBox lengths,
      (Real.fourierChar (MvPolynomial.eval
        (fun i => (startInt i : ℝ) + (W.modulus : ℝ) * v i)
        (normalizedTwistFrequencyPolynomial W.cover a poly)) : ℂ) *
      majorPhaseSample J d poly Ψ c F β R.eval
        (fun i => startInt i + (W.modulus : ℤ) * v i)‖ := by
    simpa only [startInt, Int.cast_natCast] using
      (Real.exp_le_exp.mpr (neg_le_neg hEQ)).trans hselected
  let w := lowTaggedWeight J d
  let := weightedBasisIndex_finite w d (lowTaggedWeight_pos J d)
  let : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
  obtain ⟨fast, g, Slow, RatPart, qOut, hcount, hgspan, hgraded, hgheight, hKgraded,
      hretained, hmass, _, hqOut, hqBound, hgrid, _, hSlow, hRat, hidentity⟩ :=
    hdetect J D htd R poly hpoly U hcoeff Ψ c F hF β startInt W.modulus W.modulus_pos
      W.cover W.cover_pos a hhigh lengths hlengths Q hQ (hR.mono hpQ) hcap
      (hdim.trans hpQ) (hcover.trans (Real.exp_le_exp.mpr hpQ))
      (hΨ.trans (Real.exp_le_exp.mpr hpQ))
      (fun i => (ha i).trans (Real.exp_le_exp.mpr hEQ)) hlong hβslice hselectedQ hsliceRank
  let K := (fast.toSubmodule.baseChange ℝ).map
    (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype))
  let A := fun i => lowTaggedPolynomial J d poly i - MvPolynomial.C (c i)
  have hA : ∀ i, (A i).totalDegree ≤ w i := fun i =>
    (MvPolynomial.totalDegree_sub_C_le _ _).trans (lowTaggedPolynomial_degree J d poly hpoly i)
  obtain ⟨Slow', RatPart', _, _, hidentity', hmass', hSlow', hRat', _, _, hgrid'⟩ :=
    algebraic_major_weighted_affine_top_pullback_decomposition K w (lowTaggedWeight_pos J d)
      d F hF A hA Slow RatPart W.modulus W.modulus_pos startInt
      (fun i => (N i : ℝ)) (fun i => (lengths i : ℝ)) hNpos
      (fun i => Nat.cast_pos.mpr (hlengths i)) hidentity
      (Real.exp E) (Real.exp G) (Real.one_le_exp hE) hcomparison d qOut hSlow hRat hmass hgrid
  have hmassFinal : realPolynomialMass Slow' ≤ Real.exp B :=
    hmass'.trans (pow_mul_exp_le_exp_of_le_budget (Real.exp_nonneg E) le_rfl hE
      le_rfl (by linarith : (d : ℝ)*E+G ≤ B))
  have hdenFinal : ((W.modulus^d*qOut : ℕ) : ℝ) ≤ Real.exp B :=
    nat_pow_mul_le_exp_of_le_budget hmod hqBound (by linarith : (d : ℝ)*p+G ≤ B)
  have hdenPos : 0 < W.modulus^d*qOut := Nat.mul_pos (pow_pos W.modulus_pos _) hqOut
  refine ⟨fast, g, Slow', RatPart', W.modulus^d*qOut,
    hcount.trans hGle, hgspan, hgraded, (fun j i => (hgheight j i).trans hGle),
    hKgraded, hretained, hmassFinal, ?_, hdenPos, hdenFinal, hgrid', ?_,
    hSlow', hRat', hidentity'⟩
  · exact fun α => (realPolynomialMass_coeff_le Slow' α).trans hmassFinal
  · exact fun α => den_le_of_mem_denominatorGrid hdenPos hgrid' α

end Erdos3.VectorPolynomial

end

end OAI
