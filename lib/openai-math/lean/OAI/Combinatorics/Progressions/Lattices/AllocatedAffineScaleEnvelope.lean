import OAI.Combinatorics.Progressions.Dynamics.AllocatedReferenceIdealBudget

namespace OAI

section

namespace Erdos3

noncomputable def affineReferenceCoefficientLog {A : Type*} [Semiring A] (D L : A) : A :=
  8 * (D + 1) * (L + 1)

theorem affineReferenceCoefficient_bounds
    {D L dlog slog P ideal Ki Cmask boundary : ℝ}
    (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hdlog : dlog ≤ L) (hslog : slog ≤ L) (hP : P ≤ L)
    (hideal : ideal ≤ Real.exp L) (hKi : Ki ≤ Real.exp L)
    (hCmask0 : 0 ≤ Cmask) (hCmask : Cmask ≤ Real.exp L)
    (hb0 : 0 ≤ boundary) (hb : boundary ≤ Real.exp L)
    (axes output unselected integer : ℕ)
    (ha : (axes : ℝ) ≤ D) (ho : (output : ℝ) ≤ D)
    (hu : (unselected : ℝ) ≤ D) (hi : (integer : ℝ) ≤ D) :
    let cap := (Real.exp dlog) ^ axes
    let lip := (axes : ℝ) * Real.exp dlog * cap
    let radius := max (Real.exp P * ideal) (Real.exp slog)
    let mask := Cmask ^ axes
    let support := (2 * Real.exp slog) ^ output
    let Q := affineReferenceCoefficientLog D L
    mask ≤ Real.exp Q ∧
    mask * (2 * cap * boundary + lip * 2) * support ≤ Real.exp Q ∧
    mask * lip * support ≤ Real.exp Q ∧
    mask * (2 * radius) ^ unselected * ((2 * radius + 2) ^ integer * (Ki + lip)) ≤ Real.exp Q := by
  intro cap lip radius mask support Q
  have hDL : 0 ≤ D * L := mul_nonneg hD hL
  have hcap : cap ≤ Real.exp (D * L) :=
    pow_le_exp_mul_of_le_exp (Real.exp_pos _).le (Real.exp_le_exp.mpr hdlog) hL axes ha
  have hm : mask ≤ Real.exp (D * L) :=
    pow_le_exp_mul_of_le_exp hCmask0 hCmask hL axes ha
  have haxes : (axes : ℝ) ≤ Real.exp D := ha.trans (by linarith [Real.add_one_le_exp D])
  have hlip : lip ≤ Real.exp (D + L + D * L) := by
    calc
      _ ≤ Real.exp D * Real.exp L * Real.exp (D * L) := by dsimp [lip, cap]; gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hrad : radius ≤ Real.exp (2 * L) := by
    apply max_le
    · calc
        _ ≤ Real.exp P * Real.exp L := mul_le_mul_of_nonneg_left hideal (Real.exp_pos _).le
        _ ≤ Real.exp L * Real.exp L := by gcongr
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    · exact Real.exp_le_exp.mpr (by linarith)
  have hrad0 : 0 ≤ radius := (Real.exp_pos slog).le.trans (le_max_right _ _)
  have hsuppBase : 2 * Real.exp slog ≤ Real.exp (L + 2) := by
    calc
      _ ≤ Real.exp L * Real.exp 2 := by rw [mul_comm 2]; gcongr
      _ = _ := (Real.exp_add _ _).symm
  have hsupp : support ≤ Real.exp (D * (L + 2)) :=
    pow_le_exp_mul_of_le_exp (by positivity) hsuppBase (by positivity) output ho
  have hradBase : 2 * radius ≤ Real.exp (2 * L + 2) := by
    calc
      _ ≤ Real.exp (2 * L) * Real.exp 2 := by rw [mul_comm 2]; gcongr
      _ = _ := (Real.exp_add _ _).symm
  have hradPlus : 2 * radius + 2 ≤ Real.exp (2 * L + 4) := by
    have h1 : 1 ≤ Real.exp (2 * L) := Real.one_le_exp_iff.mpr (by positivity)
    calc
      _ ≤ 4 * Real.exp (2 * L) := by linarith only [hrad, h1]
      _ ≤ Real.exp (2 * L) * Real.exp 4 := by nlinarith [Real.exp_pos (2 * L)]
      _ = _ := (Real.exp_add _ _).symm
  have hru := pow_le_exp_mul_of_le_exp (mul_nonneg (by norm_num) hrad0) hradBase
    (by positivity : 0 ≤ 2 * L + 2) unselected hu
  have hri := pow_le_exp_mul_of_le_exp (by positivity : 0 ≤ 2 * radius + 2) hradPlus
    (by positivity : 0 ≤ 2 * L + 4) integer hi
  have hbl : 2 * cap * boundary ≤ Real.exp (D * L + L + 2) := by
    calc
      _ ≤ Real.exp (D * L) * Real.exp L * Real.exp 2 := by
        rw [show 2 * cap * boundary = cap * boundary * 2 by ring]
        gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]
  have hll : lip * 2 ≤ Real.exp (D + L + D * L + 2) := by
    calc
      _ ≤ Real.exp (D + L + D * L) * Real.exp 2 := by gcongr
      _ = _ := (Real.exp_add _ _).symm
  have hboundary := add_le_exp_add_one (by positivity : 0 ≤ D * L + L + 2)
    (by positivity : 0 ≤ D + L + D * L + 2) hbl hll
  have hsum := add_le_exp_add_one hL (by positivity : 0 ≤ D + L + D * L) hKi hlip
  have hlog₀ : D * L ≤ Q := by dsimp [Q, affineReferenceCoefficientLog]; nlinarith only [hDL, hD, hL]
  have hlog₁ : D * L + ((D * L + L + 2) + (D + L + D * L + 2) + 1) + D * (L + 2) ≤ Q := by
    dsimp [Q, affineReferenceCoefficientLog]; nlinarith only [hDL, hD, hL]
  have hlog₂ : D * L + (D + L + D * L) + D * (L + 2) ≤ Q := by
    dsimp [Q, affineReferenceCoefficientLog]; nlinarith only [hDL, hD, hL]
  have hlog₃ : D * L + D * (2 * L + 2) +
      (D * (2 * L + 4) + (L + (D + L + D * L) + 1)) ≤ Q := by
    dsimp [Q, affineReferenceCoefficientLog]; nlinarith only [hDL, hD, hL]
  refine ⟨hm.trans (Real.exp_le_exp.mpr hlog₀), ?_, ?_, ?_⟩
  · calc
      _ ≤ Real.exp (D * L) * Real.exp ((D * L + L + 2) + (D + L + D * L + 2) + 1) *
          Real.exp (D * (L + 2)) := by gcongr
      _ ≤ _ := by rw [← Real.exp_add, ← Real.exp_add]; exact Real.exp_le_exp.mpr hlog₁
  · calc
      _ ≤ Real.exp (D * L) * Real.exp (D + L + D * L) * Real.exp (D * (L + 2)) := by gcongr
      _ ≤ _ := by rw [← Real.exp_add, ← Real.exp_add]; exact Real.exp_le_exp.mpr hlog₂
  · by_cases hneg : Ki + lip < 0
    · exact (mul_nonpos_of_nonneg_of_nonpos (by positivity)
        (mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg.le)).trans (Real.exp_pos Q).le
    · have hsum0 := le_of_not_gt hneg
      calc
        _ ≤ Real.exp (D * L) * Real.exp (D * (2 * L + 2)) *
            (Real.exp (D * (2 * L + 4)) * Real.exp (L + (D + L + D * L) + 1)) := by gcongr
        _ ≤ _ := by simp only [← Real.exp_add]; exact Real.exp_le_exp.mpr hlog₃

theorem affineReferenceError_accuracy {target Q mask cap lip boundary support volume Ki η ratio ε mesh : ℝ}
    (hη0 : 0 ≤ η) (hratio0 : 0 ≤ ratio) (hε0 : 0 ≤ ε) (hmesh0 : 0 ≤ mesh)
    (hcoeff : mask ≤ Real.exp Q ∧
      mask * (2 * cap * boundary + lip * 2) * support ≤ Real.exp Q ∧
      mask * lip * support ≤ Real.exp Q ∧ mask * volume * (Ki + lip) ≤ Real.exp Q)
    (hη : η ≤ Real.exp (-(target + Q + 4)))
    (hratio : ratio ≤ Real.exp (-(target + Q + 4)))
    (hε : ε ≤ Real.exp (-(target + Q + 4)))
    (hmesh : mesh ≤ Real.exp (-(target + Q + 4))) :
    mask * (η + ((2 * cap * boundary + lip * 2) * ratio + lip * ε) * support +
      volume * (Ki + lip) * mesh) ≤ Real.exp (-target) := by
  have hterm {c x : ℝ} (hc : c ≤ Real.exp Q) (hx0 : 0 ≤ x)
      (hx : x ≤ Real.exp (-(target + Q + 4))) : c * x ≤ Real.exp (-(target + 4)) := by
    calc
      _ ≤ Real.exp Q * Real.exp (-(target + Q + 4)) :=
        (mul_le_mul_of_nonneg_right hc hx0).trans (mul_le_mul_of_nonneg_left hx (Real.exp_pos _).le)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have h₁ := hterm hcoeff.1 hη0 hη
  have h₂ := hterm hcoeff.2.1 hratio0 hratio
  have h₃ := hterm hcoeff.2.2.1 hε0 hε
  have h₄ := hterm hcoeff.2.2.2 hmesh0 hmesh
  have hsum : mask * (η + ((2 * cap * boundary + lip * 2) * ratio + lip * ε) * support +
      volume * (Ki + lip) * mesh) ≤ 4 * Real.exp (-(target + 4)) := by
    nlinarith only [h₁, h₂, h₃, h₄]
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  calc
    _ ≤ 4 * Real.exp (-(target + 4)) := hsum
    _ ≤ Real.exp 4 * Real.exp (-(target + 4)) := mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem affineReferenceError_accuracy_separated {target Q Qη mask cap lip boundary support volume Ki η ratio ε mesh : ℝ}
    (hη0 : 0 ≤ η) (hratio0 : 0 ≤ ratio) (hε0 : 0 ≤ ε) (hmesh0 : 0 ≤ mesh)
    (hcoeff : mask ≤ Real.exp Qη ∧
      mask * (2 * cap * boundary + lip * 2) * support ≤ Real.exp Q ∧
      mask * lip * support ≤ Real.exp Q ∧ mask * volume * (Ki + lip) ≤ Real.exp Q)
    (hη : η ≤ Real.exp (-(target + Qη + 4)))
    (hratio : ratio ≤ Real.exp (-(target + Q + 4)))
    (hε : ε ≤ Real.exp (-(target + Q + 4)))
    (hmesh : mesh ≤ Real.exp (-(target + Q + 4))) :
    mask * (η + ((2 * cap * boundary + lip * 2) * ratio + lip * ε) * support +
      volume * (Ki + lip) * mesh) ≤ Real.exp (-target) := by
  have hterm {c x Q : ℝ} (hc : c ≤ Real.exp Q) (hx0 : 0 ≤ x)
      (hx : x ≤ Real.exp (-(target + Q + 4))) : c * x ≤ Real.exp (-(target + 4)) := by
    calc
      _ ≤ Real.exp Q * Real.exp (-(target + Q + 4)) :=
        (mul_le_mul_of_nonneg_right hc hx0).trans (mul_le_mul_of_nonneg_left hx (Real.exp_pos _).le)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have h₁ := hterm hcoeff.1 hη0 hη
  have h₂ := hterm hcoeff.2.1 hratio0 hratio
  have h₃ := hterm hcoeff.2.2.1 hε0 hε
  have h₄ := hterm hcoeff.2.2.2 hmesh0 hmesh
  have hsum : mask * (η + ((2 * cap * boundary + lip * 2) * ratio + lip * ε) * support +
      volume * (Ki + lip) * mesh) ≤ 4 * Real.exp (-(target + 4)) := by
    nlinarith only [h₁, h₂, h₃, h₄]
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  calc
    _ ≤ 4 * Real.exp (-(target + 4)) := hsum
    _ ≤ Real.exp 4 * Real.exp (-(target + 4)) := mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical NNReal

def allocatedAffineL1Log {A : Type*} [Semiring A] (m : ℕ) (D P Prho Pk : A) : A :=
  P + ((m * 2 ^ (m + 1) : ℕ) * Pk + allocatedDensityEnvelope m D P) +
    allocatedSupportEnvelope m D P + allocatedIdealLipEnvelope D P Prho +
    ((m + 1 : ℕ) * D + 2) + scalarCubeRiemannLog D

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

theorem allocatedAffineL1_primitive_bounds {D P Prho Pk : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B α O D)
    (hP : 0 ≤ P) (hPrho : 0 ≤ Prho) (hPk : 0 ≤ Pk)
    {Mk : ℕ} (hMk : (Mk : ℝ) ≤ Real.exp Pk)
    (partition : LayerSamplerAxis I n → Prop)
    (R : Fin m → ℝ) (hR : ∀ j, 0 ≤ R j) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (ρ : ℝ≥0) (hρ : (ρ : ℝ)⁻¹ ≤ Real.exp Prho) :
    let L := allocatedAffineL1Log m D P Prho Pk
    let Output := Σ a : {a // ¬partition a}, O a.val.1
    0 ≤ L ∧ P ≤ L ∧
      allocatedDensityLog (G := G) B α O P ≤ L ∧
      allocatedJetSupportLog (G := G) B α O P ≤ L ∧
      (layerKernelIndexBound m Mk : ℝ) * Real.exp (allocatedDensityLog (G := G) B α O P) ≤ Real.exp L ∧
      partitionedIdealRadius α m + 1 ≤ Real.exp L ∧
      ‖(∏ o : Output, |R o.1.val.1|)⁻¹‖ *
        ((affineProductProfileLip Output ρ : ℝ) * Real.exp P) ≤ Real.exp L ∧
      ((m * 2 ^ (m + 1) : ℕ) : ℝ) * Pk ≤ L ∧
      scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) ≤ Real.exp L := by
  intro L Output
  have hD := hdim.nonneg
  have hden := allocatedDensityEnvelope_nonneg m hD hP
  have hsupp := allocatedSupportEnvelope_nonneg m hD hP
  have hindex : 0 ≤ ((m * 2 ^ (m + 1) : ℕ) : ℝ) * Pk := mul_nonneg (Nat.cast_nonneg _) hPk
  have hlip : 0 ≤ allocatedIdealLipEnvelope D P Prho := by
    unfold allocatedIdealLipEnvelope
    positivity
  have hradius : 0 ≤ ((m + 1 : ℕ) : ℝ) * D + 2 := by positivity
  have hboundary : 0 ≤ scalarCubeRiemannLog D := by unfold scalarCubeRiemannLog; positivity
  have hpieces : 0 ≤ L ∧ P ≤ L ∧
      ((m * 2 ^ (m + 1) : ℕ) : ℝ) * Pk + allocatedDensityEnvelope m D P ≤ L ∧
      allocatedSupportEnvelope m D P ≤ L ∧ allocatedIdealLipEnvelope D P Prho ≤ L ∧
      ((m + 1 : ℕ) : ℝ) * D + 2 ≤ L ∧ scalarCubeRiemannLog D ≤ L := by
    dsimp only [L, allocatedAffineL1Log]
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  have hdenL : allocatedDensityEnvelope m D P ≤ L := by linarith only [hpieces.2.2.1, hindex]
  refine ⟨hpieces.1, hpieces.2.1, (allocatedDensityLog_le_envelope B hdim hP).trans hdenL,
    (allocatedJetSupportLog_le_envelope B hdim hP).trans hpieces.2.2.2.1, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      _ ≤ Real.exp (((m * 2 ^ (m + 1) : ℕ) : ℝ) * Pk) * Real.exp (allocatedDensityEnvelope m D P) :=
        mul_le_mul (layerKernelIndexBound_le_exp m hMk)
          (Real.exp_le_exp.mpr (allocatedDensityLog_le_envelope B hdim hP)) (Real.exp_nonneg _) (Real.exp_nonneg _)
      _ ≤ _ := by rw [← Real.exp_add]; exact Real.exp_le_exp.mpr hpieces.2.2.1
  · apply (partitionedIdealRadius_add_one_le_exp α m).trans
    apply Real.exp_le_exp.mpr
    have hdim' := mul_le_mul_of_nonneg_left hdim.cube (by positivity : 0 ≤ (m : ℝ) + 1)
    have hb := hpieces.2.2.2.2.2.1
    push_cast at hb
    linarith
  · have hk := diagonalProfileLip_le_exp (fun o : Output => R o.1.val.1)
      (fun o => hR o.1.val.1) hP hPrho (hdim.active_outputs B partition) hdim.profile
      (fun o => hRi o.1.val.1) hρ
    simp only [NNReal.coe_mul, NNReal.coe_mk, coe_nnnorm] at hk
    simp_rw [abs_of_nonneg (hR _)]
    exact hk.trans (Real.exp_le_exp.mpr hpieces.2.2.2.2.1)
  · linarith only [hpieces.2.2.1, hden]
  · exact (scalarCubeRiemannBoundary_le_exp α hD hdim.cube).trans
      (Real.exp_le_exp.mpr hpieces.2.2.2.2.2.2)

theorem exists_allocatedAffineL1Log_bound (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ D P Prho Pk : ℝ,
      0 ≤ D → 0 ≤ P → 0 ≤ Prho → 0 ≤ Pk →
      allocatedAffineL1Log m D P Prho Pk ≤ (D + P + Prho + Pk + A) ^ A := by
  let X : Polynomial ℕ := Polynomial.X
  let poly := allocatedAffineL1Log m X X X X
  obtain ⟨A, hA, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨A, hA, ?_⟩
  intro D P Prho Pk hD hP hPrho hPk
  let Q := D + P + Prho + Pk
  have hQ : 0 ≤ Q := by dsimp [Q]; linarith
  have hDQ : D ≤ Q := by dsimp [Q]; linarith
  have hPQ : P ≤ Q := by dsimp [Q]; linarith
  have hrQ : Prho ≤ Q := by dsimp [Q]; linarith
  have hkQ : Pk ≤ Q := by dsimp [Q]; linarith
  have hkernel : kernelOutputEnvelope D (4 * (P + 8)) ≤ kernelOutputEnvelope Q (4 * (Q + 8)) := by
    unfold kernelOutputEnvelope kernelGeometryEnvelope kernelInverseEnvelope
    gcongr
  have hden : allocatedDensityEnvelope m D P ≤ allocatedDensityEnvelope m Q Q := by
    unfold allocatedDensityEnvelope
    gcongr
  have hsupp : allocatedSupportEnvelope m D P ≤ allocatedSupportEnvelope m Q Q := by
    unfold allocatedSupportEnvelope
    gcongr
  have hmono : allocatedAffineL1Log m D P Prho Pk ≤ allocatedAffineL1Log m Q Q Q Q := by
    unfold allocatedAffineL1Log allocatedIdealLipEnvelope scalarCubeRiemannLog
    gcongr
  apply hmono.trans
  simpa [poly, X, allocatedAffineL1Log, allocatedDensityEnvelope, allocatedSupportEnvelope,
    allocatedIdealLipEnvelope, scalarCubeRiemannLog, kernelOutputEnvelope,
    kernelGeometryEnvelope, kernelInverseEnvelope, Polynomial.eval₂_pow, Nat.cast_add, Nat.cast_mul]
    using hbound Q hQ

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

noncomputable def allocatedAffineCoefficientAccuracyLog {A : Type*} [Semiring A]
    (m : ℕ) (D P Prho Pk target : A) : A :=
  target + 1 + coefficientReplacementErrorLog D (allocatedAffineL1Log m D P Prho Pk)

noncomputable def allocatedAffineReferenceAccuracyLog {A : Type*} [Semiring A]
    (m : ℕ) (D P Prho Pk target : A) : A :=
  target + 1 + affineReferenceCoefficientLog D (allocatedAffineL1Log m D P Prho Pk) + 4

noncomputable def allocatedAffineLengthLog {A : Type*} [Semiring A]
    (m : ℕ) (D P Prho Pk target F T : A) : A :=
  m * allocatedFrontEnvelope m D P (allocatedAffineCoefficientAccuracyLog m D P Prho Pk target) +
    progressionSliceLengthLog D (allocatedAffineReferenceAccuracyLog m D P Prho Pk target) F T

 theorem allocatedAffineL1Log_nonneg (m : ℕ) {D P Prho Pk : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hr : 0 ≤ Prho) (hk : 0 ≤ Pk) :
    0 ≤ allocatedAffineL1Log m D P Prho Pk := by
  have hd := allocatedDensityEnvelope_nonneg m hD hP
  have hs := allocatedSupportEnvelope_nonneg m hD hP
  dsimp only [allocatedAffineL1Log, allocatedIdealLipEnvelope, scalarCubeRiemannLog]
  positivity

 theorem allocatedAffineLengthLog_bounds (m : ℕ) {D P Prho Pk target F T : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hr : 0 ≤ Prho) (hk : 0 ≤ Pk)
    (ht : 0 ≤ target) (hF : 0 ≤ F) (hT : 0 ≤ T) :
    let e := allocatedAffineCoefficientAccuracyLog m D P Prho Pk target
    let E := allocatedAffineReferenceAccuracyLog m D P Prho Pk target
    let L := allocatedAffineLengthLog m D P Prho Pk target F T
    0 ≤ e ∧ 0 ≤ E ∧ 0 ≤ L ∧ E ≤ L ∧
      (m : ℝ) * allocatedFrontEnvelope m D P e ≤ L ∧
      progressionSliceLengthLog D E F T ≤ L := by
  intro e E L
  have hb := allocatedAffineL1Log_nonneg m hD hP hr hk
  have he : 0 ≤ e := by dsimp [e, allocatedAffineCoefficientAccuracyLog, coefficientReplacementErrorLog]; positivity
  have hE : 0 ≤ E := by dsimp [E, allocatedAffineReferenceAccuracyLog, affineReferenceCoefficientLog]; positivity
  have hki := kernelInverseEnvelope_nonneg hD hP
  have hf : 0 ≤ (m : ℝ) * allocatedFrontEnvelope m D P e := by
    dsimp [allocatedFrontEnvelope, allocatedKernelEnvelope]; positivity
  have hs : 0 ≤ progressionSliceLengthLog D E F T := by
    dsimp [progressionSliceLengthLog, scalarCubeRiemannLog]; positivity
  have hEL : E ≤ progressionSliceLengthLog D E F T := by
    have hB : 0 ≤ scalarCubeRiemannLog D := by unfold scalarCubeRiemannLog; positivity
    dsimp only [progressionSliceLengthLog]; linarith
  refine ⟨he, hE, add_nonneg hf hs, ?_, le_add_of_nonneg_right hs, le_add_of_nonneg_left hf⟩
  exact hEL.trans (le_add_of_nonneg_left hf)

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

noncomputable def allocatedAffineScale (D P Prho Pk target F T : ℝ) :
    LayerSamplerScale (G := G) B U basis R σ :=
  selectedLayerSamplerScale B U basis R σ hR hσ
    ⌈Real.exp (allocatedAffineLengthLog m D P Prho Pk target F T)⌉₊

 theorem allocatedAffineScale_lower (D P Prho Pk target F T : ℝ) :
    Real.exp (allocatedAffineLengthLog m D P Prho Pk target F T) ≤
      ((allocatedAffineScale (G := G) B U basis hR hσ D P Prho Pk target F T).value : ℝ) :=
  (Nat.le_ceil _).trans (Nat.cast_le.mpr
    (selectedLayerSamplerScale_bounds B U basis R σ hR hσ _).1)

 theorem allocatedAffineScale_upper {D P Prho Pk target F T : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B α O D)
    (hP : 0 ≤ P) (hr : 0 ≤ Prho) (hk : 0 ≤ Pk) (ht : 0 ≤ target)
    (hF : 0 ≤ F) (hT : 0 ≤ T)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P) :
    ((allocatedAffineScale (G := G) B U basis hR hσ D P Prho Pk target F T).value : ℝ) ≤
      Real.exp (allocatedScaleLog (D + P + allocatedAffineLengthLog m D P Prho Pk target F T + 1)) := by
  let L := allocatedAffineLengthLog m D P Prho Pk target F T
  let Q := D + P + L + 1
  have hD := hdim.nonneg
  have hL := (allocatedAffineLengthLog_bounds m hD hP hr hk ht hF hT).2.2.1
  have hQ : 0 ≤ Q := by dsimp [Q]; linarith
  have hDQ : D ≤ Q := by dsimp [Q]; linarith
  have hPQ : P ≤ Q := by dsimp [Q]; linarith
  have hLQ : L + 1 ≤ Q := by dsimp [Q]; linarith
  apply selectedLayerSamplerScale_exp_bound B U basis R σ hR hσ _ hQ
    (hdim.degree.trans hDQ) (fun j => (hdim.integer_axes B j).trans hDQ)
    (fun j => (hRi j).trans (Real.exp_le_exp.mpr hPQ))
    (fun j => (hσi j).trans (Real.exp_le_exp.mpr hPQ))
    (fun j => (hdim.coefficients j).trans hDQ)
  · exact (hdim.profile.trans hDQ).trans (by linarith [Real.add_one_le_exp Q])
  · exact (natCeil_le_exp_succ_of_le hL le_rfl).trans (Real.exp_le_exp.mpr hLQ)

 theorem allocatedAffineLength_ready {D P Prho Pk target F T : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B α O D)
    (hP : 0 ≤ P) (hr : 0 ≤ Prho) (hk : 0 ≤ Pk) (ht : 0 ≤ target)
    (hF : 0 ≤ F) (hT : 0 ≤ T)
    (S : LayerSamplerScale (G := G) B U basis R σ)
    (hS : Real.exp (allocatedAffineLengthLog m D P Prho Pk target F T) ≤ S.value) :
    let e := allocatedAffineCoefficientAccuracyLog m D P Prho Pk target
    let E := allocatedAffineReferenceAccuracyLog m D P Prho Pk target
    Real.exp (allocatedKernelReplacementLog (G := G) B α O P e) ≤ S.value ∧
      1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ Real.exp (-E) ∧
      Real.exp (progressionSliceLengthLog D E F T) ≤ S.value := by
  intro e E
  obtain ⟨he, hE, _, hEL, hf, hs⟩ :=
    allocatedAffineLengthLog_bounds m hdim.nonneg hP hr hk ht hF hT
  refine ⟨?_, ?_, (Real.exp_le_exp.mpr hs).trans hS⟩
  · exact (Real.exp_le_exp.mpr ((allocatedKernelReplacementLog_le_envelope B hdim hP).trans hf)).trans hS
  · have hES : Real.exp E ≤ S.value := (Real.exp_le_exp.mpr hEL).trans hS
    have hS1 : (1 : ℝ) ≤ S.value := (Real.one_le_exp_iff.mpr hE).trans hES
    have hpow : (S.value : ℝ) ≤ (S.value : ℝ) ^ (layerTailDegree m + 1) := by
      simpa only [pow_one] using pow_le_pow_right₀ hS1 (Nat.succ_le_succ (Nat.zero_le _))
    calc
      _ ≤ 1 / Real.exp E := one_div_le_one_div_of_le (Real.exp_pos _) (hES.trans hpow)
      _ = _ := by rw [Real.exp_neg, one_div]

 theorem AllocatedComparisonDimensions.active_tuples {D : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B α O D)
    (partition : LayerSamplerAxis I n → Prop) :
    (Fintype.card (PrincipalTupleIndex (fun a : {a // ¬partition a} => B a.val)
      (fun a => layerSamplerDegree I n a.val)) : ℝ) ≤ D :=
  (Nat.cast_le.mpr (dependentAxis_card_restrict_le
    (fun a => B a × Fin (layerSamplerDegree I n a)) (fun a => ¬partition a))).trans hdim.tuples

 theorem allocatedAffineLength_slice_ready [DecidableEq α]
    {D P Prho Pk target F T δ : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B α O D)
    (hP : 0 ≤ P) (hr : 0 ≤ Prho) (hk : 0 ≤ Pk) (ht : 0 ≤ target)
    (hF : 0 ≤ F) (hT : 0 ≤ T)
    (S : LayerSamplerScale (G := G) B U basis R σ)
    (hS : Real.exp (allocatedAffineLengthLog m D P Prho Pk target F T) ≤ S.value)
    (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
    (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S j : ℤ))
    (hδ : 0 < δ) (hδF : δ⁻¹ ≤ Real.exp F)
    (modulus : ℕ) (hm : 0 < modulus) (hmT : (modulus : ℝ) ≤ Real.exp T) :
    let grid := allocatedGridAxis (I := I) U basis S.value
    let Tuple := PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
      (fun a => layerSamplerDegree I n a.val)
    let embed := fun j : Tuple => (⟨j.1.val, j.2⟩ : PrincipalTupleIndex B (layerSamplerDegree I n))
    let E := allocatedAffineReferenceAccuracyLog m D P Prho Pk target
    (∀ j : Tuple, 0 < step (embed j)) →
    (∀ j : Tuple, δ * allocatedPrincipalSides B U basis S (embed j) ≤
      ((integerProgressionSupport (c (embed j)) (step (embed j) : ℤ) (H (embed j))).card : ℝ)) →
    (∀ j : Tuple, 2 ≤ H (embed j)) ∧
    (∀ j : Tuple, (Fintype.card α + 1) * modulus ≤ H (embed j)) ∧
    (∀ j : Tuple, scalarCubeGridBoundaryConstant α * ((modulus : ℝ) / H (embed j)) <
      MeasureTheory.volume.real (scalarCubeDomain α)) ∧
    (∑ j : Tuple, (modulus : ℝ) / H (embed j)) ≤ Real.exp (-E) ∧
    (∀ j : Tuple, (step (embed j) : ℝ) / allocatedPrincipalSides B U basis S (embed j) ≤
      Real.exp (-E)) := by
  intro grid Tuple embed E hstep hdense
  have hlen (j : Tuple) : allocatedPrincipalSides B U basis S (embed j) = S.value :=
    allocatedPrincipalSides_long B U basis S j.1.val j.1.property j.2.1 j.2.2
  have hready := allocatedAffineLength_ready B U basis hdim hP hr hk ht hF hT S hS
  have hE := (allocatedAffineLengthLog_bounds m hdim.nonneg hP hr hk ht hF hT).2.1
  have hslices := progressionSlice_scale_bounds (α := α)
    (fun j : Tuple => H (embed j)) (fun j : Tuple => step (embed j)) (fun j : Tuple => c (embed j))
    hdim.nonneg hE hF hT (hdim.active_tuples B grid) hdim.cube hδ hδF hm hmT hready.2.2 hstep
    (fun j => by simpa only [hlen j] using hsubset (embed j))
    (fun j => by simpa only [hlen j] using hdense j)
  simpa only [hlen] using hslices

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem allocatedAffineLengthLog_kernel_bound {m : ℕ} (hm : 0 < m)
    {D P Prho Pk target F T : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hr : 0 ≤ Prho) (hk : 0 ≤ Pk)
    (ht : 0 ≤ target) (hF : 0 ≤ F) (hT : 0 ≤ T) :
    Pk ≤ allocatedAffineLengthLog m D P Prho Pk target F T := by
  let L := allocatedAffineL1Log m D P Prho Pk
  have hL : 0 ≤ L := allocatedAffineL1Log_nonneg m hD hP hr hk
  have hd := allocatedDensityEnvelope_nonneg m hD hP
  have hs := allocatedSupportEnvelope_nonneg m hD hP
  have hi : 0 ≤ allocatedIdealLipEnvelope D P Prho := by
    unfold allocatedIdealLipEnvelope
    positivity
  have hb : 0 ≤ scalarCubeRiemannLog D := by unfold scalarCubeRiemannLog; positivity
  have hc : (1 : ℝ) ≤ ((m * 2 ^ (m + 1) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mul_pos hm (pow_pos (by decide : 0 < (2 : ℕ)) _))
  have hkL : Pk ≤ L := by
    have hprod := mul_le_mul_of_nonneg_right hc hk
    dsimp only [L, allocatedAffineL1Log]
    have hrad : 0 ≤ ((m + 1 : ℕ) : ℝ) * D := mul_nonneg (Nat.cast_nonneg _) hD
    nlinarith
  have hLE : L ≤ allocatedAffineReferenceAccuracyLog m D P Prho Pk target := by
    have hp := mul_nonneg hD (add_nonneg hL zero_le_one)
    dsimp only [allocatedAffineReferenceAccuracyLog, affineReferenceCoefficientLog]
    change L ≤ target + 1 + 8 * (D + 1) * (L + 1) + 4
    nlinarith
  exact hkL.trans (hLE.trans (allocatedAffineLengthLog_bounds m hD hP hr hk ht hF hT).2.2.2.1)

theorem allocatedAffineLength_kernel_ready {m : ℕ} (hm : 0 < m)
    {D P Prho Pk target F T : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hr : 0 ≤ Prho) (hk : 0 ≤ Pk)
    (ht : 0 ≤ target) (hF : 0 ≤ F) (hT : 0 ≤ T)
    {Mk S : ℕ} (hMk : (Mk : ℝ) ≤ Real.exp Pk)
    (hS : Real.exp (allocatedAffineLengthLog m D P Prho Pk target F T) ≤ (S : ℝ)) : Mk ≤ S := by
  exact_mod_cast hMk.trans ((Real.exp_le_exp.mpr
    (allocatedAffineLengthLog_kernel_bound hm hD hP hr hk ht hF hT)).trans hS)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedAffineScalePolynomial {A : Type*} [Semiring A]
    (m : ℕ) (D P Lb target F T : A) : A :=
  let e := target + 1 + coefficientReplacementErrorLog D Lb
  let E := target + 1 + affineReferenceCoefficientLog D Lb + 4
  let Q := D + P + (m * allocatedFrontEnvelope m D P e + progressionSliceLengthLog D E F T) + 1
  (1 + Q ^ 2) * (5 * Q + 49)

 theorem exists_allocatedAffineScaleLog_bound (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ D P Prho Pk target F T : ℝ,
      0 ≤ D → 0 ≤ P → 0 ≤ Prho → 0 ≤ Pk → 0 ≤ target → 0 ≤ F → 0 ≤ T →
      allocatedScaleLog (D + P + allocatedAffineLengthLog m D P Prho Pk target F T + 1) ≤
        (D + P + Prho + Pk + target + F + T + A) ^ A := by
  obtain ⟨b, hb, hLb⟩ := exists_allocatedAffineL1Log_bound m
  let X : Polynomial ℕ := Polynomial.X
  let poly := allocatedAffineScalePolynomial m X X ((X + Polynomial.C b) ^ b) X X X
  obtain ⟨A, hA, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨A, hA, ?_⟩
  intro D P Prho Pk target F T hD hP hr hk ht hF hT
  let Q := D + P + Prho + Pk + target + F + T
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hDQ : D ≤ Q := by dsimp [Q]; linarith
  have hPQ : P ≤ Q := by dsimp [Q]; linarith
  have htQ : target ≤ Q := by dsimp [Q]; linarith
  have hFQ : F ≤ Q := by dsimp [Q]; linarith
  have hTQ : T ≤ Q := by dsimp [Q]; linarith
  have hl0 := allocatedAffineL1Log_nonneg m hD hP hr hk
  have hl : allocatedAffineL1Log m D P Prho Pk ≤ (Q + b) ^ b := by
    apply (hLb D P Prho Pk hD hP hr hk).trans
    apply pow_le_pow_left₀ (by positivity)
    dsimp [Q]; linarith
  have he : allocatedAffineCoefficientAccuracyLog m D P Prho Pk target ≤
      Q + 1 + coefficientReplacementErrorLog Q ((Q + b) ^ b) := by
    dsimp only [allocatedAffineCoefficientAccuracyLog, coefficientReplacementErrorLog]
    gcongr
  have hE : allocatedAffineReferenceAccuracyLog m D P Prho Pk target ≤
      Q + 1 + affineReferenceCoefficientLog Q ((Q + b) ^ b) + 4 := by
    dsimp only [allocatedAffineReferenceAccuracyLog, affineReferenceCoefficientLog]
    gcongr
  have hi : kernelInverseEnvelope D P ≤ kernelInverseEnvelope Q Q := by
    unfold kernelInverseEnvelope
    gcongr
  have hfront : allocatedFrontEnvelope m D P (allocatedAffineCoefficientAccuracyLog m D P Prho Pk target) ≤
      allocatedFrontEnvelope m Q Q (Q + 1 + coefficientReplacementErrorLog Q ((Q + b) ^ b)) := by
    have hki := kernelInverseEnvelope_nonneg hD hP
    dsimp only [allocatedFrontEnvelope, allocatedKernelEnvelope]
    gcongr
  have hslice : progressionSliceLengthLog D (allocatedAffineReferenceAccuracyLog m D P Prho Pk target) F T ≤
      progressionSliceLengthLog Q (Q + 1 + affineReferenceCoefficientLog Q ((Q + b) ^ b) + 4) Q Q := by
    dsimp only [progressionSliceLengthLog, scalarCubeRiemannLog]
    gcongr
  have hL0 := (allocatedAffineLengthLog_bounds m hD hP hr hk ht hF hT).2.2.1
  have hL : allocatedAffineLengthLog m D P Prho Pk target F T ≤
      (m : ℝ) * allocatedFrontEnvelope m Q Q (Q + 1 + coefficientReplacementErrorLog Q ((Q + b) ^ b)) +
        progressionSliceLengthLog Q (Q + 1 + affineReferenceCoefficientLog Q ((Q + b) ^ b) + 4) Q Q := by
    exact add_le_add (mul_le_mul_of_nonneg_left hfront (Nat.cast_nonneg _)) hslice
  have hmono : allocatedScaleLog (D + P + allocatedAffineLengthLog m D P Prho Pk target F T + 1) ≤
      allocatedAffineScalePolynomial m Q Q ((Q + b) ^ b) Q Q Q := by
    dsimp only [allocatedScaleLog, allocatedAffineScalePolynomial]
    gcongr
  apply hmono.trans
  simpa [poly, X, allocatedAffineScalePolynomial, allocatedFrontEnvelope, allocatedKernelEnvelope,
    kernelInverseEnvelope, kernelGeometryEnvelope, coefficientReplacementErrorLog,
    affineReferenceCoefficientLog, progressionSliceLengthLog, scalarCubeRiemannLog,
    Polynomial.eval₂_pow] using hbound Q hQ

end Erdos3.VectorPolynomial

end

end OAI
