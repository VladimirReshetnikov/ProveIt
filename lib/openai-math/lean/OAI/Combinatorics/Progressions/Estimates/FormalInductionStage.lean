import OAI.Combinatorics.Progressions.Dynamics.FormalStageBudget
import OAI.Combinatorics.Progressions.Nilpotent.UniformControlledBracketStage

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_formal_induction_stage (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L μ ι κ ν τ σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype μ] [Fintype ι] [Fintype κ] [Fintype ν] [Fintype τ] [Fintype σ]
    (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
    (_hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
    (_hgraded : BasisHomogeneousBrackets b w) (_hs : 2 ≤ s)
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)) (V K Ebr Ecur : Submodule ℚ L)
    (_hUV : ∀ u ∈ U, ∀ v ∈ V.baseChange ℝ, ⁅u, v⁆ ∈ V.baseChange ℝ)
    (_hV : BasisGradedSubmodule (b.baseChange ℝ) w (V.baseChange ℝ))
    (eK : Basis κ ℚ K) (eBr : Basis ν ℚ Ebr) (eCur : Basis τ ℚ Ecur)
    (f : Basis ι ℚ (L ⧸ V))
    (_hK : ∀ x ∈ K.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w 1 x = x)
    {j H : ℕ} (_hj : 2 ≤ j) (_hH : 1 ≤ H)
    (_hBrGrade : ∀ x ∈ Ebr.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w (j - 1) x = x)
    (_hBrU : Ebr.baseChange ℝ ≤ U.toSubmodule)
    (_hBrK : j = 2 → Ebr.baseChange ℝ ≤ K.baseChange ℝ)
    (_hBrV : 2 < j → Ebr.baseChange ℝ ≤ V.baseChange ℝ)
    (_hCurGrade : ∀ x ∈ Ecur.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w j x = x)
    (_hCurU : Ecur.baseChange ℝ ≤ U.toSubmodule)
    (_hCurProjection : ∀ x ∈ U, basisGradeProjection (b.baseChange ℝ) w j x ∈ Ecur.baseChange ℝ)
    (_hBracketMatrix : ∀ i z, RationalHeightLE (bracketSystemMatrix eBr f (fun z => (eK z : L)) i z) H)
    (_hCurrentMatrix : ∀ i z, RationalHeightLE (subspaceQuotientMatrix eCur f i z) H)
    (_hKernelBasis : ∀ i z, RationalHeightLE (b.repr (eK z : L) i) H)
    (_hBracketBasis : ∀ i z, RationalHeightLE (b.repr (eBr z : L) i) H)
    (_hCurrentBasis : ∀ i z, RationalHeightLE (b.repr (eCur z : L) i) H)
    (_hQuotient : ∀ i z, RationalHeightLE (f.repr (V.mkQ (b z)) i) H)
    (_hStructure : ∀ i z r, RationalHeightLE (b.repr ⁅b i, b z⁆ r) H)
    {p : ℝ} (_hp : 0 ≤ p)
    (_hμ : (Fintype.card μ : ℝ) ≤ p) (_hι : (Fintype.card ι : ℝ) ≤ p)
    (_hκ : (Fintype.card κ : ℝ) ≤ p) (_hν : (Fintype.card ν : ℝ) ≤ p)
    (_hτ : (Fintype.card τ : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hjp : (j : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (X : F.FormalInductionState b w U V K eK T j p)
    (_hBracketSource : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1)
      (coefficients X.P.coord α) ∈ Ebr.baseChange ℝ),
    ∃ (Y : F.FormalInductionState b w U V K eK T (j + 1) ((p + C) ^ C))
      (A₁ A₂ B₁ B₂ : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot),
      (A₁ * A₂) * Y.P * (B₂ * B₁) = X.P ∧
      (∀ α, coefficients A₁.coord α ∈ U ∧ coefficients A₂.coord α ∈ U ∧
        coefficients B₁.coord α ∈ U ∧ coefficients B₂.coord α ∈ U) ∧
      (A₁.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
        A₂.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
        B₁.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
        B₂.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)) ∧
      (coefficients A₁.coord 0 = 0 ∧ coefficients A₂.coord 0 = 0 ∧
        coefficients B₁.coord 0 = 0 ∧ coefficients B₂.coord 0 = 0) ∧
      CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + C) ^ C)) A₁.coord ∧
      CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + C) ^ C)) A₂.coord ∧
      CoefficientGrid (b.baseChange ℝ) Y.denominator B₁.coord ∧
      CoefficientGrid (b.baseChange ℝ) Y.denominator B₂.coord := by
  classical
  obtain ⟨D, _, hbracketStage⟩ := exists_uniform_controlled_bracket_stage s
  obtain ⟨E, _, hcurrentStage⟩ := exists_uniform_controlled_current_stage s
  obtain ⟨C, hC, hbudget⟩ := exists_formal_stage_budget D E
  refine ⟨C, hC, ?_⟩
  intro L μ ι κ ν τ σ _ _ _ _ _ _ _ _ F b w hF hgraded hs U V K Ebr Ecur hUV hV
    eK eBr eCur f hK j H hj hH hBrGrade hBrU hBrK hBrV hCurGrade hCurU hCurProjection
    hBracketMatrix hCurrentMatrix hKernelBasis hBracketBasis hCurrentBasis hQuotient hStructure
    p hp hμ hι hκ hν hτ hσ hjp hHp T hT X hBracketSource
  let d := (p + D) ^ D
  let t := p + d
  let u := bracketTransitionBudget t
  let v := bracketConstructionBudget u
  let q := u + v
  let z := (q + E) ^ E
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hu : 0 ≤ u := bracketTransitionBudget_nonneg ht
  have hv : 0 ≤ v := bracketConstructionBudget_nonneg hu
  have hq : 0 ≤ q := add_nonneg hu hv
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hpt : p ≤ t := le_add_of_nonneg_right hd
  have htu : t ≤ u := le_bracketTransitionBudget ht
  have huv : u ≤ v := (bracket_construction_budget_bounds hu).1
  have huq : u ≤ q := le_add_of_nonneg_right hv
  have hvq : v ≤ q := le_add_of_nonneg_left hu
  have hpu : p ≤ u := hpt.trans htu
  have hpq : p ≤ q := hpu.trans huq
  have hcap : d + z + 1 ≤ (p + C) ^ C := hbudget p hp
  have hdCap : d ≤ (p + C) ^ C := by linarith
  have hzCap : z ≤ (p + C) ^ C := by linarith
  have hsumCap : d + z ≤ (p + C) ^ C := by linarith
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hTD : ∀ i, Real.exp ((p + D) ^ D) ≤ T i :=
    fun i => (Real.exp_le_exp.mpr hdCap).trans (hT i)
  have hk (r : κ) : basisGradeProjection (b.baseChange ℝ) w 1 ((1 : ℝ) ⊗ₜ[ℚ] (eK r : L)) =
      (1 : ℝ) ⊗ₜ[ℚ] (eK r : L) := by
    have h := hK _ (bracketSystemLift_mem eK (Pi.single r 1))
    rw [bracketSystemLift_single] at h
    exact h
  obtain ⟨n₀, A₁, B₁, hn₀, hn₀bound, hAB₁, hAhom₁, hBhom₁, hAnorm₁, hBgrid₁,
    hprod₁, hconstant₁, hgraded₁, hU₁, hbelow₁, hbrackets₁, hlifts₁, hrems₁,
    hrawSystem, hliftControls₁, hderivControls₁⟩ :=
    hbracketStage F b w hF hgraded hs U hUV hV eBr f (fun r => (eK r : L)) hk hj
      hBrGrade hBrU hH X.denominator_pos hBracketMatrix hBracketBasis hQuotient hStructure hp
      hμ hι hκ hν hσ hHp hHp hHp X.denominator_bound T hTD X.P X.mem_U X.graded
      hBracketSource X.S X.R X.lift_system X.S_shift X.R_shift X.S_remainder X.R_remainder
      X.lower_bracket X.S_bound X.R_grid X.small X.rational
      (fun i => basisPolynomialLift (Pi.basisFun ℝ κ) X.S (X.k i)) X.derivative_system
      X.small_shift X.rational_shift X.small_bound X.rational_grid
  let P₁ := A₁⁻¹ * X.P * B₁⁻¹
  let S₁ := fun r => dualAdjoint A₁⁻¹ (X.S r)
  let R₁ := fun r => dualAdjoint B₁ (X.R r)
  have hA₁bound : CoefficientBound (b.baseChange ℝ) T (Real.exp d) A₁.coord :=
    (coefficientBound_iff_norm _ T hTpos (Real.exp_nonneg _) _).mpr hAnorm₁
  have hdt : d ≤ t := le_add_of_nonneg_left hp
  have hExpdt : Real.exp d ≤ Real.exp t := Real.exp_le_exp.mpr hdt
  obtain ⟨a, c, n₁, hn₁, hn₁bound, hmidU, hmidK, hmidLower, hmidLift,
    hmidSystem, hmidRemainders, hmidExtra, hmidEquation, hmidBracket, hmidControls, hmidLiftControls⟩ :=
    F.exists_controlled_bracket_to_current_layer b w hF hs U (V.baseChange ℝ) hUV hV eK hK
      hj hH hn₀ hKernelBasis ht (hμ.trans hpt) (hκ.trans hpt)
      (hHp.trans (Real.exp_le_exp.mpr hpt)) (hn₀bound.trans hExpdt) T hTpos X.P A₁ B₁
      X.mem_U (fun α => hBrU (hAB₁ α).1) (fun α => hBrU (hAB₁ α).2)
      (fun α => hBrGrade _ (hAB₁ α).1) (fun α => hBrGrade _ (hAB₁ α).2)
      hAhom₁ hBhom₁ (fun h α => hBrK h (hAB₁ α).1) (fun h α => hBrK h (hAB₁ α).2)
      (fun h α => hBrV h (hAB₁ α).1) (fun h α => hBrV h (hAB₁ α).2)
      X.horizontal X.lower_log X.S X.R X.small X.rational X.k X.lift_system X.derivative_system
      X.small_remainder X.rational_remainder (fun r α => (hrems₁ r α).1)
      (fun r α => (hrems₁ r α).2.1) (fun r α => (hrems₁ r α).2.2)
      (hA₁bound.mono _ T hTpos hExpdt) hBgrid₁
      (fun r => (hliftControls₁ r).1.mono _ T hTpos hExpdt)
      (fun r => (hliftControls₁ r).2.1)
      (fun i => (hderivControls₁ i).1.mono _ T hTpos
        (div_le_div_of_nonneg_right hExpdt (hTpos i).le))
      (fun i => (hderivControls₁ i).2.1)
      (fun r => (hliftControls₁ r).2.2.1) (fun r => (hliftControls₁ r).2.2.2)
      (fun i => (hderivControls₁ i).2.2.1) (fun i => (hderivControls₁ i).2.2.2)
  let Smap₁ := (dualAdjointAddEquiv A₁⁻¹).toAddMonoidHom.comp
    (basisPolynomialLift (Pi.basisFun ℝ κ) X.S).toAddMonoidHom
  let Rmap₁ := (dualAdjointAddEquiv B₁).toAddMonoidHom.comp
    (basisPolynomialLift (Pi.basisFun ℝ κ) X.R).toAddMonoidHom
  let small₁ := fun i => dualAdjoint A₁⁻¹ (X.small i - formalLogDerivative i A₁) +
    if j = 2 then Smap₁ (a i) else 0
  let rational₁ := fun i => dualAdjoint B₁ (X.rational i) - formalLogDerivative i B₁ +
    if j = 2 then Rmap₁ (c i) else 0
  let k₁ := fun i => if j = 2 then X.k i - a i - c i else X.k i
  let extra₁ := fun i => Smap₁ (k₁ i)
  have hHpu : (H : ℝ) ≤ Real.exp u := hHp.trans (Real.exp_le_exp.mpr hpu)
  obtain ⟨nQ, hnQ, hnQbound, hprojectedBound, hprojectedGrid⟩ :=
    uniform_current_layer_inputs_from_ambient b w f j hn₁ hQuotient hu
      (hμ.trans hpu) (hι.trans hpu) hHpu hn₁bound T hTpos small₁ rational₁
      (fun i => (hmidControls i).1) (fun i => (hmidControls i).2.1)
  let nInput := n₁ * nQ
  have hnInput : 0 < nInput := Nat.mul_pos hn₁ hnQ
  have hn₁Input : n₁ ∣ nInput := dvd_mul_right n₁ nQ
  have hnQInput : nQ ∣ nInput := dvd_mul_left nQ n₁
  have hInputBound : (nInput : ℝ) ≤ Real.exp q := by
    calc
      _ = (n₁ : ℝ) * (nQ : ℝ) := Nat.cast_mul _ _
      _ ≤ Real.exp u * Real.exp v := mul_le_mul hn₁bound hnQbound (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp q := (Real.exp_add _ _).symm
  have hTE : ∀ i, Real.exp ((q + E) ^ E) ≤ T i :=
    fun i => (Real.exp_le_exp.mpr hzCap).trans (hT i)
  have hHq : (H : ℝ) ≤ Real.exp q := hHp.trans (Real.exp_le_exp.mpr hpq)
  have hEuq : Real.exp u ≤ Real.exp q := Real.exp_le_exp.mpr huq
  have hP₁cur : ∀ α, basisGradeProjection (b.baseChange ℝ) w j (coefficients P₁.coord α) ∈ Ecur.baseChange ℝ :=
    fun α => hCurProjection _ (hmidU α)
  obtain ⟨n₂, A₂, B₂, hn₂, hn₂bound, hAB₂, hAhom₂, hBhom₂, hAnorm₂, hBgrid₂,
    hprod₂, hconstant₂, hgraded₂, hU₂, hcurrent₂, hbelow₂, hsystem₂, hshift₂,
    hremainders₂, hK₂, hlower₂, hbracket₂, hextra₂, hlifts₂, hliftRemainders₂,
    hliftControls₂, hderivControls₂⟩ :=
    hcurrentStage F b w hF hgraded hs U (K.baseChange ℝ) hUV hV eCur f hj hCurGrade hCurU
      hH hnInput hCurrentMatrix hCurrentBasis hQuotient hStructure hq (Real.exp_nonneg v)
      (hμ.trans hpq) (hι.trans hpq) (hτ.trans hpq) (hσ.trans hpq) (hjp.trans hpq)
      hHq hHq hHq hInputBound (Real.exp_le_exp.mpr hvq) T hTE P₁
      hmidU hgraded₁ hP₁cur hmidK hmidLower hmidBracket small₁ rational₁ extra₁
      (fun i α => (hmidRemainders i α).1) (fun i α => (hmidRemainders i α).2)
      hmidExtra hmidSystem (fun i => (hmidControls i).2.2.1) (fun i => (hmidControls i).2.2.2)
      hprojectedBound (fun i α => realDenominatorGrid_subset_of_dvd hnQ hnQInput (hprojectedGrid i α))
      S₁ R₁ (fun r => (1 : ℝ) ⊗ₜ[ℚ] (eK r : L))
      (fun r => (hliftControls₁ r).2.2.1) (fun r => (hliftControls₁ r).2.2.2)
      hlifts₁ (fun r α => (hrems₁ r α).1) (fun r α => (hrems₁ r α).2.1)
      (fun r => (hmidLiftControls r).1.mono _ T hTpos hEuq)
      (fun r α => realDenominatorGrid_subset_of_dvd hn₁ hn₁Input ((hmidLiftControls r).2 α))
      (fun i => (hmidControls i).1.mono _ T hTpos (div_le_div_of_nonneg_right hEuq (hTpos i).le))
      (fun i α => realDenominatorGrid_subset_of_dvd hn₁ hn₁Input ((hmidControls i).2.1 α))
  let P₂ := A₂⁻¹ * P₁ * B₂⁻¹
  let S₂ := fun r => dualAdjoint A₂⁻¹ (S₁ r)
  let R₂ := fun r => dualAdjoint B₂ (R₁ r)
  let small₂ := fun i => dualAdjoint A₂⁻¹ (small₁ i - formalLogDerivative i A₂)
  let rational₂ := fun i => dualAdjoint B₂ (rational₁ i) - formalLogDerivative i B₂
  let n := n₀ * n₂
  have hn : 0 < n := Nat.mul_pos hn₀ hn₂
  have hn₀n : n₀ ∣ n := dvd_mul_right n₀ n₂
  have hn₂n : n₂ ∣ n := dvd_mul_left n₂ n₀
  have hnBound : (n : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    calc
      _ = (n₀ : ℝ) * (n₂ : ℝ) := Nat.cast_mul _ _
      _ ≤ Real.exp d * Real.exp z := mul_le_mul hn₀bound hn₂bound (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (d + z) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hsumCap
  have hEz : Real.exp z ≤ Real.exp ((p + C) ^ C) := Real.exp_le_exp.mpr hzCap
  have hS₁eval (x : κ → ℝ) : basisPolynomialLift (Pi.basisFun ℝ κ) S₁ x = Smap₁ x := by
    rw [basisPolynomialLift_adjoint (hnil := F.realification.lowerCentralSeries_eq_bot)
      (Pi.basisFun ℝ κ) A₁⁻¹ X.S]
    rfl
  have hextraEq : (fun i => dualAdjoint A₂⁻¹ (extra₁ i)) =
      fun i => basisPolynomialLift (Pi.basisFun ℝ κ) S₂ (k₁ i) := by
    funext i
    rw [basisPolynomialLift_adjoint (hnil := F.realification.lowerCentralSeries_eq_bot)
      (Pi.basisFun ℝ κ) A₂⁻¹ S₁]
    change dualAdjoint A₂⁻¹ (Smap₁ (k₁ i)) =
      dualAdjoint A₂⁻¹ (basisPolynomialLift (Pi.basisFun ℝ κ) S₁ (k₁ i))
    rw [hS₁eval]
  have hsystemFinal : PolynomialDerivativeSystemMod ((V.baseChange ℝ).restrictScalars ℚ)
      P₂ small₂ rational₂ (fun i => basisPolynomialLift (Pi.basisFun ℝ κ) S₂ (k₁ i)) := by
    rw [← hextraEq]
    exact hsystem₂
  have hbracketsFinal : ∀ r < (j + 1) - 1, ∀ i α,
      ⁅basisGradeProjection (b.baseChange ℝ) w r (coefficients P₂.coord α),
        (1 : ℝ) ⊗ₜ[ℚ] (eK i : L)⁆ ∈ V.baseChange ℝ := by
    intro r hr i α
    have hrj : r < j := by omega
    have heq := congrArg (fun Q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) => coefficients Q α) (hbelow₂ r hrj)
    simp only [coefficients_map, LinearMap.restrictScalars_apply] at heq
    rw [heq]
    exact hbrackets₁ r hrj i α
  let Y : F.FormalInductionState b w U V K eK T (j + 1) ((p + C) ^ C) := {
    P := P₂
    S := S₂
    R := R₂
    small := small₂
    rational := rational₂
    k := k₁
    denominator := n
    denominator_pos := hn
    denominator_bound := hnBound
    constant_zero := hconstant₂.trans (hconstant₁.trans X.constant_zero)
    mem_U := hU₂
    graded := hgraded₂
    horizontal := hK₂
    lower_log := hlower₂
    lower_bracket := hbracketsFinal
    lift_system := hlifts₂
    derivative_system := hsystemFinal
    S_shift := fun r => (hliftControls₂ r).2.2.1
    R_shift := fun r => (hliftControls₂ r).2.2.2
    small_shift := fun i => (hshift₂ i).1
    rational_shift := fun i => (hshift₂ i).2
    S_remainder := fun r α => (hliftRemainders₂ r α).1
    R_remainder := fun r α => (hliftRemainders₂ r α).2
    small_remainder := fun i α => (hremainders₂ i α).1
    rational_remainder := fun i α => (hremainders₂ i α).2
    S_bound := fun r => (hliftControls₂ r).1.mono _ T hTpos hEz
    R_grid := fun r α => realDenominatorGrid_subset_of_dvd hn₂ hn₂n ((hliftControls₂ r).2.1 α)
    small_bound := fun i => (hderivControls₂ i).1.mono _ T hTpos
      (div_le_div_of_nonneg_right hEz (hTpos i).le)
    rational_grid := fun i α => realDenominatorGrid_subset_of_dvd hn₂ hn₂n ((hderivControls₂ i).2 α) }
  refine ⟨Y, A₁, A₂, B₁, B₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (A₁ * A₂) * P₂ * (B₂ * B₁) = X.P
    calc
      _ = A₁ * (A₂ * P₂ * B₂) * B₁ := by group
      _ = A₁ * P₁ * B₁ := by rw [hprod₂]
      _ = X.P := hprod₁
  · intro α
    exact ⟨hBrU (hAB₁ α).1, hCurU (hAB₂ α).1, hBrU (hAB₁ α).2, hCurU (hAB₂ α).2⟩
  · exact ⟨homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)
        (j - 1) A₁.coord hAhom₁ (fun α => hBrGrade _ (hAB₁ α).1),
      homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)
        j A₂.coord hAhom₂ (fun α => hCurGrade _ (hAB₂ α).1),
      homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)
        (j - 1) B₁.coord hBhom₁ (fun α => hBrGrade _ (hAB₁ α).2),
      homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)
        j B₂.coord hBhom₂ (fun α => hCurGrade _ (hAB₂ α).2)⟩
  · have hzero₁ : Finsupp.weight (fun _ : σ => (1 : ℕ)) (0 : σ →₀ ℕ) ≠ j - 1 := by simp only [map_zero]; omega
    have hzero₂ : Finsupp.weight (fun _ : σ => (1 : ℕ)) (0 : σ →₀ ℕ) ≠ j := by simp only [map_zero]; omega
    exact ⟨hAhom₁ 0 hzero₁, hAhom₂ 0 hzero₂, hBhom₁ 0 hzero₁, hBhom₂ 0 hzero₂⟩
  · exact hA₁bound.mono _ T hTpos (Real.exp_le_exp.mpr hdCap)
  · have hA₂bound : CoefficientBound (b.baseChange ℝ) T (Real.exp z) A₂.coord :=
      (coefficientBound_iff_norm _ T hTpos (Real.exp_nonneg _) _).mpr hAnorm₂
    exact hA₂bound.mono _ T hTpos hEz
  · exact fun α => realDenominatorGrid_subset_of_dvd hn₀ hn₀n (hBgrid₁ α)
  · exact fun α => realDenominatorGrid_subset_of_dvd hn₂ hn₂n (hBgrid₂ α)

end Erdos3.NilpotentLieFiltration

end

end OAI
