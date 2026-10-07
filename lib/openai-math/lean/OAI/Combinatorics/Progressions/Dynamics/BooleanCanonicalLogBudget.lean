import OAI.Combinatorics.Progressions.Dynamics.ModeThresholdLogBudget
import OAI.Combinatorics.Progressions.Estimates.CanonicalCubeMinorThreshold
import OAI.Combinatorics.Progressions.Polynomial.PolynomialThresholdBudget

namespace OAI

section

namespace Erdos3

def productMinorEntryLog (q h : ℕ) (P : ℝ) : ℝ := P+h+(h : ℝ)*q
def productMinorPartialLog (q h : ℕ) (P : ℝ) : ℝ := P+2*h+(h : ℝ)*q
def productMinorInverseLog (j q h : ℕ) (P E : ℝ) : ℝ :=
  j+(j : ℝ)^2+(j-1 : ℕ)*productMinorEntryLog q h P+E
def productMinorDerivativeLog (n j q h : ℕ) (P : ℝ) : ℝ :=
  n+j+productMinorPartialLog q h P
def productMinorDeterminantLog (n j q h : ℕ) (P : ℝ) : ℝ :=
  n+(j : ℝ)^2+j+productMinorPartialLog q h P+j*(productMinorEntryLog q h P+1)

theorem productMinorEntryBound_le_exp (q h : ℕ) {C P : ℝ}
    (hC : 0 ≤ C) (hCP : C ≤ Real.exp P) :
    productMinorEntryBound q h C 1 ≤ Real.exp (productMinorEntryLog q h P) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hq : (q : ℝ)+1 ≤ Real.exp q := Real.add_one_le_exp _
  have hp : ((q : ℝ)+1)^(h-1) ≤ ((q : ℝ)+1)^h :=
    pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) q]) (Nat.sub_le _ _)
  unfold productMinorEntryBound
  rw [mul_one]
  calc
    _ ≤ C*((2 : ℝ)^h*((q : ℝ)+1)^h) := by gcongr
    _ ≤ Real.exp P*((Real.exp 1)^h*(Real.exp q)^h) := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      simp only [productMinorEntryLog, mul_one]
      ring

theorem productMinorPartialBound_le_exp (q h : ℕ) {C P : ℝ}
    (_hC : 0 ≤ C) (hCP : C ≤ Real.exp P) :
    productMinorPartialBound q h C 1 ≤ Real.exp (productMinorPartialLog q h P) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hq : (q : ℝ)+1 ≤ Real.exp q := Real.add_one_le_exp _
  have hh : (h : ℝ) ≤ Real.exp h := by linarith [Real.add_one_le_exp (h : ℝ)]
  unfold productMinorPartialBound
  rw [mul_one]
  calc
    _ ≤ Real.exp P*((Real.exp 1)^h*(Real.exp h*(Real.exp q)^h)) := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      simp only [productMinorPartialLog, mul_one]
      ring

theorem productMinorInverseBound_le_exp (j q h : ℕ) {C κ P E : ℝ}
    (hC : 0 ≤ C) (hκ : 0 < κ) (hCP : C ≤ Real.exp P) (hκE : κ⁻¹ ≤ Real.exp E) :
    productMinorInverseBound j q h C 1 κ ≤ Real.exp (productMinorInverseLog j q h P E) := by
  have hj : (j : ℝ) ≤ Real.exp j := by linarith [Real.add_one_le_exp (j : ℝ)]
  have hf := factorial_le_exp_sq j
  have he := productMinorEntryBound_le_exp q h hC hCP
  have he0 := productMinorEntryBound_nonneg q h hC zero_le_one
  unfold productMinorInverseBound
  rw [div_eq_mul_inv]
  calc
    _ ≤ Real.exp j*(Real.exp ((j : ℝ)^2)*(Real.exp (productMinorEntryLog q h P))^(j-1)*Real.exp E) := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      unfold productMinorInverseLog
      ring

theorem productMinorDerivativeBound_le_exp (n j q h : ℕ) {C P : ℝ}
    (hC : 0 ≤ C) (hCP : C ≤ Real.exp P) :
    productMinorDerivativeBound n j q h C 1 ≤ Real.exp (productMinorDerivativeLog n j q h P) := by
  have hn : (n : ℝ) ≤ Real.exp n := by linarith [Real.add_one_le_exp (n : ℝ)]
  have hj : (j : ℝ) ≤ Real.exp j := by linarith [Real.add_one_le_exp (j : ℝ)]
  have hb := productMinorPartialBound_le_exp q h hC hCP
  have hb0 := productMinorPartialBound_nonneg q h hC zero_le_one
  calc
    _ ≤ Real.exp n*(Real.exp j*Real.exp (productMinorPartialLog q h P)) := by
      unfold productMinorDerivativeBound
      gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; unfold productMinorDerivativeLog; ring

theorem productMinorDeterminantDerivativeBound_le_exp (n j q h : ℕ) {C P : ℝ}
    (hC : 0 ≤ C) (hP : 0 ≤ P) (hCP : C ≤ Real.exp P) :
    productMinorDeterminantDerivativeBound n j q h C 1 ≤ Real.exp (productMinorDeterminantLog n j q h P) := by
  have hn : (n : ℝ) ≤ Real.exp n := by linarith [Real.add_one_le_exp (n : ℝ)]
  have hj : (j : ℝ) ≤ Real.exp j := by linarith [Real.add_one_le_exp (j : ℝ)]
  have hf := factorial_le_exp_sq j
  have hb := productMinorPartialBound_le_exp q h hC hCP
  have hb0 := productMinorPartialBound_nonneg q h hC zero_le_one
  have he := one_add_le_exp_succ (show 0 ≤ productMinorEntryLog q h P by unfold productMinorEntryLog; positivity)
    (productMinorEntryBound_le_exp q h hC hCP)
  have he0 := productMinorEntryBound_nonneg q h hC zero_le_one
  calc
    _ ≤ Real.exp n*(Real.exp ((j : ℝ)^2)*(Real.exp j*Real.exp (productMinorPartialLog q h P)*
        (Real.exp (productMinorEntryLog q h P+1))^j)) := by
      unfold productMinorDeterminantDerivativeBound
      gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      unfold productMinorDeterminantLog
      ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

variable {D α : Type*} [Fintype D] [Fintype α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]

noncomputable def jointBooleanInverseBudget (h : D → ℕ) (C κ : D → ℝ) : ℝ≥0 :=
  ∑ d, Real.toNNReal (productMinorInverseBound (Fintype.card (O d)) (Fintype.card α)
    (h d) (C d) 1 (κ d))

noncomputable def jointBooleanDerivativeBudget (h : D → ℕ) (C : D → ℝ) : ℝ≥0 :=
  ∑ d, Real.toNNReal (productMinorDerivativeBound (Fintype.card (BlockParameter (B d) (Fin (h d)) α))
    (Fintype.card (O d)) (Fintype.card α) (h d) (C d) 1)

omit [∀ d, Fintype (B d)] in
theorem jointBooleanInverseBudget_le (h : D → ℕ) (C κ : D → ℝ) (d : D) :
    productMinorInverseBound (Fintype.card (O d)) (Fintype.card α) (h d) (C d) 1 (κ d) ≤
      jointBooleanInverseBudget (O := O) (α := α) h C κ := by
  classical
  apply (Real.le_coe_toNNReal _).trans
  exact_mod_cast (Finset.single_le_sum (f := fun e => Real.toNNReal
    (productMinorInverseBound (Fintype.card (O e)) (Fintype.card α) (h e) (C e) 1 (κ e)))
      (fun _ _ => zero_le) (Finset.mem_univ d))

theorem jointBooleanDerivativeBudget_le (h : D → ℕ) (C : D → ℝ) (d : D) :
    productMinorDerivativeBound (Fintype.card (BlockParameter (B d) (Fin (h d)) α))
      (Fintype.card (O d)) (Fintype.card α) (h d) (C d) 1 ≤
        jointBooleanDerivativeBudget (B := B) (O := O) (α := α) h C := by
  classical
  apply (Real.le_coe_toNNReal _).trans
  exact_mod_cast (Finset.single_le_sum (f := fun e => Real.toNNReal
    (productMinorDerivativeBound (Fintype.card (BlockParameter (B e) (Fin (h e)) α))
      (Fintype.card (O e)) (Fintype.card α) (h e) (C e) 1))
        (fun _ _ => zero_le) (Finset.mem_univ d))

end Erdos3

end

section

namespace Erdos3

def cubeMinorConstantLog (j q h N d : ℕ) : ℝ :=
  (j : ℝ)*h*((q : ℝ)+1)^2+3*N+(d+1 : ℝ)+d*(8+(d+1 : ℝ))

def cubeMinorScaleLog (j N d : ℕ) (P : ℝ) : ℝ := (N : ℝ)*d+j*P

def cubeMinorThresholdLog (m j q h N d : ℕ) (P E : ℝ) : ℝ :=
  cubeMinorScaleLog j N d P+2+(N*d : ℕ)*(cubeMinorConstantLog j q h N d+m+E+2)

theorem cubeMinorProbabilityConstant_le_exp (O α : Type*) [Fintype O] [Fintype α] [DecidableEq α]
    (h N d : ℕ) (hN : 0 < N) (hd : 0 < d) :
    cubeMinorProbabilityConstant O α h N d ≤
      Real.exp (cubeMinorConstantLog (Fintype.card O) (Fintype.card α) h N d) := by
  have hden := scalarCubeDomainDensity_le_exp α
  have hden0 := (scalarCubeDomainDensity_pos α).le
  have hc := multivariateSublevelConstant_le_exp N d hd
  have hc0 := (multivariateSublevelConstant_pos hN d).le
  unfold cubeMinorProbabilityConstant
  calc
    _ ≤ (Real.exp (((Fintype.card α : ℝ)+1)^2))^Fintype.card (O × Fin h)*
        Real.exp (3*(N : ℝ)+(d+1 : ℝ)+d*(8+(d+1 : ℝ))) := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, cubeMinorConstantLog]
      ring

theorem cubeMinorProbabilityScale_le_exp (O : Type*) [Fintype O] (N d : ℕ)
    {c₀ P : ℝ} (hc₀ : 0 < c₀) (hcP : c₀⁻¹ ≤ Real.exp P) :
    cubeMinorProbabilityScale O N d c₀ ≤ Real.exp (cubeMinorScaleLog (Fintype.card O) N d P) := by
  have hd : (d : ℝ)+1 ≤ Real.exp d := Real.add_one_le_exp _
  unfold cubeMinorProbabilityScale
  rw [div_eq_mul_inv, ← inv_pow]
  calc
    _ ≤ (Real.exp d)^N*(Real.exp P)^Fintype.card O := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]; rfl

theorem cubeMinorThreshold_inverse_le_exp (J O α : Type*)
    [Fintype J] [Fintype O] [Fintype α] [DecidableEq α]
    (h N d : ℕ) (hN : 0 < N) (hd : 0 < d) {c₀ η P E : ℝ}
    (hc₀ : 0 < c₀) (hη : 0 < η) (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hcP : c₀⁻¹ ≤ Real.exp P) (hηE : η⁻¹ ≤ Real.exp E) :
    (cubeMinorThreshold J O α h N d c₀ η)⁻¹ ≤
      Real.exp (cubeMinorThresholdLog (Fintype.card J) (Fintype.card O) (Fintype.card α) h N d P E) := by
  exact polynomialSublevelThreshold_inverse_le_exp (N*d) (Fintype.card J)
    (cubeMinorProbabilityConstant_pos O α h hN d).le (cubeMinorProbabilityScale_pos O N d hc₀).le hη
    (by unfold cubeMinorConstantLog; positivity) (by unfold cubeMinorScaleLog; positivity) hE
    (cubeMinorProbabilityConstant_le_exp O α h N d hN hd)
    (cubeMinorProbabilityScale_le_exp O N d hc₀ hcP) hηE

theorem canonicalCubeMinorThreshold_inverse_le_exp (J O α : Type*)
    [Fintype J] [Fintype O] [Nonempty O] [Fintype α] [DecidableEq α]
    (h : ℕ) (hh : 0 < h) {c₀ η P E : ℝ}
    (hc₀ : 0 < c₀) (hη : 0 < η) (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hcP : c₀⁻¹ ≤ Real.exp P) (hηE : η⁻¹ ≤ Real.exp E) :
    (canonicalCubeMinorThreshold J O α h c₀ η)⁻¹ ≤
      Real.exp (cubeMinorThresholdLog (Fintype.card J) (Fintype.card O) (Fintype.card α) h
        (cubeMinorVariableCount O α h) (cubeMinorDegree O h) P E) :=
  cubeMinorThreshold_inverse_le_exp J O α h (cubeMinorVariableCount O α h) (cubeMinorDegree O h)
    (boolean_minor_parameter_count_pos O α hh)
    (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)) hc₀ hη hP hE hcP hηE

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

def canonicalBooleanMinorLog (O α : Type*) [Fintype O] [Fintype α]
    (h : ℕ) (P E : ℝ) : ℝ :=
  cubeMinorThresholdLog 1 (Fintype.card O) (Fintype.card α) h
    (cubeMinorVariableCount O α h) (cubeMinorDegree O h) P E

noncomputable def jointBooleanInverseLog {D α : Type*} [Fintype D] [Fintype α]
    {O : D → Type*} [∀ d, Fintype (O d)] (h : D → ℕ) (P E : ℝ) : ℝ :=
  Fintype.card D+∑ d, productMinorInverseLog (Fintype.card (O d)) (Fintype.card α) (h d) P
    (canonicalBooleanMinorLog (O d) α (h d) P E)

noncomputable def jointBooleanDerivativeLog {D α : Type*} [Fintype D] [Fintype α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)] (h : D → ℕ) (P : ℝ) : ℝ :=
  Fintype.card D+∑ d, productMinorDerivativeLog (Fintype.card (BlockParameter (B d) (Fin (h d)) α))
    (Fintype.card (O d)) (Fintype.card α) (h d) P

def booleanAxisWeightLog (B O α : Type*) [Fintype B] [Fintype O] [Fintype α]
    (h : ℕ) (P E : ℝ) : ℝ :=
  (scalarCubeDerivativeLog (Fintype.card α) P+2*Fintype.card (B × Fin h)+E+1)+
  (Fintype.card (BlockParameter B (Fin h) α)+P+canonicalBooleanMinorLog O α h P E+
    productMinorDeterminantLog (Fintype.card (BlockParameter B (Fin h) α))
      (Fintype.card O) (Fintype.card α) h P)+1

noncomputable def jointBooleanWeightLog {D α : Type*} [Fintype D] [Fintype α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)] (h : D → ℕ) (P E : ℝ) : ℝ :=
  Fintype.card D+∑ d, booleanAxisWeightLog (B d) (O d) α (h d) P E

theorem canonicalBooleanMinorLog_nonneg (O α : Type*) [Fintype O] [Fintype α]
    (h : ℕ) {P E : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) :
    0 ≤ canonicalBooleanMinorLog O α h P E := by
  unfold canonicalBooleanMinorLog cubeMinorThresholdLog cubeMinorScaleLog cubeMinorConstantLog
  positivity

theorem jointBooleanInverseLog_nonneg {D α : Type*} [Fintype D] [Fintype α]
    {O : D → Type*} [∀ d, Fintype (O d)] (h : D → ℕ) {P E : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) :
    0 ≤ jointBooleanInverseLog (O := O) (α := α) h P E := by
  apply add_nonneg (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro d _
  have hk := canonicalBooleanMinorLog_nonneg (O d) α (h d) hP hE
  unfold productMinorInverseLog productMinorEntryLog
  positivity

theorem jointBooleanDerivativeLog_nonneg {D α : Type*} [Fintype D] [Fintype α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    (h : D → ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ jointBooleanDerivativeLog (B := B) (O := O) (α := α) h P := by
  apply add_nonneg (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro d _
  unfold productMinorDerivativeLog productMinorPartialLog
  positivity

theorem jointBooleanInverseBudget_canonical_le_exp {D α : Type*}
    [Fintype D] [Fintype α] [DecidableEq α]
    {O : D → Type*} [∀ d, Fintype (O d)] [∀ d, Nonempty (O d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (c₀ C η : D → ℝ)
    (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d) (hη : ∀ d, 0 < η d)
    {P E : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hcP : ∀ d, (c₀ d)⁻¹ ≤ Real.exp P) (hCP : ∀ d, C d ≤ Real.exp P)
    (hηE : ∀ d, (η d)⁻¹ ≤ Real.exp E) :
    (jointBooleanInverseBudget (O := O) (α := α) h C
      (fun d => canonicalCubeMinorThreshold Unit (O d) α (h d) (c₀ d) (η d)) : ℝ) ≤
      Real.exp (jointBooleanInverseLog (O := O) (α := α) h P E) := by
  unfold jointBooleanInverseBudget jointBooleanInverseLog
  rw [NNReal.coe_sum]
  apply sum_le_exp_card_add_sum
  · intro d
    have hk := canonicalBooleanMinorLog_nonneg (O d) α (h d) hP hE
    unfold productMinorInverseLog productMinorEntryLog
    positivity
  · intro d
    apply coe_toNNReal_le_exp
    exact productMinorInverseBound_le_exp _ _ _ (hC d)
      (canonicalCubeMinorThreshold_pos Unit (O d) α (hh d) (hc₀ d) (hη d)) (hCP d)
      (canonicalCubeMinorThreshold_inverse_le_exp Unit (O d) α (h d) (hh d)
        (hc₀ d) (hη d) hP hE (hcP d) (hηE d))

theorem jointBooleanDerivativeBudget_le_exp {D α : Type*} [Fintype D] [Fintype α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    (h : D → ℕ) (C : D → ℝ) (hC : ∀ d, 0 ≤ C d) {P : ℝ} (hP : 0 ≤ P)
    (hCP : ∀ d, C d ≤ Real.exp P) :
    (jointBooleanDerivativeBudget (B := B) (O := O) (α := α) h C : ℝ) ≤
      Real.exp (jointBooleanDerivativeLog (B := B) (O := O) (α := α) h P) := by
  unfold jointBooleanDerivativeBudget jointBooleanDerivativeLog
  rw [NNReal.coe_sum]
  apply sum_le_exp_card_add_sum
  · intro d
    unfold productMinorDerivativeLog productMinorPartialLog
    positivity
  · intro d
    exact coe_toNNReal_le_exp (productMinorDerivativeBound_le_exp _ _ _ _ (hC d) (hCP d))

end Erdos3

end

end OAI
