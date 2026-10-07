import OAI.Combinatorics.Progressions.Dynamics.JointPivotProfileBudget
import OAI.Combinatorics.Progressions.Probability.SmoothSpatialProbability

namespace OAI

section

namespace Erdos3

theorem selectedColumn_card {I J : Type*} [Fintype I] [Fintype J] (s : I ↪ J) :
    Fintype.card I + Fintype.card (UnselectedColumn s) = Fintype.card J := by
  simpa only [Fintype.card_sum] using Fintype.card_congr (selectedColumnEquiv s)

theorem selectedSpatial_dimension {I J N : Type*} [Fintype I] [Fintype J] [Fintype N] (s : I ↪ J) :
    Fintype.card (Unit ⊕ I) + Fintype.card (UnselectedColumn s ⊕ N) =
      1 + Fintype.card J + Fintype.card N := by
  have h := selectedColumn_card s
  simp only [Fintype.card_sum, Fintype.card_unit]
  omega

theorem scalarSpatialIndexAllowance_le_exp (I : Type*) [Fintype I] {B : ℕ} {R : ℝ}
    (hB : (B : ℝ) ≤ Real.exp R) :
    scalarSpatialIndexAllowance I B ≤ Real.exp ((Fintype.card I + 1 : ℝ) * R) := by
  unfold scalarSpatialIndexAllowance
  calc
    _ ≤ (Real.exp R)^(Fintype.card I + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hB _
    _ = _ := by rw [← Real.exp_nat_mul]; push_cast; rfl

theorem scalarSpatialInverseAllowance_le_exp (I : Type*) [Fintype I] {B : ℕ} {R : ℝ}
    (hB : (B : ℝ) ≤ Real.exp R) :
    scalarSpatialInverseAllowance I B ≤
      Real.exp ((Fintype.card I + 1 : ℝ) + (Fintype.card I + 1 : ℝ)^2 + R) := by
  have hn : (Fintype.card I + 1 : ℝ) ≤ Real.exp (Fintype.card I + 1 : ℝ) := by
    linarith [Real.add_one_le_exp (Fintype.card I + 1 : ℝ)]
  have hf : ((Fintype.card I + 1).factorial : ℝ) ≤ Real.exp ((Fintype.card I + 1 : ℝ)^2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using factorial_le_exp_sq (Fintype.card I + 1)
  unfold scalarSpatialInverseAllowance
  calc
    _ ≤ Real.exp (Fintype.card I + 1 : ℝ) * Real.exp ((Fintype.card I + 1 : ℝ)^2) * Real.exp R := by gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]

end Erdos3

end

section

namespace Erdos3

noncomputable def smoothSpatialMeshThreshold (I J N : Type*)
    [Fintype I] [Fintype J] [Fintype N] (L : ℕ) : ℝ :=
  2 * 4 ^ (1 + Fintype.card J + Fintype.card N) *
    (1 + Fintype.card J + Fintype.card N : ℝ) * probabilityProfileLipschitz *
      (((Fintype.card I).factorial : ℝ) * (L : ℝ)^Fintype.card I)

theorem smoothSpatial_profile_dimensions {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N] (s : I ↪ J) :
    Fintype.card (UnselectedColumn s) + Fintype.card (Unit ⊕ I) = 1 + Fintype.card J ∧
    Fintype.card (UnselectedColumn s ⊕ N) + Fintype.card (Unit ⊕ I) =
      1 + Fintype.card J + Fintype.card N := by
  have h := selectedColumn_card s
  simp only [Fintype.card_sum, Fintype.card_unit]
  omega

theorem smoothSpatial_mesh_conditions {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N] (s : I ↪ J) {L : ℕ} {ρ : ℝ}
    (hρ : 0 < ρ) (hlarge : smoothSpatialMeshThreshold I J N L ≤ ρ) :
    ((Fintype.card I).factorial : ℝ) * (L : ℝ)^Fintype.card I ≤ ρ ∧
    4 ^ (Fintype.card (Unit ⊕ I) + Fintype.card (UnselectedColumn s ⊕ N)) *
      (((Fintype.card (UnselectedColumn s ⊕ N) + Fintype.card (Unit ⊕ I)) : ℝ) *
        probabilityProfileLipschitz) *
      ((((Fintype.card I).factorial : ℝ) * (L : ℝ)^Fintype.card I) / ρ) ≤ 1 / 2 := by
  let d := 1 + Fintype.card J + Fintype.card N
  let D : ℝ := ((Fintype.card I).factorial : ℝ) * (L : ℝ)^Fintype.card I
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by dsimp [d]; omega)
  have hA : (1 : ℝ) ≤ probabilityProfileLipschitz := probabilityProfileLipschitz_one_le
  have hpow : (1 : ℝ) ≤ 4 ^ d := one_le_pow₀ (by norm_num)
  have hfactor : 1 ≤ 2 * (4 : ℝ) ^ d * d * probabilityProfileLipschitz := by
    have hprod : (1 : ℝ) ≤ 4 ^ d * d * probabilityProfileLipschitz := by
      calc
        1 = 1 * 1 * 1 := by norm_num
        _ ≤ 4 ^ d * d * probabilityProfileLipschitz :=
          mul_le_mul (mul_le_mul hpow hd zero_le_one (by positivity)) hA
            (by norm_num) (by positivity)
    nlinarith
  have hl : 2 * (4 : ℝ)^d * d * probabilityProfileLipschitz * D ≤ ρ := by
    simpa only [smoothSpatialMeshThreshold, d, D, Nat.cast_add, Nat.cast_one] using hlarge
  refine ⟨(le_mul_of_one_le_left hD hfactor).trans hl, ?_⟩
  have hc : (Fintype.card (UnselectedColumn s ⊕ N) : ℝ) + Fintype.card (Unit ⊕ I) = d := by
    exact_mod_cast (smoothSpatial_profile_dimensions (N := N) s).2
  rw [selectedSpatial_dimension s, hc]
  change (4 : ℝ)^d * ((d : ℝ) * probabilityProfileLipschitz) * (D / ρ) ≤ 1 / 2
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  have he : (4 : ℝ)^d * ((d : ℝ) * probabilityProfileLipschitz) * (D / ρ) * 2 =
      (2 * 4^d * d * probabilityProfileLipschitz * D) / ρ := by ring
  rw [he]
  exact (div_le_one hρ).mpr hl

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

noncomputable def smoothSpatialDiscretizationCost {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) (M L : ℕ) : ℝ :=
  (normalizedFiberErrorConstant (Fintype.card (Unit ⊕ I)) (Fintype.card (UnselectedColumn s ⊕ N))
    (scalarSpatialIndexAllowance I M) (scalarSpatialInverseAllowance I M)
    (Fintype.card (UnselectedColumn s ⊕ N)) 1 1
    ((Fintype.card (UnselectedColumn s ⊕ N)+Fintype.card (Unit ⊕ I))*probabilityProfileLipschitz) *
      (Fintype.card (Unit ⊕ I)).factorial) * (L : ℝ)^Fintype.card (Unit ⊕ I)

noncomputable def smoothSpatialDisplacementCost {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) (M : ℕ) : ℝ :=
  scalarSpatialIndexAllowance I M *
    spatialKernelErrorConstant (Fintype.card (Unit ⊕ I)) (Fintype.card (UnselectedColumn s))
      (scalarSpatialInverseAllowance I M) 1
      ((Fintype.card (UnselectedColumn s)+Fintype.card (Unit ⊕ I))*probabilityProfileLipschitz) *
    Fintype.card N

theorem smoothSpatialError_decomposition {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) (M L : ℕ) (ρ ξ : ℝ) :
    smoothSpatialError N s M L ρ ξ =
      smoothSpatialDiscretizationCost N s M L/ρ+smoothSpatialDisplacementCost N s M*ξ := by
  unfold smoothSpatialError smoothSpatialDiscretizationCost smoothSpatialDisplacementCost
  ring

theorem smoothSpatialDiscretizationCost_nonneg {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) (M L : ℕ) :
    0 ≤ smoothSpatialDiscretizationCost N s M L := by
  unfold smoothSpatialDiscretizationCost normalizedFiberErrorConstant integerFiberErrorConstant
    scalarSpatialIndexAllowance scalarSpatialInverseAllowance
  positivity

theorem smoothSpatialDisplacementCost_nonneg {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) (M : ℕ) :
    0 ≤ smoothSpatialDisplacementCost N s M := by
  unfold smoothSpatialDisplacementCost spatialKernelErrorConstant
    scalarSpatialIndexAllowance scalarSpatialInverseAllowance
  positivity

theorem smoothSpatial_error_choices {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) (M L : ℕ) {ε : ℝ} (hε : 0 < ε) :
    let ρ := twoTermErrorResolution (smoothSpatialMeshThreshold I J N L)
      (smoothSpatialDiscretizationCost N s M L) ε
    let ξ := twoTermErrorWidth (smoothSpatialDisplacementCost N s M) ε
    0 < ρ ∧ smoothSpatialMeshThreshold I J N L ≤ ρ ∧
    0 < ξ ∧ ξ ≤ 1 ∧ smoothSpatialError N s M L ρ ξ ≤ ε := by
  dsimp only
  rw [smoothSpatialError_decomposition]
  exact twoTermErrorChoices_spec (by unfold smoothSpatialMeshThreshold; positivity)
    (smoothSpatialDiscretizationCost_nonneg N s M L) (smoothSpatialDisplacementCost_nonneg N s M) hε

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

noncomputable def spatialProfileLog (j d : ℕ) (p : ℝ) : ℝ :=
  (j+1)*p+(j : ℝ)^2+2*j+d+probabilityProfileLipschitz+1

theorem spatialProfileLog_nonneg (j d : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ spatialProfileLog j d p := by unfold spatialProfileLog; positivity

theorem spatialProfileLog_bounds {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) {M : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hM : (M : ℝ) ≤ Real.exp p) :
    let j := Fintype.card (Unit ⊕ I)
    let d := Fintype.card (UnselectedColumn s ⊕ N)
    let P := spatialProfileLog j d p
    scalarSpatialIndexAllowance I M ≤ Real.exp P ∧
    scalarSpatialInverseAllowance I M ≤ Real.exp P ∧
    (d : ℝ) ≤ Real.exp P ∧
    ((d+j : ℝ)*probabilityProfileLipschitz) ≤ Real.exp P := by
  dsimp only
  let j := Fintype.card (Unit ⊕ I)
  let d := Fintype.card (UnselectedColumn s ⊕ N)
  have hj : (Fintype.card I+1 : ℝ) = j := by
    simp only [j, Fintype.card_sum, Fintype.card_unit, Nat.cast_add, Nat.cast_one]
    ring
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hκ : (0 : ℝ) ≤ probabilityProfileLipschitz := NNReal.coe_nonneg _
  have hG := scalarSpatialIndexAllowance_le_exp I hM
  have hU := scalarSpatialInverseAllowance_le_exp I hM
  rw [hj] at hG hU
  have hn : (d+j : ℝ) ≤ Real.exp (d+j : ℝ) := by
    linarith [Real.add_one_le_exp (d+j : ℝ)]
  have hk : (probabilityProfileLipschitz : ℝ) ≤ Real.exp probabilityProfileLipschitz := by
    linarith [Real.add_one_le_exp (probabilityProfileLipschitz : ℝ)]
  refine ⟨hG.trans (Real.exp_le_exp.mpr ?_), hU.trans (Real.exp_le_exp.mpr ?_), ?_, ?_⟩
  · change (j : ℝ)*p ≤ spatialProfileLog j d p
    unfold spatialProfileLog
    nlinarith
  · change (j : ℝ)+j^2+p ≤ spatialProfileLog j d p
    unfold spatialProfileLog
    nlinarith
  · calc
      (d : ℝ) ≤ Real.exp d := by linarith [Real.add_one_le_exp (d : ℝ)]
      _ ≤ Real.exp (spatialProfileLog j d p) := by
        apply Real.exp_le_exp.mpr
        unfold spatialProfileLog
        nlinarith
  · calc
      (d+j : ℝ)*probabilityProfileLipschitz ≤
          Real.exp (d+j : ℝ)*Real.exp probabilityProfileLipschitz :=
        mul_le_mul hn hk hκ (Real.exp_pos _).le
      _ = Real.exp ((d+j : ℝ)+probabilityProfileLipschitz) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (spatialProfileLog j d p) := by
        apply Real.exp_le_exp.mpr
        unfold spatialProfileLog
        nlinarith

noncomputable def spatialDiscretizationLog (j d : ℕ) (p l : ℝ) : ℝ :=
  let P := spatialProfileLog j d p
  2*(j : ℝ)^2+(2*j+4)*P+(j+2*d)*(P+4)+4+j*l

theorem smoothSpatialDiscretizationCost_le_exp {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) {M L : ℕ} {p l : ℝ}
    (hp : 0 ≤ p) (hM : (M : ℝ) ≤ Real.exp p) (hL : (L : ℝ) ≤ Real.exp l) :
    smoothSpatialDiscretizationCost N s M L ≤
      Real.exp (spatialDiscretizationLog (Fintype.card (Unit ⊕ I))
        (Fintype.card (UnselectedColumn s ⊕ N)) p l) := by
  let j := Fintype.card (Unit ⊕ I)
  let d := Fintype.card (UnselectedColumn s ⊕ N)
  let P := spatialProfileLog j d p
  obtain ⟨hG, hU, hV, hK⟩ := spatialProfileLog_bounds N s hp hM
  have hP : 0 ≤ P := spatialProfileLog_nonneg j d hp
  have hone : (1 : ℝ) ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have hc := coefficientComparisonConstant_le_exp j d
    ((d+j)*probabilityProfileLipschitz) hP
    (by unfold scalarSpatialIndexAllowance; positivity)
    (by unfold scalarSpatialInverseAllowance; positivity)
    (Nat.cast_nonneg d) zero_le_one zero_le_one zero_le_one
    hG hU hV hone hone (by simpa only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast] using hK) hone
  simp only [one_pow, mul_one] at hc
  unfold smoothSpatialDiscretizationCost
  calc
    _ ≤ Real.exp (2*(j : ℝ)^2+(2*j+4)*P+(j+2*d)*(P+4)+4) * (Real.exp l)^j :=
      mul_le_mul hc (pow_le_pow_left₀ (Nat.cast_nonneg _) hL j) (by positivity) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; rfl

theorem spatialKernelErrorConstant_le_exp (j e : ℕ) {U P : ℝ} (K : ℝ≥0)
    (hU0 : 0 ≤ U) (hU : U ≤ Real.exp P) (hK : (K : ℝ) ≤ Real.exp P) :
    spatialKernelErrorConstant j e U 1 K ≤
      Real.exp ((j : ℝ)^2+(j+2)*P+2*e) := by
  have htwo : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  unfold spatialKernelErrorConstant
  norm_num only [mul_one]
  calc
    _ ≤ (Real.exp ((j : ℝ)^2)*(Real.exp P)^j)*(Real.exp 2)^e*Real.exp P*Real.exp P := by
      gcongr
      exact factorial_le_exp_sq j
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      simp only [← Real.exp_add]
      congr 1
      ring

noncomputable def spatialDisplacementLog (j d e n : ℕ) (p : ℝ) : ℝ :=
  (j : ℝ)^2+(j+3)*spatialProfileLog j d p+2*e+n

theorem smoothSpatialDisplacementCost_le_exp {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) {M : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hM : (M : ℝ) ≤ Real.exp p) :
    smoothSpatialDisplacementCost N s M ≤
      Real.exp (spatialDisplacementLog (Fintype.card (Unit ⊕ I))
        (Fintype.card (UnselectedColumn s ⊕ N)) (Fintype.card (UnselectedColumn s))
        (Fintype.card N) p) := by
  let j := Fintype.card (Unit ⊕ I)
  let d := Fintype.card (UnselectedColumn s ⊕ N)
  let e := Fintype.card (UnselectedColumn s)
  let P := spatialProfileLog j d p
  obtain ⟨hG, hU, _, hK⟩ := spatialProfileLog_bounds N s hp hM
  have he : (e : ℝ) ≤ d := by
    simp only [d, e, Fintype.card_sum, Nat.cast_add]
    exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hsmall : ((e+j : ℝ)*probabilityProfileLipschitz) ≤ Real.exp P := by
    apply le_trans _ hK
    gcongr
  have hc := spatialKernelErrorConstant_le_exp j e ((e+j)*probabilityProfileLipschitz)
    (by unfold scalarSpatialInverseAllowance; positivity) hU
    (by simpa only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast] using hsmall)
  have hn : (Fintype.card N : ℝ) ≤ Real.exp (Fintype.card N : ℝ) := by
    linarith [Real.add_one_le_exp (Fintype.card N : ℝ)]
  unfold smoothSpatialDisplacementCost
  calc
    _ ≤ Real.exp P * Real.exp ((j : ℝ)^2+(j+2)*P+2*e) * Real.exp (Fintype.card N : ℝ) := by
      apply mul_le_mul _ hn (Nat.cast_nonneg _) (by positivity)
      exact mul_le_mul hG hc (by unfold spatialKernelErrorConstant scalarSpatialInverseAllowance; positivity)
        (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      dsimp [spatialDisplacementLog, P]
      ring

noncomputable def spatialMeshLog (a b n : ℕ) (l : ℝ) : ℝ :=
  2+5*(1+b+n)+probabilityProfileLipschitz+(a : ℝ)^2+a*l

theorem smoothSpatialMeshThreshold_le_exp (I J N : Type*)
    [Fintype I] [Fintype J] [Fintype N] {L : ℕ} {l : ℝ}
    (hL : (L : ℝ) ≤ Real.exp l) :
    smoothSpatialMeshThreshold I J N L ≤
      Real.exp (spatialMeshLog (Fintype.card I) (Fintype.card J) (Fintype.card N) l) := by
  have htwo : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hd : (1+Fintype.card J+Fintype.card N : ℝ) ≤
      Real.exp (1+Fintype.card J+Fintype.card N : ℝ) := by
    linarith [Real.add_one_le_exp (1+Fintype.card J+Fintype.card N : ℝ)]
  have hk : (probabilityProfileLipschitz : ℝ) ≤ Real.exp probabilityProfileLipschitz := by
    linarith [Real.add_one_le_exp (probabilityProfileLipschitz : ℝ)]
  unfold smoothSpatialMeshThreshold
  calc
    _ ≤ Real.exp 2 * (Real.exp 4)^(1+Fintype.card J+Fintype.card N) *
        Real.exp (1+Fintype.card J+Fintype.card N : ℝ) * Real.exp probabilityProfileLipschitz *
        (Real.exp ((Fintype.card I : ℝ)^2)*(Real.exp l)^Fintype.card I) := by
      gcongr
      exact factorial_le_exp_sq _
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      simp only [← Real.exp_add]
      congr 1
      dsimp [spatialMeshLog]
      push_cast
      ring

end Erdos3

end

end OAI
