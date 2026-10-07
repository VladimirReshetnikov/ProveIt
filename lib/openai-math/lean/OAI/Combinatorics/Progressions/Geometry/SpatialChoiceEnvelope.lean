import OAI.Combinatorics.Progressions.Lattices.PrincipalJoinedResidues
import OAI.Combinatorics.Progressions.Sampling.JointFrozenSamplerLaw
import OAI.Combinatorics.Progressions.Sampling.SpatialGridVolume

namespace OAI

section

namespace Erdos3

theorem smoothSpatialDensityCap_le_exp {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (B : ℕ) {R : ℝ} (hU : scalarSpatialInverseAllowance I B ≤ Real.exp R) :
    smoothSpatialDensityCap s B ≤ Real.exp
      ((Fintype.card (Unit ⊕ I) : ℝ)^2 + Fintype.card (Unit ⊕ I) * R +
        2 * Fintype.card (UnselectedColumn s)) := by
  have hU0 : 0 ≤ scalarSpatialInverseAllowance I B := by unfold scalarSpatialInverseAllowance; positivity
  have hfact := factorial_le_exp_sq (Fintype.card (Unit ⊕ I))
  have htwo : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  unfold smoothSpatialDensityCap
  calc
    _ ≤ Real.exp ((Fintype.card (Unit ⊕ I) : ℝ)^2) *
        (Real.exp R)^Fintype.card (Unit ⊕ I) * (Real.exp 2)^Fintype.card (UnselectedColumn s) := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

theorem smoothSpatialDensityLip_le_exp {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (B : ℕ) {R : ℝ} (hU : scalarSpatialInverseAllowance I B ≤ Real.exp R) :
    smoothSpatialDensityLip s B ≤ Real.exp
      ((Fintype.card (Unit ⊕ I) : ℝ)^2 + (Fintype.card (Unit ⊕ I) + 1) * R +
        3 * Fintype.card (UnselectedColumn s) + Fintype.card (Unit ⊕ I) + probabilityProfileLipschitz) := by
  have hcap := smoothSpatialDensityCap_le_exp s B hU
  have hn : (Fintype.card (UnselectedColumn s) + Fintype.card (Unit ⊕ I) : ℝ) ≤
      Real.exp (Fintype.card (UnselectedColumn s) + Fintype.card (Unit ⊕ I) : ℝ) := by
    linarith [Real.add_one_le_exp (Fintype.card (UnselectedColumn s) + Fintype.card (Unit ⊕ I) : ℝ)]
  have hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp (probabilityProfileLipschitz : ℝ) := by
    linarith [Real.add_one_le_exp (probabilityProfileLipschitz : ℝ)]
  have hcap0 := smoothSpatialDensityCap_nonneg s B
  have hU0 : 0 ≤ scalarSpatialInverseAllowance I B := by unfold scalarSpatialInverseAllowance; positivity
  unfold smoothSpatialDensityLip
  calc
    _ ≤ Real.exp ((Fintype.card (Unit ⊕ I) : ℝ)^2 + Fintype.card (Unit ⊕ I) * R +
        2 * Fintype.card (UnselectedColumn s)) *
        (Real.exp (Fintype.card (UnselectedColumn s) + Fintype.card (Unit ⊕ I) : ℝ) *
          Real.exp (probabilityProfileLipschitz : ℝ)) * Real.exp R := by gcongr
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def spatialGridAccuracy (n j : ℕ) (τ : ℝ) : ℝ := τ/(4*5^(n*j))

theorem spatialGridAccuracy_pos (n j : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    0 < spatialGridAccuracy n j τ := by unfold spatialGridAccuracy; positivity

theorem spatialGridAccuracy_le (n j : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) :
    spatialGridAccuracy n j τ ≤ τ/4 := by
  have hpow : (1 : ℝ) ≤ 5^(n*j) := one_le_pow₀ (by norm_num)
  unfold spatialGridAccuracy
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4*5^(n*j))).mpr
  nlinarith

noncomputable def smoothSpatialPointAccuracy {I J : Type*} [Fintype I] [Fintype J]
    (n : ℕ) (s : I ↪ J) (M smax : ℕ) (τ : ℝ) : ℝ :=
  vectorSpatialAccuracy n
    (2+((M^smax : ℕ) : ℝ)^Fintype.card (Unit ⊕ I)*smoothSpatialDensityCap s M)
    (spatialGridAccuracy n (Fintype.card (Unit ⊕ I)) τ)

theorem smoothSpatialPointAccuracy_pos {I J : Type*} [Fintype I] [Fintype J]
    (n : ℕ) (s : I ↪ J) (M smax : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    0 < smoothSpatialPointAccuracy n s M smax τ := by
  have hC := smoothSpatialDensityCap_nonneg s M
  exact vectorSpatialAccuracy_pos n (by positivity) (spatialGridAccuracy_pos _ _ hτ)

noncomputable def smoothJointResolution {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (n : ℕ) (s : I ↪ J) (M L smax : ℕ) (τ : ℝ) : ℝ :=
  twoTermErrorResolution (smoothSpatialMeshThreshold I J N L)
    (smoothSpatialDiscretizationCost N s M L) (smoothSpatialPointAccuracy n s M smax τ)

noncomputable def smoothJointWidth {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (n : ℕ) (s : I ↪ J) (M smax : ℕ) (τ : ℝ) : ℝ :=
  twoTermErrorWidth (smoothSpatialDisplacementCost N s M) (smoothSpatialPointAccuracy n s M smax τ)

noncomputable def smoothJointRadius {I J : Type*} [Fintype I] [Fintype J]
    (n : ℕ) (s : I ↪ J) (M smax : ℕ) (τ : ℝ) : ℝ :=
  spatialSiteRadius (((M^smax : ℕ) : ℝ)^Fintype.card (Unit ⊕ I))
    (smoothSpatialDensityLip s M) (smoothSpatialPointAccuracy n s M smax τ)

theorem smoothSpatial_output_choices {A I J N U : Type*}
    [Fintype A] [Fintype I] [Fintype J] [Fintype N]
    (s : I ↪ J) (M smax : ℕ) {ℓ : ℕ} (hℓ : 0 < ℓ) {τ : ℝ} (hτ : 0 < τ)
    (L : U → ℕ) (c : A → N → ℤ) (index : A → N → U) :
    let ρ := smoothJointResolution N (Fintype.card A) s M ℓ smax τ
    let ξ := smoothJointWidth N (Fintype.card A) s M smax τ
    let W := fun a n => ((|c a n| : ℤ)+(L (index a n) : ℤ) : ℝ)
    let H := fun a => spatialOutputScale ℓ ρ ξ (W a)
    let Q := fun (_ : A) (_ : N) => ρ
    (∀ a, 0 < H a) ∧ (∀ a, 1 ≤ H a) ∧ (∀ a, ρ ≤ H a/ℓ) ∧
    (∀ a n, 0 < Q a n) ∧ (∀ a n, ρ ≤ Q a n) ∧
    ∀ a n, W a n*Q a n ≤ ξ*H a := by
  have hp := smoothSpatialPointAccuracy_pos (Fintype.card A) s M smax hτ
  obtain ⟨hρ, _, hξ, _, _⟩ := smoothSpatial_error_choices N s M ℓ hp
  let W := fun a n => ((|c a n| : ℤ)+(L (index a n) : ℤ) : ℝ)
  have hW (a) (n) : 0 ≤ W a n := by dsimp only [W]; positivity
  have hs (a) := spatialOutputScale_spec hℓ hρ hξ (W a) (hW a)
  exact ⟨fun a => (hs a).1, fun a => (hs a).2.1, fun a => (hs a).2.2.1,
    fun _ _ => hρ, fun _ _ => le_rfl, fun a n => (hs a).2.2.2 n⟩

theorem smoothSpatial_grid_tolerance {A I J N : Type*}
    [Fintype A] [Fintype I] [Fintype J] [Fintype N]
    (s : I ↪ J) (M L smax : ℕ) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    {m : ℕ} (hm : m ≤ M^smax)
    (H : A → ℝ) (hH : ∀ a, 1 ≤ H a)
    (grid : Finset (A → (Unit ⊕ I) → ℤ))
    (hbox : ∀ v ∈ grid, ∀ a i, |((spatialStar (v a) i : ℤ) : ℝ)/H a| ≤ 1) :
    let ρ := smoothJointResolution N (Fintype.card A) s M L smax τ
    let ξ := smoothJointWidth N (Fintype.card A) s M smax τ
    let r := smoothJointRadius (Fintype.card A) s M smax τ
    let E := smoothSpatialError N s M L ρ ξ
    let G := (m : ℝ)^Fintype.card (Unit ⊕ I)
    let S := Fintype.card A*(E+4*G*smoothSpatialDensityLip s M*r)*
      (1+G*smoothSpatialDensityCap s M+E)^Fintype.card A
    let Δ := S/(∏ a, ∏ _i : Unit ⊕ I, H a)*grid.card
    0 < ρ ∧ smoothSpatialMeshThreshold I J N L ≤ ρ ∧
    0 < ξ ∧ ξ ≤ 1 ∧ 0 < r ∧ Δ ≤ τ/4 ∧ Δ+(1+Δ)*(τ/4) ≤ τ := by
  let ε := spatialGridAccuracy (Fintype.card A) (Fintype.card (Unit ⊕ I)) τ
  let δ := smoothSpatialPointAccuracy (Fintype.card A) s M smax τ
  let ρ := smoothJointResolution N (Fintype.card A) s M L smax τ
  let ξ := smoothJointWidth N (Fintype.card A) s M smax τ
  let r := smoothJointRadius (Fintype.card A) s M smax τ
  let E := smoothSpatialError N s M L ρ ξ
  let G := (m : ℝ)^Fintype.card (Unit ⊕ I)
  let G₀ := ((M^smax : ℕ) : ℝ)^Fintype.card (Unit ⊕ I)
  have hC := smoothSpatialDensityCap_nonneg s M
  have hK := smoothSpatialDensityLip_nonneg s M
  have hε : 0 < ε := spatialGridAccuracy_pos _ _ hτ
  have hε1 : ε ≤ 1 := (spatialGridAccuracy_le _ _ hτ.le).trans (by linarith)
  have hδ : 0 < δ := smoothSpatialPointAccuracy_pos _ s M smax hτ
  obtain ⟨hρ, hmesh, hξ, hξ1, hE⟩ := smoothSpatial_error_choices N s M L hδ
  have hG : 0 ≤ G := by positivity
  have hG₀ : 0 ≤ G₀ := by positivity
  have hGG : G ≤ G₀ := pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hm) _
  have hr : 0 < r := spatialSiteRadius_pos hG₀ hK hδ
  have hE0 : 0 ≤ E := smoothSpatialError_nonneg N s M L hρ.le hξ.le
  have hS : Fintype.card A*(E+4*G*smoothSpatialDensityLip s M*r)*
      (1+G*smoothSpatialDensityCap s M+E)^Fintype.card A ≤ ε := by
    calc
      _ ≤ Fintype.card A*(E+4*G₀*smoothSpatialDensityLip s M*r)*
          (1+G₀*smoothSpatialDensityCap s M+E)^Fintype.card A := by gcongr
      _ ≤ ε := vectorSpatialSiteError_le _ hG₀ hC hK hE0 hε hε1 hE
  have hΔ : (Fintype.card A*(E+4*G*smoothSpatialDensityLip s M*r)*
      (1+G*smoothSpatialDensityCap s M+E)^Fintype.card A)/
      (∏ a, ∏ _i : Unit ⊕ I, H a)*grid.card ≤ τ/4 := by
    calc
      _ ≤ 5^(Fintype.card A*Fintype.card (Unit ⊕ I))*
          (Fintype.card A*(E+4*G*smoothSpatialDensityLip s M*r)*
            (1+G*smoothSpatialDensityCap s M+E)^Fintype.card A) :=
        spatialGrid_error_le H hH grid hbox (by positivity)
      _ ≤ 5^(Fintype.card A*Fintype.card (Unit ⊕ I))*ε :=
        mul_le_mul_of_nonneg_left hS (by positivity)
      _ = τ/4 := by
        dsimp only [ε, spatialGridAccuracy]
        have hp : (5 : ℝ)^(Fintype.card A*Fintype.card (Unit ⊕ I)) ≠ 0 := by positivity
        field_simp
  refine ⟨hρ, hmesh, hξ, hξ1, hr, hΔ, ?_⟩
  have hδ1 : (Fintype.card A*(E+4*G*smoothSpatialDensityLip s M*r)*
      (1+G*smoothSpatialDensityCap s M+E)^Fintype.card A)/
      (∏ a, ∏ _i : Unit ⊕ I, H a)*grid.card ≤ 1 := by linarith
  have hh := mul_le_mul_of_nonneg_right (add_le_add (le_refl (1 : ℝ)) hδ1)
    (show 0 ≤ τ/4 by positivity)
  linarith

end Erdos3

end

section

namespace Erdos3

noncomputable def spatialDensityCapLog (j e : ℕ) (p : ℝ) : ℝ :=
  (j : ℝ)^2+j*(j+(j : ℝ)^2+p)+2*e

noncomputable def spatialDensityLipLog (j e : ℕ) (p : ℝ) : ℝ :=
  (j : ℝ)^2+(j+1)*(j+(j : ℝ)^2+p)+3*e+j+probabilityProfileLipschitz

theorem smoothSpatialDensity_log_bounds {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) {M : ℕ} {p : ℝ} (hM : (M : ℝ) ≤ Real.exp p) :
    smoothSpatialDensityCap s M ≤ Real.exp
      (spatialDensityCapLog (Fintype.card (Unit ⊕ I)) (Fintype.card (UnselectedColumn s)) p) ∧
    smoothSpatialDensityLip s M ≤ Real.exp
      (spatialDensityLipLog (Fintype.card (Unit ⊕ I)) (Fintype.card (UnselectedColumn s)) p) := by
  have hU := scalarSpatialInverseAllowance_le_exp I hM
  have hj : (Fintype.card I+1 : ℝ) = Fintype.card (Unit ⊕ I) := by
    simp only [Fintype.card_sum, Fintype.card_unit, Nat.cast_add, Nat.cast_one]
    ring
  rw [hj] at hU
  exact ⟨smoothSpatialDensityCap_le_exp s M hU, smoothSpatialDensityLip_le_exp s M hU⟩

theorem spatialModulusPower_le_exp (j s : ℕ) {M : ℕ} {p : ℝ}
    (hM : (M : ℝ) ≤ Real.exp p) :
    (((M^s : ℕ) : ℝ)^j) ≤ Real.exp ((j : ℝ)*s*p) := by
  push_cast
  calc
    _ ≤ ((Real.exp p)^s)^j := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      congr 1
      ring

theorem spatialGridAccuracy_inverse_le_exp (n j : ℕ) {τ u : ℝ}
    (hτ : 0 < τ) (hτu : τ⁻¹ ≤ Real.exp u) :
    (spatialGridAccuracy n j τ)⁻¹ ≤ Real.exp (4+5*((n : ℝ)*j)+u) := by
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have h5 : (5 : ℝ) ≤ Real.exp 5 := by linarith [Real.add_one_le_exp (5 : ℝ)]
  rw [spatialGridAccuracy, inv_div, div_eq_mul_inv]
  calc
    _ ≤ Real.exp 4*(Real.exp 5)^(n*j)*Real.exp u := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      push_cast
      congr 1
      ring

noncomputable def spatialPointLog (n j e s : ℕ) (p u : ℝ) : ℝ :=
  (n+1)*((j : ℝ)*s*p+spatialDensityCapLog j e p+7+5*((n : ℝ)*j)+u)+n+1

theorem smoothSpatialPointAccuracy_inverse_le_exp {I J : Type*} [Fintype I] [Fintype J]
    (n : ℕ) (s : I ↪ J) (smax : ℕ) {M : ℕ} {p u τ : ℝ}
    (hp : 0 ≤ p) (hu : 0 ≤ u) (hM : (M : ℝ) ≤ Real.exp p)
    (hτ : 0 < τ) (hτu : τ⁻¹ ≤ Real.exp u) :
    (smoothSpatialPointAccuracy n s M smax τ)⁻¹ ≤
      Real.exp (spatialPointLog n (Fintype.card (Unit ⊕ I))
        (Fintype.card (UnselectedColumn s)) smax p u) := by
  let j := Fintype.card (Unit ⊕ I)
  let e := Fintype.card (UnselectedColumn s)
  let G : ℝ := ((M^smax : ℕ) : ℝ)^j
  let g : ℝ := j*smax*p
  let c := spatialDensityCapLog j e p
  let P := g+c+7+5*((n : ℝ)*j)+u
  have hg : 0 ≤ g := by dsimp [g]; positivity
  have hc : 0 ≤ c := by dsimp [c, spatialDensityCapLog]; positivity
  have hG : G ≤ Real.exp g := spatialModulusPower_le_exp j smax hM
  have hC := (smoothSpatialDensity_log_bounds s hM).1
  have hC0 := smoothSpatialDensityCap_nonneg s M
  have hm : G*smoothSpatialDensityCap s M ≤ Real.exp (g+c) := by
    rw [Real.exp_add]
    exact mul_le_mul hG hC hC0 (Real.exp_pos _).le
  have hbase : 2+G*smoothSpatialDensityCap s M ≤ Real.exp P := by
    have hone : 1 ≤ Real.exp (g+c) := Real.one_le_exp_iff.mpr (by positivity)
    have hthree : (3 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
    calc
      _ ≤ 3*Real.exp (g+c) := by linarith
      _ ≤ Real.exp 3*Real.exp (g+c) := mul_le_mul_of_nonneg_right hthree (Real.exp_pos _).le
      _ = Real.exp (g+c+3) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp P := by
        apply Real.exp_le_exp.mpr
        dsimp [P]
        have hn : 0 ≤ 5*((n : ℝ)*j) := by positivity
        linarith
  have hε : (spatialGridAccuracy n j τ)⁻¹ ≤ Real.exp P := by
    apply (spatialGridAccuracy_inverse_le_exp n j hτ hτu).trans
    apply Real.exp_le_exp.mpr
    dsimp [P]
    linarith
  exact vectorSpatialAccuracy_inverse_le_exp n (by positivity)
    (spatialGridAccuracy_pos n j hτ) hbase hε

noncomputable def spatialChoiceLog (a b n v e s : ℕ) (p l u : ℝ) : ℝ :=
  spatialMeshLog a b n l+spatialDiscretizationLog (a+1) (e+n) p l+
    spatialDisplacementLog (a+1) (e+n) e n p+spatialPointLog v (a+1) e s p u

theorem spatialChoiceLog_nonneg (a b n v e s : ℕ) {p l u : ℝ}
    (hp : 0 ≤ p) (hl : 0 ≤ l) (hu : 0 ≤ u) :
    0 ≤ spatialChoiceLog a b n v e s p l u := by
  unfold spatialChoiceLog spatialMeshLog spatialDiscretizationLog spatialDisplacementLog
    spatialPointLog spatialDensityCapLog spatialProfileLog
  positivity

theorem smoothJointResolution_width_le_exp {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (n : ℕ) (s : I ↪ J) (smax : ℕ)
    {M L : ℕ} {p l u τ : ℝ} (hp : 0 ≤ p) (hl : 0 ≤ l) (hu : 0 ≤ u)
    (hM : (M : ℝ) ≤ Real.exp p) (hL : (L : ℝ) ≤ Real.exp l)
    (hτ : 0 < τ) (hτu : τ⁻¹ ≤ Real.exp u) :
    let P := spatialChoiceLog (Fintype.card I) (Fintype.card J) (Fintype.card N)
      n (Fintype.card (UnselectedColumn s)) smax p l u
    smoothJointResolution N n s M L smax τ ≤ Real.exp (2*P+4) ∧
    (smoothJointWidth N n s M smax τ)⁻¹ ≤ Real.exp (2*P+4) := by
  let T := spatialMeshLog (Fintype.card I) (Fintype.card J) (Fintype.card N) l
  let A := spatialDiscretizationLog (Fintype.card (Unit ⊕ I))
    (Fintype.card (UnselectedColumn s ⊕ N)) p l
  let B := spatialDisplacementLog (Fintype.card (Unit ⊕ I))
    (Fintype.card (UnselectedColumn s ⊕ N)) (Fintype.card (UnselectedColumn s)) (Fintype.card N) p
  let D := spatialPointLog n (Fintype.card (Unit ⊕ I))
    (Fintype.card (UnselectedColumn s)) smax p u
  have hT : 0 ≤ T := by dsimp [T, spatialMeshLog]; positivity
  have hA : 0 ≤ A := by dsimp [A, spatialDiscretizationLog, spatialProfileLog]; positivity
  have hB : 0 ≤ B := by dsimp [B, spatialDisplacementLog, spatialProfileLog]; positivity
  have hD : 0 ≤ D := by dsimp [D, spatialPointLog, spatialDensityCapLog]; positivity
  have hP : 0 ≤ T+A+B+D := by positivity
  have ht : smoothSpatialMeshThreshold I J N L ≤ Real.exp (T+A+B+D) := by
    apply (smoothSpatialMeshThreshold_le_exp I J N hL).trans
    exact Real.exp_le_exp.mpr (by change T ≤ T+A+B+D; linarith)
  have ha : smoothSpatialDiscretizationCost N s M L ≤ Real.exp (T+A+B+D) := by
    apply (smoothSpatialDiscretizationCost_le_exp N s hp hM hL).trans
    exact Real.exp_le_exp.mpr (by change A ≤ T+A+B+D; linarith)
  have hb : smoothSpatialDisplacementCost N s M ≤ Real.exp (T+A+B+D) := by
    apply (smoothSpatialDisplacementCost_le_exp N s hp hM).trans
    exact Real.exp_le_exp.mpr (by change B ≤ T+A+B+D; linarith)
  have hd : (smoothSpatialPointAccuracy n s M smax τ)⁻¹ ≤ Real.exp (T+A+B+D) := by
    apply (smoothSpatialPointAccuracy_inverse_le_exp n s smax hp hu hM hτ hτu).trans
    exact Real.exp_le_exp.mpr (by change D ≤ T+A+B+D; linarith)
  have hh := twoTermErrorChoices_log_bounds (smoothSpatialDiscretizationCost_nonneg N s M L)
    (smoothSpatialDisplacementCost_nonneg N s M) (smoothSpatialPointAccuracy_pos n s M smax hτ)
    hP ht ha hb hd
  simpa only [smoothJointResolution, smoothJointWidth, spatialChoiceLog, T, A, B, D,
    Fintype.card_sum, Fintype.card_unit, Nat.add_comm 1] using hh

theorem smoothJointRadius_inverse_le_exp {I J : Type*} [Fintype I] [Fintype J]
    (n : ℕ) (s : I ↪ J) (smax : ℕ) {M : ℕ} {p u τ : ℝ}
    (hp : 0 ≤ p) (hu : 0 ≤ u) (hM : (M : ℝ) ≤ Real.exp p)
    (hτ : 0 < τ) (hτu : τ⁻¹ ≤ Real.exp u) :
    let j := Fintype.card (Unit ⊕ I)
    let e := Fintype.card (UnselectedColumn s)
    let P := (j : ℝ)*smax*p+spatialDensityLipLog j e p+spatialPointLog n j e smax p u
    (smoothJointRadius n s M smax τ)⁻¹ ≤ Real.exp (3*P+16) := by
  dsimp only
  let j := Fintype.card (Unit ⊕ I)
  let e := Fintype.card (UnselectedColumn s)
  let g : ℝ := j*smax*p
  let k := spatialDensityLipLog j e p
  let d := spatialPointLog n j e smax p u
  have hg : 0 ≤ g := by dsimp [g]; positivity
  have hk : 0 ≤ k := by dsimp [k, spatialDensityLipLog]; positivity
  have hd : 0 ≤ d := by dsimp [d, spatialPointLog, spatialDensityCapLog]; positivity
  have hG : (((M^smax : ℕ) : ℝ)^j) ≤ Real.exp (g+k+d) := by
    apply (spatialModulusPower_le_exp j smax hM).trans
    exact Real.exp_le_exp.mpr (by change g ≤ g+k+d; linarith)
  have hK : smoothSpatialDensityLip s M ≤ Real.exp (g+k+d) := by
    apply (smoothSpatialDensity_log_bounds s hM).2.trans
    exact Real.exp_le_exp.mpr (by change k ≤ g+k+d; linarith)
  have hD : 1/smoothSpatialPointAccuracy n s M smax τ ≤ Real.exp (g+k+d) := by
    rw [one_div]
    apply (smoothSpatialPointAccuracy_inverse_le_exp n s smax hp hu hM hτ hτu).trans
    exact Real.exp_le_exp.mpr (by change d ≤ g+k+d; linarith)
  simpa only [one_div, smoothJointRadius, g, k, d, j, e] using spatialSiteRadius_inverse_le_exp
    (by positivity : (0 : ℝ) ≤ ((M^smax : ℕ) : ℝ)^j) (smoothSpatialDensityLip_nonneg s M)
    (smoothSpatialPointAccuracy_pos n s M smax hτ) (by positivity : 0 ≤ g+k+d) hG hK hD

theorem smoothSpatialOutputScale_le_exp {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N] (n : ℕ) (s : I ↪ J) (smax : ℕ)
    {M L : ℕ} {p l u w τ : ℝ} (hp : 0 ≤ p) (hl : 0 ≤ l) (hu : 0 ≤ u) (hw : 0 ≤ w)
    (hM : (M : ℝ) ≤ Real.exp p) (hL : (L : ℝ) ≤ Real.exp l)
    (hτ : 0 < τ) (hτu : τ⁻¹ ≤ Real.exp u)
    (W : N → ℝ) (hW0 : ∀ i, 0 ≤ W i) (hW : ∀ i, W i ≤ Real.exp w) :
    let P := spatialChoiceLog (Fintype.card I) (Fintype.card J) (Fintype.card N)
      n (Fintype.card (UnselectedColumn s)) smax p l u
    spatialOutputScale L (smoothJointResolution N n s M L smax τ)
      (smoothJointWidth N n s M smax τ) W ≤
        Real.exp (Fintype.card N+3*(l+2*P+4+w)+3) := by
  let P := spatialChoiceLog (Fintype.card I) (Fintype.card J) (Fintype.card N)
    n (Fintype.card (UnselectedColumn s)) smax p l u
  have hP : 0 ≤ P := spatialChoiceLog_nonneg _ _ _ _ _ _ hp hl hu
  obtain ⟨hρ, hξ⟩ := smoothJointResolution_width_le_exp N n s smax hp hl hu hM hL hτ hτu
  obtain ⟨hρ0, _, hξ0, _, _⟩ := smoothSpatial_error_choices N s M L
    (smoothSpatialPointAccuracy_pos n s M smax hτ)
  apply spatialOutputScale_log_bound L hρ0.le hξ0 (by positivity : 0 ≤ l+2*P+4+w) W hW0
  · intro i
    exact (hW i).trans (Real.exp_le_exp.mpr (by linarith))
  · exact hL.trans (Real.exp_le_exp.mpr (by linarith))
  · exact hρ.trans (Real.exp_le_exp.mpr (by change 2*P+4 ≤ l+2*P+4+w; linarith))
  · exact hξ.trans (Real.exp_le_exp.mpr (by change 2*P+4 ≤ l+2*P+4+w; linarith))

end Erdos3

end

section

namespace Erdos3

noncomputable def smoothVectorSpatialError {α G : Type*} [Fintype α] [Fintype G]
    (D N : Type*) [Fintype D] [Fintype N] (selection : α ↪ G)
    (M L modulus : ℕ) (ρ ξ r : ℝ) : ℝ :=
  Fintype.card D * (smoothSpatialError N selection M L ρ ξ+
    4*(modulus : ℝ)^Fintype.card (Unit ⊕ α)*smoothSpatialDensityLip selection M*r) *
    (1+(modulus : ℝ)^Fintype.card (Unit ⊕ α)*smoothSpatialDensityCap selection M+
      smoothSpatialError N selection M L ρ ξ)^Fintype.card D

theorem smoothVectorSpatialError_nonneg {α G : Type*} [Fintype α] [Fintype G]
    (D N : Type*) [Fintype D] [Fintype N] (selection : α ↪ G)
    (M L modulus : ℕ) {ρ ξ r : ℝ} (hρ : 0 ≤ ρ) (hξ : 0 ≤ ξ) (hr : 0 ≤ r) :
    0 ≤ smoothVectorSpatialError D N selection M L modulus ρ ξ r := by
  have hE := smoothSpatialError_nonneg N selection M L hρ hξ
  have hC := smoothSpatialDensityCap_nonneg selection M
  have hK := smoothSpatialDensityLip_nonneg selection M
  unfold smoothVectorSpatialError
  positivity

namespace VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {D N : Type*} [Fintype D] [Fintype N]
variable (c : D → N → ℤ) (index : D → N → PrincipalTupleIndex B (layerSamplerDegree I n))

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

noncomputable def allocatedSpatialColumns
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides) : D → Matrix (Unit ⊕ α) N ℤ :=
  fun d => principalSpatialColumns (c d) (index d) (principalAxisJoin grid u v)

noncomputable def allocatedSpatialResidueColumns (modulus : ℕ)
    (r : PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
      (fun a => layerSamplerDegree I n a.val) → Option α → ZMod modulus) :
    D → Matrix (Unit ⊕ α) N (ZMod modulus) :=
  fun d => principalSpatialResidueColumns modulus (c d) (index d)
    (principalAxisResidueJoin grid u modulus r)

omit [Fintype α] [DecidableEq α] [Fintype D] [Fintype N] in
theorem allocatedSpatialColumns_residue (modulus : ℕ)
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides) (d : D) :
    integerResidueMatrix (allocatedSpatialColumns B U basis S u c index v d) modulus =
      allocatedSpatialResidueColumns B U basis S u c index modulus (principalResidueLabel modulus v) d :=
  principalSpatialColumns_join_residue grid u v modulus (c d) (index d)

omit [Fintype α] [DecidableEq α] [Fintype D] [Fintype N] in
theorem allocatedSpatialColumns_scaled_bound (H : D → ℝ) (Q : D → N → ℝ)
    (hQ : ∀ d j, 0 ≤ Q d j) {ξ : ℝ}
    (hwidth : ∀ d j, ((|c d j| : ℤ)+(sides (index d j) : ℤ) : ℝ)*Q d j ≤ ξ*H d)
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides) (d : D) (i : Unit ⊕ α) (j : N) :
    |(allocatedSpatialColumns B U basis S u c index v d i j : ℝ)| * Q d j ≤ ξ*H d :=
  principalSpatialColumns_scaled_bound (c d) (index d) (Q d) (hQ d) (hwidth d)
    (principalAxisJoin grid u v) i j

variable (x : G → IntegerScalarCubeBox α S.value) (root : G → ℤ)
variable (selection : α ↪ G)
variable (hP : (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection).det ≠ 0)
variable (H : D → ℝ) (Q : D → N → ℝ) (hH : ∀ d, 0 < H d) (hQ : ∀ d j, 0 < Q d j)

noncomputable def allocatedSpatialOutputLaw
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides) : PMF (D → (Unit ⊕ α) → ℤ) :=
  smoothVectorSpatialOutputLaw root (scalarCubeDifferenceMatrix x)
    (allocatedSpatialColumns B U basis S u c index v) H S.value Q hH
    (Nat.cast_pos.mpr S.positive) hQ

variable [DecidableEq G]

noncomputable def allocatedSpatialProxy (modulus : ℕ) [NeZero modulus]
    (r : PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
      (fun a => layerSamplerDegree I n a.val) → Option α → ZMod modulus)
    (mesh : ℝ) (v : D → (Unit ⊕ α) → ℤ) : ℂ :=
  ∏ d, spatialSiteApprox
    (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
    (Matrix.fromCols (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)
      (liftResidueMatrix (allocatedSpatialResidueColumns B U basis S u c index modulus r d)))
    modulus (smoothSpatialKernelDensity selection root (scalarCubeDifferenceMatrix x) hP
      (H d) S.value (hH d) (Nat.cast_pos.mpr S.positive)) (H d) 1 mesh (v d)

variable [DecidableEq N]

theorem allocatedSpatial_site_error {M : ℕ} (hM : 0 < M)
    (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (hroot : ∀ j, |root j| ≤ (S.value : ℤ)) (modulus : ℕ) [NeZero modulus]
    (hp : integerScalarLattice (Unit ⊕ α) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection))
    {ρ ξ mesh : ℝ} (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hwidth : ∀ d j, ((|c d j| : ℤ)+(sides (index d j) : ℤ) : ℝ)*Q d j ≤ ξ*H d)
    (hρ : 0 < ρ) (hscale : ∀ d, ρ ≤ H d/S.value) (hscaleQ : ∀ d j, ρ ≤ Q d j)
    (hlarge : smoothSpatialMeshThreshold α G N S.value ≤ ρ) (hmesh : 0 < mesh)
    (y : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (v : D → (Unit ⊕ α) → ℤ)
    (hv : ∀ d i, |((spatialStar (v d) i : ℤ) : ℝ)/H d| ≤ 1) :
    ‖(((∏ d, ∏ _i : Unit ⊕ α, H d)*
        (allocatedSpatialOutputLaw B U basis S u c index x root H Q hH hQ y v).toReal : ℝ) : ℂ)-
      allocatedSpatialProxy B U basis S u c index x root selection hP H hH modulus
        (principalResidueLabel modulus y) mesh v‖ ≤
      smoothVectorSpatialError D N selection M S.value modulus ρ ξ mesh := by
  have he := smoothVectorSpatial_site_error selection x root hM S.positive hx hroot modulus hp
    (allocatedSpatialColumns B U basis S u c index y) H Q hH hQ hξ0 hξ1
    (allocatedSpatialColumns_scaled_bound B U basis S u c index H Q (fun d j => (hQ d j).le) hwidth y)
    hρ hscale hscaleQ hlarge hmesh v hv
  simpa only [allocatedSpatialOutputLaw, allocatedSpatialProxy, allocatedSpatialColumns_residue,
    smoothVectorSpatialError] using he

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem smoothJointParameters_spec {α G : Type*} [Fintype α] [Fintype G]
    (D N : Type*) [Fintype D] [Fintype N] (selection : α ↪ G)
    (M L smax : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    0 < smoothJointResolution N (Fintype.card D) selection M L smax τ ∧
    smoothSpatialMeshThreshold α G N L ≤ smoothJointResolution N (Fintype.card D) selection M L smax τ ∧
    0 < smoothJointWidth N (Fintype.card D) selection M smax τ ∧
    smoothJointWidth N (Fintype.card D) selection M smax τ ≤ 1 ∧
    0 < smoothJointRadius (Fintype.card D) selection M smax τ := by
  have hδ := smoothSpatialPointAccuracy_pos (Fintype.card D) selection M smax hτ
  obtain ⟨hρ, ht, hξ, hξ1, _⟩ := smoothSpatial_error_choices N selection M L hδ
  exact ⟨hρ, ht, hξ, hξ1, spatialSiteRadius_pos (by positivity)
    (smoothSpatialDensityLip_nonneg selection M) hδ⟩

noncomputable def spatialChosenHeightLog {α G : Type*} [Fintype α] [Fintype G]
    (D N : Type*) [Fintype D] [Fintype N] (selection : α ↪ G)
    (smax : ℕ) (P L E : ℝ) : ℝ :=
  Fintype.card N+3*(L+2*spatialChoiceLog (Fintype.card α) (Fintype.card G)
    (Fintype.card N) (Fintype.card D) (Fintype.card (UnselectedColumn selection))
    smax P L E+4+(P+L+1))+3

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

theorem allocatedPrincipalSides_le_scale (j : PrincipalTupleIndex B (layerSamplerDegree I n)) :
    allocatedPrincipalSides B U basis S j ≤ S.value :=
  layerSamplerSides_le (G := G) B U basis R S.positive (.inr j)

variable {D N : Type*} [Fintype D] [Fintype N]
variable (c : D → N → ℤ) (index : D → N → PrincipalTupleIndex B (layerSamplerDegree I n))

noncomputable def allocatedSpatialColumnWidth (d : D) (j : N) : ℝ :=
  ((|c d j| : ℤ)+(allocatedPrincipalSides B U basis S (index d j) : ℤ) : ℝ)

omit [Fintype D] [Fintype N] in
theorem allocatedSpatialColumnWidth_nonneg (d : D) (j : N) :
    0 ≤ allocatedSpatialColumnWidth B U basis S c index d j := by
  unfold allocatedSpatialColumnWidth
  positivity

omit [Fintype D] [Fintype N] in
theorem allocatedSpatialColumnWidth_le_exp {P L : ℝ} (hP : 0 ≤ P) (hL : 0 ≤ L)
    (hS : (S.value : ℝ) ≤ Real.exp L) (hc : ∀ d j, |(c d j : ℝ)| ≤ Real.exp P)
    (d : D) (j : N) :
    allocatedSpatialColumnWidth B U basis S c index d j ≤ Real.exp (P+L+1) := by
  have hs : (allocatedPrincipalSides B U basis S (index d j) : ℝ) ≤ Real.exp L :=
    (Nat.cast_le.mpr (allocatedPrincipalSides_le_scale B U basis S (index d j))).trans hS
  have hp' : Real.exp P ≤ Real.exp (P+L) := Real.exp_le_exp.mpr (by linarith)
  have hl' : Real.exp L ≤ Real.exp (P+L) := Real.exp_le_exp.mpr (by linarith)
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  unfold allocatedSpatialColumnWidth
  push_cast
  calc
    _ ≤ Real.exp P+Real.exp L := add_le_add (hc d j) hs
    _ ≤ 2*Real.exp (P+L) := by linarith
    _ ≤ Real.exp 1*Real.exp (P+L) := mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

variable {α : Type*} [Fintype α] (selection : α ↪ G) (M : ℕ) (τ : ℝ)

noncomputable def allocatedSpatialHeight (d : D) : ℝ :=
  spatialOutputScale S.value
    (smoothJointResolution N (Fintype.card D) selection M S.value (m+1) τ)
    (smoothJointWidth N (Fintype.card D) selection M (m+1) τ)
    (allocatedSpatialColumnWidth B U basis S c index d)

local notation "H" => allocatedSpatialHeight B U basis S c index selection M τ
local notation "ρ" => smoothJointResolution N (Fintype.card D) selection M (LayerSamplerScale.value S) (m+1) τ
local notation "ξ" => smoothJointWidth N (Fintype.card D) selection M (m+1) τ

theorem allocatedSpatialHeight_spec (hτ : 0 < τ) :
    (∀ d, 0 < H d) ∧ (∀ d, 1 ≤ H d) ∧ (∀ d, ρ ≤ H d/S.value) ∧
    ∀ d j, allocatedSpatialColumnWidth B U basis S c index d j*ρ ≤ ξ*H d := by
  obtain ⟨h0, h1, hr, _, _, hw⟩ := smoothSpatial_output_choices selection M (m+1) S.positive hτ
    (allocatedPrincipalSides B U basis S) c index
  exact ⟨h0, h1, hr, hw⟩

theorem allocatedSpatialHeight_pos (hτ : 0 < τ) (d : D) : 0 < H d :=
  (allocatedSpatialHeight_spec B U basis S c index selection M τ hτ).1 d

theorem allocatedSpatialHeight_one_le (hτ : 0 < τ) (d : D) : 1 ≤ H d :=
  (allocatedSpatialHeight_spec B U basis S c index selection M τ hτ).2.1 d

theorem allocatedSpatialHeight_le_exp {P L E : ℝ} (hP : 0 ≤ P) (hL : 0 ≤ L) (hE : 0 ≤ E)
    (hM : (M : ℝ) ≤ Real.exp P) (hS : (S.value : ℝ) ≤ Real.exp L)
    (hτ : 0 < τ) (hτE : τ⁻¹ ≤ Real.exp E) (hc : ∀ d j, |(c d j : ℝ)| ≤ Real.exp P)
    (d : D) : H d ≤ Real.exp (spatialChosenHeightLog D N selection (m+1) P L E) := by
  exact smoothSpatialOutputScale_le_exp (Fintype.card D) selection (m+1) hP hL hE (by positivity)
    hM hS hτ hτE (allocatedSpatialColumnWidth B U basis S c index d)
    (allocatedSpatialColumnWidth_nonneg B U basis S c index d)
    (allocatedSpatialColumnWidth_le_exp B U basis S c index hP hL hS hc d)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

def spatialProfileEnvelope {A : Type*} [Semiring A] (Z : A) : A :=
  (Z+1+1)*Z+(Z+1)^2+2*(Z+1)+(Z+Z)+Z+1

def spatialCapEnvelope {A : Type*} [Semiring A] (Z : A) : A :=
  (Z+1)^2+(Z+1)*((Z+1)+(Z+1)^2+Z)+2*Z

def spatialLipEnvelope {A : Type*} [Semiring A] (Z : A) : A :=
  (Z+1)^2+(Z+1+1)*((Z+1)+(Z+1)^2+Z)+3*Z+(Z+1)+Z

def spatialPointEnvelope {A : Type*} [Semiring A] (Z : A) : A :=
  (Z+1)*((Z+1)*Z*Z+spatialCapEnvelope Z+7+5*(Z*(Z+1))+Z)+Z+1

def spatialChoiceEnvelope {A : Type*} [Semiring A] (Z : A) : A :=
  (2+5*(1+Z+Z)+Z+Z^2+Z*Z)+
  (2*(Z+1)^2+(2*(Z+1)+4)*spatialProfileEnvelope Z+
    ((Z+1)+2*(Z+Z))*(spatialProfileEnvelope Z+4)+4+(Z+1)*Z)+
  ((Z+1)^2+(Z+1+3)*spatialProfileEnvelope Z+2*Z+Z)+spatialPointEnvelope Z

def spatialHeightEnvelope {A : Type*} [Semiring A] (Z : A) : A :=
  Z+3*(Z+2*spatialChoiceEnvelope Z+4+(Z+Z+1))+3

def spatialRadiusEnvelope {A : Type*} [Semiring A] (Z : A) : A :=
  3*((Z+1)*Z*Z+spatialLipEnvelope Z+spatialPointEnvelope Z)+16

def spatialParameterEnvelope {A : Type*} [Semiring A] (Z : A) : A :=
  spatialHeightEnvelope Z+(2*spatialChoiceEnvelope Z+4)+spatialRadiusEnvelope Z

theorem spatialEnvelopes_nonneg {Z : ℝ} (hZ : 0 ≤ Z) :
    0 ≤ spatialProfileEnvelope Z ∧ 0 ≤ spatialCapEnvelope Z ∧
    0 ≤ spatialLipEnvelope Z ∧ 0 ≤ spatialPointEnvelope Z ∧
    0 ≤ spatialChoiceEnvelope Z ∧ 0 ≤ spatialHeightEnvelope Z ∧
    0 ≤ spatialRadiusEnvelope Z := by
  simp only [spatialProfileEnvelope, spatialCapEnvelope, spatialLipEnvelope,
    spatialPointEnvelope, spatialChoiceEnvelope, spatialHeightEnvelope, spatialRadiusEnvelope]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> positivity

theorem spatialProfileLog_le_envelope {a e n : ℕ} {p Z : ℝ}
    (hp : 0 ≤ p) (hZ : 0 ≤ Z) (ha : (a : ℝ) ≤ Z) (he : (e : ℝ) ≤ Z)
    (hn : (n : ℝ) ≤ Z) (hpZ : p ≤ Z) (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Z) :
    spatialProfileLog (a+1) (e+n) p ≤ spatialProfileEnvelope Z := by
  unfold spatialProfileLog spatialProfileEnvelope
  push_cast
  gcongr

theorem spatialCapLog_le_envelope {a e : ℕ} {p Z : ℝ}
    (hp : 0 ≤ p) (hZ : 0 ≤ Z) (ha : (a : ℝ) ≤ Z) (he : (e : ℝ) ≤ Z) (hpZ : p ≤ Z) :
    spatialDensityCapLog (a+1) e p ≤ spatialCapEnvelope Z := by
  unfold spatialDensityCapLog spatialCapEnvelope
  push_cast
  gcongr

theorem spatialLipLog_le_envelope {a e : ℕ} {p Z : ℝ}
    (hp : 0 ≤ p) (hZ : 0 ≤ Z) (ha : (a : ℝ) ≤ Z) (he : (e : ℝ) ≤ Z)
    (hpZ : p ≤ Z) (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Z) :
    spatialDensityLipLog (a+1) e p ≤ spatialLipEnvelope Z := by
  unfold spatialDensityLipLog spatialLipEnvelope
  push_cast
  gcongr

theorem spatialPointLog_le_envelope {v a e s : ℕ} {p u Z : ℝ}
    (hp : 0 ≤ p) (hu : 0 ≤ u) (hZ : 0 ≤ Z)
    (hv : (v : ℝ) ≤ Z) (ha : (a : ℝ) ≤ Z) (he : (e : ℝ) ≤ Z) (hs : (s : ℝ) ≤ Z)
    (hpZ : p ≤ Z) (huZ : u ≤ Z) :
    spatialPointLog v (a+1) e s p u ≤ spatialPointEnvelope Z := by
  have hcap := spatialCapLog_le_envelope hp hZ ha he hpZ
  have hc0 : 0 ≤ spatialDensityCapLog (a+1) e p := by unfold spatialDensityCapLog; positivity
  have he0 := (spatialEnvelopes_nonneg hZ).2.1
  unfold spatialPointLog spatialPointEnvelope
  push_cast
  gcongr

theorem spatialChoiceLog_le_envelope {a b n v e s : ℕ} {p l u Z : ℝ}
    (hp : 0 ≤ p) (hl : 0 ≤ l) (hu : 0 ≤ u) (hZ : 0 ≤ Z)
    (ha : (a : ℝ) ≤ Z) (hb : (b : ℝ) ≤ Z) (hn : (n : ℝ) ≤ Z)
    (hv : (v : ℝ) ≤ Z) (he : (e : ℝ) ≤ Z) (hs : (s : ℝ) ≤ Z)
    (hpZ : p ≤ Z) (hlZ : l ≤ Z) (huZ : u ≤ Z)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Z) :
    spatialChoiceLog a b n v e s p l u ≤ spatialChoiceEnvelope Z := by
  have hf := spatialProfileLog_le_envelope hp hZ ha he hn hpZ hprofile
  have hf0 := spatialProfileLog_nonneg (a+1) (e+n) hp
  have he0 := (spatialEnvelopes_nonneg hZ).1
  have ht := spatialPointLog_le_envelope hp hu hZ hv ha he hs hpZ huZ
  unfold spatialChoiceLog spatialChoiceEnvelope spatialMeshLog
    spatialDiscretizationLog spatialDisplacementLog
  push_cast
  gcongr

theorem spatialChosenHeightLog_le_envelope {α G D N : Type*}
    [Fintype α] [Fintype G] [Fintype D] [Fintype N] (selection : α ↪ G)
    {s : ℕ} {p l u Z : ℝ} (hp : 0 ≤ p) (hl : 0 ≤ l) (hu : 0 ≤ u) (hZ : 0 ≤ Z)
    (ha : (Fintype.card α : ℝ) ≤ Z) (hg : (Fintype.card G : ℝ) ≤ Z)
    (hn : (Fintype.card N : ℝ) ≤ Z) (hd : (Fintype.card D : ℝ) ≤ Z)
    (he : (Fintype.card (UnselectedColumn selection) : ℝ) ≤ Z) (hs : (s : ℝ) ≤ Z)
    (hpZ : p ≤ Z) (hlZ : l ≤ Z) (huZ : u ≤ Z)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Z) :
    spatialChosenHeightLog D N selection s p l u ≤ spatialHeightEnvelope Z := by
  have hc := spatialChoiceLog_le_envelope hp hl hu hZ ha hg hn hd he hs hpZ hlZ huZ hprofile
  have hc0 := spatialChoiceLog_nonneg (Fintype.card α) (Fintype.card G) (Fintype.card N)
    (Fintype.card D) (Fintype.card (UnselectedColumn selection)) s hp hl hu
  have he0 := (spatialEnvelopes_nonneg hZ).2.2.2.2.1
  unfold spatialChosenHeightLog spatialHeightEnvelope
  gcongr

theorem spatialRadiusLog_le_envelope {v a e s : ℕ} {p u Z : ℝ}
    (hp : 0 ≤ p) (hu : 0 ≤ u) (hZ : 0 ≤ Z)
    (hv : (v : ℝ) ≤ Z) (ha : (a : ℝ) ≤ Z) (he : (e : ℝ) ≤ Z) (hs : (s : ℝ) ≤ Z)
    (hpZ : p ≤ Z) (huZ : u ≤ Z) (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Z) :
    3*((a+1 : ℕ)*s*p+spatialDensityLipLog (a+1) e p+spatialPointLog v (a+1) e s p u)+16 ≤
      spatialRadiusEnvelope Z := by
  have hL := spatialLipLog_le_envelope hp hZ ha he hpZ hprofile
  have hT := spatialPointLog_le_envelope hp hu hZ hv ha he hs hpZ huZ
  unfold spatialRadiusEnvelope
  push_cast
  gcongr

end Erdos3

end

end OAI
