import GowersSzemeredi.Proofs18GradedExponents
import GowersSzemeredi.Proofs18GenericThresholds

/-! The thresholds of the graded single-piece step (Notes L.10, G6).

* `gradedNestExp_anti_blocks`: every block's exponent, and every prefix
  exponent, is at least the full graded exponent.
* `gradedNestThr_le_exp`: if every level's width threshold is at most
  `exp(X^(2^A))` and the full exponent satisfies `e⁻¹ ≤ X^(2^B)`, the graded
  nested threshold is at most `exp(X^(2^(max A B + 2)))`. The bound is
  uniform in the number of blocks: each root `^(1/e_J)` sees `e_J ≥ e`.
* `MReq_le_expG`, `Tloc_le_expG`: the uniform proofs, graded. The threshold
  degree is `threshDegG = max(expDegG + 4, 2^(k+6) + 5)`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Prefix exponents of the graded width decrease; each block's exponent is at
least the full one. -/
theorem gradedNestExp_anti_blocks {E : Nat → Real → Real} {k : Nat} {C : Nat → Real → Real}
    (hE : ∀ l s, 0 < s → s ≤ 1 → 0 < E l s ∧ E l s ≤ 1)
    (hC : ∀ l u, 0 < u → u ≤ 1 → 0 < C l u ∧ C l u ≤ 1) (n : Nat → Nat) {t : Real}
    (ht : 0 < t) (ht1 : t ≤ 1) :
    ∀ K, (∀ J, J ≤ K → gradedNestExp E k C n K t ≤ gradedNestExp E k C n J t) ∧
      (∀ j, j < K → gradedNestExp E k C n K t ≤
        genNestExp (E j) k (C j) (n j) (gradedNestC C n j t)) := by
  intro K
  induction K with
  | zero =>
    refine ⟨fun J hJ => ?_, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    obtain rfl : J = 0 := by omega
    exact le_rfl
  | succ K ih =>
    obtain ⟨ih1, ih2⟩ := ih
    obtain ⟨e0, e1, -, -⟩ := gradedNest_facts hE k hC n K t ht ht1
    obtain ⟨c0, c1⟩ := gradedNestC_pos_le hC n K t ht ht1
    obtain ⟨g0, g1, -, -⟩ := genNest_facts (hE K) k (hC K) (n K) _ c0 c1
    have hstep : gradedNestExp E k C n (K + 1) t ≤ gradedNestExp E k C n K t := by
      show gradedNestExp E k C n K t * genNestExp (E K) k (C K) (n K) (gradedNestC C n K t) ≤ _
      exact mul_le_of_le_one_right e0.le g1
    refine ⟨fun J hJ => ?_, fun j hj => ?_⟩
    · rcases Nat.lt_or_ge J (K + 1) with h | h
      · exact hstep.trans (ih1 J (by omega))
      · obtain rfl : J = K + 1 := by omega
        exact le_rfl
    · rcases Nat.lt_or_ge j K with h | h
      · exact hstep.trans (ih2 j h)
      · obtain rfl : j = K := by omega
        show gradedNestExp E k C n j t * genNestExp (E j) k (C j) (n j) (gradedNestC C n j t) ≤ _
        exact mul_le_of_le_one_left g0.le e1

/-- **The graded nested threshold is single exponential.** -/
theorem gradedNestThr_le_exp {X : Real} (hX : 2 ≤ X) {E : Nat → Real → Real} {k : Nat}
    {C : Nat → Real → Real}
    (hE : ∀ l s, 0 < s → s ≤ 1 → 0 < E l s ∧ E l s ≤ 1)
    (hC : ∀ l u, 0 < u → u ≤ 1 → 0 < C l u ∧ C l u ≤ 1) (n : Nat → Nat) {t : Real}
    (ht : 0 < t) (ht1 : t ≤ 1) {A B K : Nat}
    (hA : ∀ j i, j < K → i < n j →
      genWThr (E j) k (nestC (fun _ => C j) i (gradedNestC C n j t)) ≤ Real.exp (X ^ (2 ^ A)))
    (hB : (gradedNestExp E k C n K t)⁻¹ ≤ X ^ (2 ^ B)) :
    gradedNestThr E k C n K t ≤ Real.exp (X ^ (2 ^ (max A B + 2))) := by
  obtain ⟨hpre, hblk⟩ := gradedNestExp_anti_blocks hE hC n ht ht1 K
  obtain ⟨eK0, -, -, -⟩ := gradedNest_facts hE k hC n K t ht ht1
  have hJ : ∀ J, J ≤ K → gradedNestThr E k C n J t ≤ Real.exp (X ^ (2 ^ (max A B + 2))) := by
    intro J
    induction J with
    | zero =>
      intro _
      show (1 : Real) ≤ _
      exact Real.one_le_exp (by positivity)
    | succ J ih =>
      intro hJK
      obtain ⟨eJ0, -, -, -⟩ := gradedNest_facts hE k hC n J t ht ht1
      obtain ⟨c0, c1⟩ := gradedNestC_pos_le hC n J t ht ht1
      obtain ⟨g0, -, gt1, -⟩ := genNest_facts (hE J) k (hC J) (n J) _ c0 c1
      have hBJ : (genNestExp (E J) k (C J) (n J) (gradedNestC C n J t))⁻¹ ≤ X ^ (2 ^ B) :=
        (inv_anti₀ eK0 (hblk J (by omega))).trans hB
      have hblock := genNestThr_le_exp hX (hE J) (hC J) c0 c1 (n J)
        (fun i hi => hA J i (by omega) hi) hBJ
      have hBpre : (gradedNestExp E k C n J t)⁻¹ ≤ X ^ (2 ^ B) :=
        (inv_anti₀ eK0 (hpre J (by omega))).trans hB
      show max (gradedNestThr E k C n J t)
        (genNestThr (E J) k (C J) (n J) (gradedNestC C n J t) ^ (1 / gradedNestExp E k C n J t)) ≤ _
      refine max_le (ih (by omega)) ?_
      rw [one_div]
      refine (ex_rpow hX gt1 hblock (inv_pos.mpr eJ0).le hBpre).trans (ex_mono hX le_rfl ?_)
      omega
  exact hJ K le_rfl

namespace GenParamsG

variable (P : GenParamsG) {alpha : Real}

/-- The threshold degree of the graded step. -/
def threshDegG (k μ0 μK : Nat) : Nat := max (expDegG k μ0 μK + 4) (2 ^ (k + 6) + 5)

/-- **The requirement on `m`**, graded. -/
theorem MReq_le_expG {μV μK : Nat} (H : GHyp P μV μK) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    1 ≤ P.MReq alpha ∧
      P.MReq alpha ≤ Real.exp ((2 / alpha) ^ (2 ^ max (expDegG P.k P.μ0 μK + 3) (2 ^ (P.k + 6) + 4))) := by
  have hX := two_div_ge_two ha ha2
  have hX1 : (1 : Real) ≤ 2 / alpha := by linarith
  obtain ⟨-, hQM, hBx⟩ := P.spectrum_exps_inv_leG H ha ha2
  have hri := P.rho1_inv_leG ha ha2 H.hk0 H.hk68
  set k := P.k with hkdef
  set E := expDegG k P.μ0 μK with hEdef
  set Z := 2 ^ (k + 6) + 1 with hZdef
  have hZ2 : 2 ≤ Z := by rw [hZdef]; have := Nat.one_le_two_pow (n := k + 6); omega
  have hρE : rhoDegG k P.μ0 + 68 * 2 ^ k + k + 7 ≤ E := by
    rw [hEdef]; unfold expDegG; exact (le_max_left _ _).trans (le_max_right _ _)
  have hKE : μK + 2 ≤ E := by
    rw [hEdef]; unfold expDegG; exact (le_max_right _ _).trans (le_max_right _ _)
  -- the recurrence threshold
  have hthr := familyRecThr_le_exp (k := k) hX (by have := H.hK; omega) H.hKμ H.hpμ hQM
  have hthr' : (familyRecThr k P.K P.p (P.QM alpha) : Real) ≤
      Real.exp ((2 / alpha) ^ (2 ^ (E + 3))) := ex_mono hX hthr (by omega)
  have hthr1 : (1 : Real) ≤ (familyRecThr k P.K P.p (P.QM alpha) : Real) :=
    Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr
      (familyRecThr_pos (k := k) (p := P.p) (by have := H.hK; omega) _).ne')
  -- the Bohr radius and `ρ`
  obtain ⟨hz0, hzi⟩ := zeta_gen_bounds k ha ha2
  have hzeq : P.Zeta alpha = section16Zeta alpha (alpha / 2) k := rfl
  obtain ⟨ht0, ht1, -⟩ := T2_gen_bounds k ha ha2
  have hC : ∀ l u, 0 < u → u ≤ 1 → 0 < P.Cg alpha l u ∧ P.Cg alpha l u ≤ 1 :=
    fun l => genC_pos_le hX1 _ _ _ _
  obtain ⟨hr0, hr1⟩ : 0 < P.Rho1 alpha ∧ P.Rho1 alpha ≤ 1 := gradedNestC_pos_le hC _ _ _ ht0 ht1
  have hρ1 : 1 ≤ rhoDegG k P.μ0 := by have := (rhoDegG_ge k P.μ0).1; omega
  obtain ⟨hR0, -, hRi⟩ := GenParams.rho_step hX hr0 hr1 hri hρ1
  have hReq : P.Rho alpha = P.Rho1 alpha / 2 * (P.Rho1 alpha / 2 / 2) := rfl
  rw [← hReq] at hR0 hRi
  have hBpos : 0 < P.Bexp alpha := by
    have := familyRecExp_pos k P.p (P.QM alpha) H.hp
    show 0 < familyRecExp k P.p _ / 2; positivity
  set z := P.Zeta alpha with hzdef
  set R := P.Rho alpha with hRdef
  set B := P.Bexp alpha with hBdef
  rw [← hzeq] at hz0 hzi
  have hcz (c : Real) (hc : c ≤ 16) :
      c / z ≤ Real.exp ((2 / alpha) ^ (2 ^ (Z + 1))) := by
    rw [div_eq_mul_inv]
    exact ex_mono hX (ex_mul' hX (inv_pos.mpr hz0).le
      (ex_of_pw (pw_const hX (a := 2) (by norm_num; exact hc))) hzi) (by omega)
  have hR3 : (R ^ 3)⁻¹ ≤ (2 / alpha) ^ (2 ^ (rhoDegG k P.μ0 + 2 + 2)) := by
    rw [← inv_pow]; exact pw_pow hX (inv_pos.mpr hR0).le hRi (by norm_num)
  have h4zr : 4 / (z * R ^ 3) ≤
      Real.exp ((2 / alpha) ^ (2 ^ (max (Z + 1) (rhoDegG k P.μ0 + 4) + 1))) := by
    rw [div_eq_mul_inv, mul_inv, ← mul_assoc]
    have h4z := hcz 4 (by norm_num)
    rw [div_eq_mul_inv] at h4z
    exact ex_mul' hX (inv_pos.mpr (pow_pos hR0 3)).le h4z (ex_of_pw hR3)
  have hBe : 1 / B ≤ (2 / alpha) ^ (2 ^ E) := by rw [one_div]; exact hBx
  have hBe2 : 2 / B ≤ (2 / alpha) ^ (2 ^ (E + 1)) := by
    rw [div_eq_mul_inv]
    exact pw_mul hX (by norm_num) (inv_pos.mpr hBpos).le (hX.trans (pw_X hX _)) hBx
  have e1 := ex_rpow_of_nonneg hX (by positivity) (hcz 8 (by norm_num)) (by positivity) hBe
  have e2 := ex_rpow_of_nonneg hX (by positivity) h4zr (by positivity) hBe
  have e3 := ex_rpow_of_nonneg hX (by positivity) (hcz 16 le_rfl) (by positivity) hBe2
  refine ⟨hthr1.trans (le_max_left _ _), ?_⟩
  show max (familyRecThr k P.K P.p (P.QM alpha) : Real)
    (max ((8 / z) ^ (1 / B)) (max ((4 / (z * R ^ 3)) ^ (1 / B)) ((16 / z) ^ (2 / B)))) ≤ _
  refine max_le (ex_mono hX hthr' (le_max_left _ _)) (max_le ?_ (max_le ?_ ?_))
  · exact ex_mono hX e1 (by rw [hZdef]; have := Nat.one_le_two_pow (n := k + 6); omega)
  · exact ex_mono hX e2 (by rw [hZdef]; have := Nat.one_le_two_pow (n := k + 6); omega)
  · exact ex_mono hX e3 (by rw [hZdef]; have := Nat.one_le_two_pow (n := k + 6); omega)

/-- **The modulus threshold of the graded step is single exponential.** -/
theorem Tloc_le_expG {μV μK : Nat} (H : GHyp P μV μK) (hk : 1 ≤ P.k) (ha : 0 < alpha)
    (ha2 : alpha ≤ 1 / 2) :
    P.Tloc alpha ≤ Real.exp ((2 / alpha) ^ (2 ^ threshDegG P.k P.μ0 μK)) := by
  have hX := two_div_ge_two ha ha2
  have hX1 : (1 : Real) ≤ 2 / alpha := by linarith
  obtain ⟨hEl0, hEli⟩ := P.Eloc_inv_leG H ha ha2
  obtain ⟨hEm, -, -⟩ := P.spectrum_exps_inv_leG H ha ha2
  have hNE := P.nestExp_inv_leG H ha ha2
  obtain ⟨-, -, -, -, -, -, -, ⟨hEm0, -⟩, -, -, ⟨hN0, -, -⟩, -, -, hEw, hC⟩ :=
    P.ranges H.hV H.hp ha ha2
  have hri := P.rho1_inv_leG ha ha2 H.hk0 H.hk68
  obtain ⟨hR1, hR⟩ := P.MReq_le_expG H ha ha2
  have hL := lemma156_gen_le hk ha ha2
  set k := P.k with hkdef
  set E := expDegG k P.μ0 μK with hEdef
  set T := threshDegG k P.μ0 μK with hTdef
  set μD := 68 * 2 ^ k with hμDdef
  have hET : E + 4 ≤ T := by rw [hTdef]; unfold threshDegG; exact le_max_left _ _
  have hZT : 2 ^ (k + 6) + 5 ≤ T := by rw [hTdef]; unfold threshDegG; exact le_max_right _ _
  have hρE : rhoDegG k P.μ0 + μD + k + 7 ≤ E := by
    rw [hEdef]; unfold expDegG; exact (le_max_left _ _).trans (le_max_right _ _)
  obtain ⟨hρ0, hρ2⟩ := rhoDegG_ge k P.μ0
  have hNE' : (P.NestExp alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ E) := pw_mono hX hNE (by omega)
  have hEm' : (P.Em alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ E) := pw_mono hX hEm (by omega)
  have hMx : (P.MExp alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ (E + 2)) := by
    show (P.NestExp alpha * (P.Em alpha / 2))⁻¹ ≤ _
    rw [show (P.NestExp alpha * (P.Em alpha / 2))⁻¹ =
      2 * ((P.NestExp alpha)⁻¹ * (P.Em alpha)⁻¹) by field_simp]
    have p1 := pw_mul hX (inv_pos.mpr hN0).le (inv_pos.mpr hEm0).le hNE' hEm'
    exact pw_mul hX (by norm_num) (by positivity) (hX.trans (pw_X hX _)) p1
  have hMx0 : 0 < P.MExp alpha := by
    show 0 < P.NestExp alpha * (P.Em alpha / 2)
    positivity
  -- the nested width threshold
  obtain ⟨ht0, ht1, -⟩ := T2_gen_bounds k ha ha2
  have hb1 : ∀ l, 1 ≤ P.bg l := fun l => by show 1 ≤ uDeg68 l + 1 + P.k; omega
  obtain ⟨hr0, -⟩ : 0 < P.Rho1 alpha ∧ P.Rho1 alpha ≤ 1 := gradedNestC_pos_le hC _ _ _ ht0 ht1
  have hdec : ∀ j r t, 0 < t → t ≤ 1 → nestC (fun _ => P.Cg alpha j) r t ≤ t := by
    intro j r t h0 h1
    exact nestC_genC_anti hX1 (hb1 j) (P.baseCg alpha j) P.k h0 h1 0 r (Nat.zero_le _)
  have hDk : ∀ j, j ≤ k → uDeg68 j ≤ 2 ^ μD := fun j hj =>
    Nat.pow_le_pow_right (by norm_num)
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hj))
  have hlevW : ∀ j i, j < k + 1 → i < vertexFaceCounts k j →
      genWThr (P.Ewg alpha j) k (nestC (fun _ => P.Cg alpha j) i
        (gradedNestC (fun l => P.Cg alpha l) (vertexFaceCounts k) j (P.T2 alpha))) ≤
        Real.exp ((2 / alpha) ^ (2 ^ (rhoDegG k P.μ0 + μD + 3 + 4))) := by
    intro j i hj hi
    obtain ⟨c0, c1⟩ := gradedNestC_pos_le hC (vertexFaceCounts k) j _ ht0 ht1
    obtain ⟨u0, u1⟩ := nestC_pos_le (c := fun _ => P.Cg alpha j) (fun _ => hC j) i _ c0 c1
    have hu1 := nestC_genC_anti (a := P.ag j) hX1 (hb1 j) (P.baseCg alpha j) P.k c0 c1 i _ hi.le
    have hu2 : P.Rho1 alpha ≤ gradedNestC (fun l => P.Cg alpha l) (vertexFaceCounts k) (j + 1)
        (P.T2 alpha) :=
      gradedNestC_anti hC hdec _ ht0 ht1 (j + 1) (k + 1) (by omega)
    have hui := (inv_anti₀ hr0 (hu2.trans hu1)).trans hri
    have hl := GenParams.lw_level_inv_le (D := uDeg68 j) ha ha2 H.hV H.hVμ H.hμ0 (hDk j (by omega))
      u0 u1 hui hρ2 (by omega)
    obtain ⟨hl0, -⟩ := lwE_pos_le (hEw j) k u0 u1
    refine genWThr_le_exp hX hl0 hl ?_
    have := Nat.lt_two_pow_self (n := rhoDegG k P.μ0 + μD + 3)
    unfold fixDeg at hρ2
    have : k ≤ 2 ^ (k + 5) := by have := Nat.lt_two_pow_self (n := k + 5); omega
    omega
  have hNT := gradedNestThr_le_exp hX hEw hC (vertexFaceCounts k) ht0 ht1 hlevW hNE'
  have hNT' : P.NestThr alpha ≤ Real.exp ((2 / alpha) ^ (2 ^ T)) := ex_mono hX hNT (by omega)
  -- the roots
  have h64 : (64 : Real) ^ (1 / P.NestExp alpha) ≤ Real.exp ((2 / alpha) ^ (2 ^ T)) :=
    ex_mono hX (ex_root (j := 3) hX (by norm_num) (by norm_num) hN0 hNE') (by omega)
  have h4 : (4 : Real) ^ (1 / P.NestExp alpha) ≤ Real.exp ((2 / alpha) ^ (2 ^ T)) :=
    ex_mono hX (ex_root (j := 2) hX (by norm_num) (by norm_num) hN0 hNE') (by omega)
  have h6 : (6 : Real) ^ (1 / P.Eloc alpha) ≤ Real.exp ((2 / alpha) ^ (2 ^ T)) :=
    ex_mono hX (ex_root (j := 2) hX (by norm_num) (by norm_num) hEl0 hEli) (by omega)
  have hF : P.F alpha = 8 * P.Eloc alpha := by show P.F alpha = 8 * (P.F alpha / 8); ring
  have h8 : (8 : Real) ^ (2 / P.F alpha) ≤ Real.exp ((2 / alpha) ^ (2 ^ T)) := by
    have hle : 2 / P.F alpha ≤ 1 / P.Eloc alpha := by
      rw [hF, div_le_div_iff₀ (by positivity) hEl0]; nlinarith
    refine (Real.rpow_le_rpow_of_exponent_le (by norm_num) hle).trans ?_
    exact ex_mono hX (ex_root (j := 2) hX (by norm_num) (by norm_num) hEl0 hEli) (by omega)
  -- the requirement on `m`
  have hMR : P.MReq alpha ^ (1 / P.MExp alpha) ≤ Real.exp ((2 / alpha) ^ (2 ^ T)) := by
    rw [one_div]
    refine ex_mono hX (ex_rpow hX hR1 hR (inv_pos.mpr hMx0).le hMx) ?_
    rw [hTdef]; unfold threshDegG; omega
  have hMT : P.MThr alpha ≤ Real.exp ((2 / alpha) ^ (2 ^ T)) := max_le hNT' h64
  -- Lemma 15.6
  have hL' : lemma156ExplicitThreshold k (alpha / 2) (alpha / 2) ≤
      Real.exp ((2 / alpha) ^ (2 ^ T)) := by
    refine ex_of_pw (pw_mono hX hL ?_)
    have : 2 ^ (k + 4) + 4 * k + 13 ≤ 2 ^ (k + 6) + 5 := by
      have h := Nat.lt_two_pow_self (n := k)
      have h4 : 2 ^ (k + 4) = 16 * 2 ^ k := by rw [pow_add]; ring
      have : 2 ^ (k + 6) = 64 * 2 ^ k := by rw [pow_add]; ring
      omega
    omega
  have h3 : (3 : Real) ≤ Real.exp ((2 / alpha) ^ (2 ^ T)) :=
    ex_of_pw (pw_mono hX (pw_const hX (a := 1) (by norm_num)) (by omega))
  show max (max 3 (lemma156ExplicitThreshold k (alpha / 2) (alpha / 2)))
    (max (P.MThr alpha)
      (max (4 ^ (1 / P.NestExp alpha))
        (max (P.MReq alpha ^ (1 / P.MExp alpha))
          (max (6 ^ (1 / P.Eloc alpha)) (8 ^ (2 / P.F alpha)))))) ≤ _
  exact max_le (max_le h3 hL') (max_le hMT (max_le h4 (max_le hMR (max_le h6 h8))))

end GenParamsG

end LeanProofs.GowersSzemeredi
