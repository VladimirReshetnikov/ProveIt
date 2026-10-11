import GowersSzemeredi.Proofs18WidthPowerBounds

/-! The scale conditions of the length-six route.

`length_six_quartic_inverse` needs, at every large prime modulus `N`, the
conditions `SinglePieceModulusConditions`. This module proves them above
an explicit threshold `Tloc`, with an explicit exponent `e`.

The first step is the nested lift width
`nestW = W(C(C t₂))(W(C t₂)(W t₂ N))`. By `sixW_powerLB` and
`WidthPowerLB.comp` it is at least `N^(a₁a₂a₃)` above an explicit threshold
(`lsNestExp`, `lsNestThr`). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

section Nest

variable (Eb : Nat → Real → Real → Real → Real) (C : Real → Real) (alpha t : Real)

/-- The exponent of the three-fold nested width. -/
def lsNestExp : Real :=
  sixWExp Eb alpha t * sixWExp Eb alpha (C t) * sixWExp Eb alpha (C (C t))

/-- The threshold of the three-fold nested width. -/
def lsNestThr : Real :=
  max (max (sixWThr Eb alpha t) (sixWThr Eb alpha (C t) ^ (1 / sixWExp Eb alpha t)))
    (sixWThr Eb alpha (C (C t)) ^ (1 / (sixWExp Eb alpha t * sixWExp Eb alpha (C t))))

end Nest

theorem nestW_three_eq (C : Real → Real) (W : Real → Nat → Nat) (t : Real) (L : Nat) :
    nestW (fun _ => C) (fun _ => W) 3 t L = W (C (C t)) (W (C t) (W t L)) := rfl

theorem nestC_three_eq (C : Real → Real) (t : Real) :
    nestC (fun _ => C) 3 t = C (C (C t)) := rfl

/-- **The nested lift width is a power above an explicit threshold.** -/
theorem lsNest_powerLB {Eb : Nat → Real → Real → Real → Real} {C : Real → Real} {alpha t : Real}
    (hE : ∀ l g u s, 0 < s → s ≤ 1 → 0 < Eb l g u s ∧ Eb l g u s ≤ 1)
    (hC : ∀ u, 0 < u → u ≤ 1 → 0 < C u ∧ C u ≤ 1) (ht : 0 < t) (ht1 : t ≤ 1) :
    WidthPowerLB (fun L => nestW (fun _ => C) (fun _ => sixW Eb alpha) 3 t L)
      (lsNestExp Eb C alpha t) (lsNestThr Eb C alpha t) := by
  obtain ⟨hc1, hc1'⟩ := hC t ht ht1
  obtain ⟨hc2, hc2'⟩ := hC (C t) hc1 hc1'
  have h1 := sixW_powerLB (alpha := alpha) hE ht ht1
  have h2 := sixW_powerLB (alpha := alpha) hE hc1 hc1'
  have h3 := sixW_powerLB (alpha := alpha) hE hc2 hc2'
  have a1 := sixWExp_pos (alpha := alpha) hE ht ht1
  have a2 := sixWExp_pos (alpha := alpha) hE hc1 hc1'
  have a3 := sixWExp_pos (alpha := alpha) hE hc2 hc2'
  have h12 := WidthPowerLB.comp h1 h2 a1 a2.le (one_le_sixWThr Eb alpha t)
    (zero_le_one.trans (one_le_sixWThr Eb alpha (C t)))
  have h123 := WidthPowerLB.comp h12 h3 (mul_pos a1 a2) a3.le
    ((one_le_sixWThr Eb alpha t).trans (le_max_left _ _))
    (zero_le_one.trans (one_le_sixWThr Eb alpha (C (C t))))
  intro L hL
  have := h123 L hL
  simpa only [nestW_three_eq, lsNestExp] using this

theorem lsNestExp_pos {Eb : Nat → Real → Real → Real → Real} {C : Real → Real} {alpha t : Real}
    (hE : ∀ l g u s, 0 < s → s ≤ 1 → 0 < Eb l g u s ∧ Eb l g u s ≤ 1)
    (hC : ∀ u, 0 < u → u ≤ 1 → 0 < C u ∧ C u ≤ 1) (ht : 0 < t) (ht1 : t ≤ 1) :
    0 < lsNestExp Eb C alpha t := by
  obtain ⟨hc1, hc1'⟩ := hC t ht ht1
  obtain ⟨hc2, hc2'⟩ := hC (C t) hc1 hc1'
  unfold lsNestExp
  exact mul_pos (mul_pos (sixWExp_pos hE ht ht1) (sixWExp_pos hE hc1 hc1'))
    (sixWExp_pos hE hc2 hc2')

theorem lsNestExp_le_one {Eb : Nat → Real → Real → Real → Real} {C : Real → Real} {alpha t : Real}
    (hE : ∀ l g u s, 0 < s → s ≤ 1 → 0 < Eb l g u s ∧ Eb l g u s ≤ 1)
    (hC : ∀ u, 0 < u → u ≤ 1 → 0 < C u ∧ C u ≤ 1) (ht : 0 < t) (ht1 : t ≤ 1) :
    lsNestExp Eb C alpha t ≤ 1 := by
  obtain ⟨hc1, hc1'⟩ := hC t ht ht1
  obtain ⟨hc2, hc2'⟩ := hC (C t) hc1 hc1'
  have a1 := sixWExp_pos (alpha := alpha) hE ht ht1
  have a2 := sixWExp_pos (alpha := alpha) hE hc1 hc1'
  have a3 := sixWExp_pos (alpha := alpha) hE hc2 hc2'
  have b1 := sixWExp_le_one (alpha := alpha) hE ht ht1
  have b2 := sixWExp_le_one (alpha := alpha) hE hc1 hc1'
  have b3 := sixWExp_le_one (alpha := alpha) hE hc2 hc2'
  unfold lsNestExp
  have h12 : sixWExp Eb alpha t * sixWExp Eb alpha (C t) ≤ 1 :=
    (mul_le_mul b1 b2 a2.le zero_le_one).trans (by norm_num)
  exact (mul_le_mul h12 b3 a3.le zero_le_one).trans (by norm_num)

theorem one_le_lsNestThr (Eb : Nat → Real → Real → Real → Real) (C : Real → Real)
    (alpha t : Real) : 1 ≤ lsNestThr Eb C alpha t :=
  (one_le_sixWThr Eb alpha t).trans ((le_max_left _ _).trans (le_max_left _ _))


/-- `L ↦ coverWidth E t ⌈L/8⌉` is at least `L^(E/2)` above `64`. -/
theorem coverWidth_div8_powerLB (E : Real → Real) (t : Real)
    (hE : 0 < E (t / 2)) :
    WidthPowerLB (fun L => coverWidth E t ⌈(L : Real) / 8⌉₊) (E (t / 2) / 2) 64 := by
  intro L hL
  have hLpos : (0 : Real) < L := by linarith
  have hc := coverWidth_powerLB E t hE.le ⌈(L : Real) / 8⌉₊ (Nat.cast_nonneg _)
  have h8 : (L : Real) / 8 ≤ ⌈(L : Real) / 8⌉₊ := Nat.le_ceil _
  have hp : ((L : Real) / 8) ^ E (t / 2) ≤ (⌈(L : Real) / 8⌉₊ : Real) ^ E (t / 2) :=
    Real.rpow_le_rpow (by positivity) h8 hE.le
  refine le_trans ?_ (hp.trans hc)
  -- `L^(E/2) ≤ (L/8)^E` because `8 ≤ √L`
  have hsq : (8 : Real) ≤ (L : Real) ^ ((1 : Real) / 2) := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 64) hL (by norm_num : (0 : Real) ≤ 1 / 2)
    have h64 : (64 : Real) ^ ((1 : Real) / 2) = 8 := by
      rw [show (64 : Real) = 8 ^ (2 : Real) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [h64] at h
    exact h
  have hsplit : (L : Real) ^ E (t / 2) = (L : Real) ^ (E (t / 2) / 2) *
      ((L : Real) ^ ((1 : Real) / 2)) ^ E (t / 2) := by
    rw [← Real.rpow_mul hLpos.le, ← Real.rpow_add hLpos]
    congr 1
    ring
  rw [Real.div_rpow hLpos.le (by norm_num), hsplit]
  rw [le_div_iff₀ (by positivity)]
  have h8E : (8 : Real) ^ E (t / 2) ≤ ((L : Real) ^ ((1 : Real) / 2)) ^ E (t / 2) :=
    Real.rpow_le_rpow (by norm_num) hsq hE.le
  have hLE : 0 ≤ (L : Real) ^ (E (t / 2) / 2) := Real.rpow_nonneg hLpos.le _
  nlinarith

/-- The spectrum cell width is monotone in the exponent, for `m ≥ 1`. -/
theorem spectrumCellWidth_mono_exp {zeta : Real} (hz : 0 ≤ zeta) {m : Nat} (hm : 1 ≤ m)
    {e e' : Real} (hee' : e ≤ e') : spectrumCellWidth zeta m e ≤ spectrumCellWidth zeta m e' := by
  unfold spectrumCellWidth
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.sqrt_le_sqrt
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm) hee'

/-- The spectrum cell width as a power. -/
theorem spectrumCellWidth_eq {zeta : Real} {m : Nat} {e : Real} :
    spectrumCellWidth zeta m e = zeta / 2 * (m : Real) ^ (e / 2) := by
  unfold spectrumCellWidth
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg m)]
  ring_nf

/-! ### The parameters of the length-six route -/

section Params

variable (A Bq : Nat → Real) (K2 p2 : Nat) (alpha : Real)

def lsC : Real → Real := sixC sixQb alpha
def lsT2 : Real := globalTheta2 alpha (alpha / 2) 2
def lsRho1 : Real := lsC alpha (lsC alpha (lsC alpha (lsT2 alpha)))
def lsDelta : Real := section16Delta (section16ThetaOne alpha (alpha / 2) 2)
def lsBudget : Real := globalBudget alpha (alpha / 2) 2
/-- The exponent of the spectrum-scale cover. -/
def lsEm : Real := sixEb A Bq 2 (lsDelta alpha) (lsBudget alpha) (lsRho1 alpha / 2 / 2)
/-- The exponent of `m` in `N`. -/
def lsMExp : Real := lsNestExp (sixEb A Bq) (lsC alpha) alpha (lsT2 alpha) * (lsEm A Bq alpha / 2)
/-- The threshold for `m ≥ N^lsMExp`. -/
def lsMThr : Real :=
  max (lsNestThr (sixEb A Bq) (lsC alpha) alpha (lsT2 alpha))
    (64 ^ (1 / lsNestExp (sixEb A Bq) (lsC alpha) alpha (lsT2 alpha)))
/-- The worst spectrum count. -/
def lsQM : Nat := ⌊singlePieceGlobalQmax sixQb (lsC alpha) alpha (alpha / 2) 2⌋₊
/-- The exponent of `m` in the spectrum cell width. -/
def lsB : Real := familyRecExp 2 p2 (lsQM alpha) / 2
def lsZeta : Real := section16Zeta alpha (alpha / 2) 2
def lsRho : Real := spectrumPieceRho (fun t => t / 2) (lsRho1 alpha)
def lsThS : Real := singlePieceTheta (lsRho alpha) 1
def lsCS : Real := singlePieceGlobalC sixQb alpha (alpha / 2) 2 (lsThS alpha)
def lsEth : Real := sixEb A Bq 2 (alpha / 2) (lsBudget alpha) (lsThS alpha / 2)
def lsEc : Real := sixEb A Bq 2 (alpha / 2) (lsBudget alpha) (lsCS alpha / 2)
/-- The exponent of the final width in `N`. -/
def lsF : Real :=
  lsMExp A Bq alpha * (lsB p2 alpha * (lsEth A Bq alpha * lsEc A Bq alpha) / 2)
/-- The localization exponent. -/
def lsE : Real := lsF A Bq p2 alpha / 8
/-- How large `m` must be. -/
def lsMReq : Real :=
  max (familyRecThr 2 K2 p2 (lsQM alpha) : Real)
    (max ((8 / lsZeta alpha) ^ (1 / lsB p2 alpha))
      (max ((4 / (lsZeta alpha * lsRho alpha ^ 3)) ^ (1 / lsB p2 alpha))
        ((16 / lsZeta alpha) ^ (2 / lsB p2 alpha))))
/-- **The modulus threshold of the length-six route.** -/
def lsTloc : Real :=
  max (max 3 (lemma156ExplicitThreshold 2 (alpha / 2) (alpha / 2)))
    (max (lsMThr A Bq alpha)
      (max (4 ^ (1 / lsNestExp (sixEb A Bq) (lsC alpha) alpha (lsT2 alpha)))
        (max (lsMReq K2 p2 alpha ^ (1 / lsMExp A Bq alpha))
          (max (6 ^ (1 / lsE A Bq p2 alpha)) (8 ^ (2 / lsF A Bq p2 alpha))))))

end Params

theorem le_rpow_of_rpow_inv_le {T x a : Real} (ha : 0 < a) (hT : 0 ≤ T)
    (h : T ^ (1 / a) ≤ x) : T ≤ x ^ a := by
  have h1 := Real.rpow_le_rpow (Real.rpow_nonneg hT _) h ha.le
  rwa [← Real.rpow_mul hT, show 1 / a * a = 1 by field_simp, Real.rpow_one] at h1

/-- **The scale conditions of the length-six route hold above `lsTloc`.** -/
theorem ls_modulus_conditions {A Bq : Nat → Real} (hB : ∀ q, 0 < Bq q) {K2 p2 : Nat}
    (hK2 : 2 ≤ K2) (hp2 : 0 < p2) {alpha : Real} (ha : 0 < alpha) (haHalf : alpha ≤ 1 / 2)
    (N : Nat) [NeZero N] [Fact N.Prime] (hN : lsTloc A Bq K2 p2 alpha ≤ N) :
    SinglePieceModulusConditions sixQb (sixEb A Bq) (sixC sixQb alpha)
      (sixW (sixEb A Bq) alpha) alpha 2 (familyRecExp 2 p2) (familyRecThr 2 K2 p2)
      (lsE A Bq p2 alpha) N := by
  classical
  -- ranges of the controls
  have hE : ∀ l g u s, 0 < s → s ≤ 1 → 0 < sixEb A Bq l g u s ∧ sixEb A Bq l g u s ≤ 1 :=
    fun l g u s hs hs1 => ⟨sixEb_pos hB l g u s hs hs1, sixEb_le_one l g u s hs hs1⟩
  have hC := sixC_pos_le (fun l g t s _ _ => sixQb_ge_one l g t s) alpha
  have ha1 : alpha ≤ 1 := by linarith
  obtain ⟨hθ₂, hθ₂1⟩ := section16ThetaTwo_pos_le (gamma := alpha / 2) 2 ha ha1 (by positivity)
    (by linarith)
  have ht2 : 0 < lsT2 alpha := by unfold lsT2 globalTheta2; positivity
  have ht21 : lsT2 alpha ≤ 1 := by unfold lsT2 globalTheta2; linarith
  obtain ⟨hc1, hc1'⟩ := hC _ ht2 ht21
  obtain ⟨hc2, hc2'⟩ := hC _ hc1 hc1'
  obtain ⟨hr1, hr1'⟩ := hC _ hc2 hc2'
  have hρ1 : 0 < lsRho1 alpha := hr1
  have hρ1' : lsRho1 alpha ≤ 1 := hr1'
  have hρ : 0 < lsRho alpha := by unfold lsRho spectrumPieceRho; positivity
  have hρ' : lsRho alpha ≤ 1 := by
    unfold lsRho spectrumPieceRho
    have : lsRho1 alpha / 2 * (lsRho1 alpha / 2 / 2) ≤ 1 * 1 :=
      mul_le_mul (by linarith) (by linarith) (by positivity) zero_le_one
    linarith
  have hthS : 0 < lsThS alpha := by unfold lsThS singlePieceTheta; positivity
  have hthS' : lsThS alpha ≤ 1 := by
    unfold lsThS singlePieceTheta
    have h3 : lsRho alpha ^ 3 ≤ 1 := pow_le_one₀ hρ.le hρ'
    rw [div_le_one (by positivity)]
    norm_num
    linarith
  have hcS : 0 < lsCS alpha ∧ lsCS alpha ≤ 1 := by
    have hq := sixQb_ge_one 2 (alpha / 2) (globalBudget alpha (alpha / 2) 2) (lsThS alpha / 2)
    unfold lsCS singlePieceGlobalC
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by linarith)]
    linarith
  obtain ⟨hz, hzHalf⟩ := section16Zeta_pos_le_half 2 ha ha1 (by positivity : 0 < alpha / 2)
    (by linarith : alpha / 2 ≤ 1)
  have hζ : 0 < lsZeta alpha := hz
  have hb : 0 < lsB p2 alpha := by unfold lsB; exact div_pos (familyRecExp_pos 2 p2 _ hp2) two_pos
  obtain ⟨hEm, hEm'⟩ := hE 2 (lsDelta alpha) (lsBudget alpha) (lsRho1 alpha / 2 / 2)
    (by positivity) (by linarith)
  obtain ⟨hEth, hEth'⟩ := hE 2 (alpha / 2) (lsBudget alpha) (lsThS alpha / 2)
    (by positivity) (by linarith)
  obtain ⟨hEc, hEc'⟩ := hE 2 (alpha / 2) (lsBudget alpha) (lsCS alpha / 2)
    (by linarith [hcS.1]) (by linarith [hcS.2])
  have haN := lsNestExp_pos (alpha := alpha) hE hC ht2 ht21
  have haN' := lsNestExp_le_one (alpha := alpha) hE hC ht2 ht21
  have hmE : 0 < lsMExp A Bq alpha := by
    unfold lsMExp; exact mul_pos haN (div_pos (show 0 < lsEm A Bq alpha from hEm) two_pos)
  have hF : 0 < lsF A Bq p2 alpha := by
    unfold lsF lsEth lsEc at *
    exact mul_pos hmE (by positivity)
  have he : 0 < lsE A Bq p2 alpha := by unfold lsE; positivity
  -- the modulus is large
  have hNpos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hT : ∀ X : Real, X ≤ lsTloc A Bq K2 p2 alpha → X ≤ N := fun X hX => hX.trans hN
  have hN3 : (3 : Real) ≤ N := hT _ ((le_max_left _ _).trans (le_max_left _ _))
  have hN156 : lemma156ExplicitThreshold 2 (alpha / 2) (alpha / 2) ≤ N :=
    hT _ ((le_max_right _ _).trans (le_max_left _ _))
  have hNM : lsMThr A Bq alpha ≤ N :=
    hT _ ((le_max_left _ _).trans (le_max_right _ _))
  have hN4 : (4 : Real) ^ (1 / lsNestExp (sixEb A Bq) (lsC alpha) alpha (lsT2 alpha)) ≤ N :=
    hT _ ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hNR : lsMReq K2 p2 alpha ^ (1 / lsMExp A Bq alpha) ≤ N :=
    hT _ ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      (le_max_right _ _))))
  have hN6 : (6 : Real) ^ (1 / lsE A Bq p2 alpha) ≤ N :=
    hT _ ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))))
  have hN8 : (8 : Real) ^ (2 / lsF A Bq p2 alpha) ≤ N :=
    hT _ ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))))
  have hprime : N.Prime := Fact.out
  have hodd : Odd N := hprime.odd_of_ne_two (by
    intro h2; rw [h2] at hN3; norm_num at hN3)
  -- the nested width and `m`
  obtain ⟨NW, hNW⟩ : ∃ NW : Nat, nestW (fun _ => sixC sixQb alpha)
      (fun _ => sixW (sixEb A Bq) alpha) (2 ^ 2 - 1) (globalTheta2 alpha (alpha / 2) 2) N = NW :=
    ⟨_, rfl⟩
  have hNW3 : nestW (fun _ => sixC sixQb alpha) (fun _ => sixW (sixEb A Bq) alpha) 3
      (lsT2 alpha) N = NW := hNW
  have hnest := lsNest_powerLB (alpha := alpha) hE hC ht2 ht21
  have hNWpow : (N : Real) ^ lsNestExp (sixEb A Bq) (lsC alpha) alpha (lsT2 alpha) ≤ NW := by
    have h : (N : Real) ^ lsNestExp (sixEb A Bq) (lsC alpha) alpha (lsT2 alpha) ≤
        ((nestW (fun _ => sixC sixQb alpha) (fun _ => sixW (sixEb A Bq) alpha) 3
          (lsT2 alpha) N : Nat) : Real) := hnest N (hNM.trans' (le_max_left _ _))
    rw [hNW3] at h
    exact h
  have hNW4 : (4 : Real) ≤ NW :=
    (le_rpow_of_rpow_inv_le haN (by norm_num) hN4).trans hNWpow
  obtain ⟨m, hm⟩ : ∃ m : Nat, coverWidth (sixEb A Bq 2 (lsDelta alpha) (lsBudget alpha))
      (singlePieceGlobalRho1 (sixC sixQb alpha) alpha (alpha / 2) 2 / 2)
      ⌈(NW : Real) / 8⌉₊ = m := ⟨_, rfl⟩
  have hmpow : (N : Real) ^ lsMExp A Bq alpha ≤ m := by
    have hcov := coverWidth_div8_powerLB (sixEb A Bq 2 (lsDelta alpha) (lsBudget alpha))
      (lsRho1 alpha / 2) hEm
    have hcomp := WidthPowerLB.comp hnest hcov haN (by positivity)
      (one_le_lsNestThr _ _ _ _) (by norm_num)
    have h := hcomp N hNM
    have hm' : coverWidth (sixEb A Bq 2 (lsDelta alpha) (lsBudget alpha)) (lsRho1 alpha / 2)
        ⌈((nestW (fun _ => sixC sixQb alpha) (fun _ => sixW (sixEb A Bq) alpha) 3
          (lsT2 alpha) N : Nat) : Real) / 8⌉₊ = m := by
      rw [hNW3]; exact hm
    have h' : (N : Real) ^ lsMExp A Bq alpha ≤
        (coverWidth (sixEb A Bq 2 (lsDelta alpha) (lsBudget alpha)) (lsRho1 alpha / 2)
          ⌈((nestW (fun _ => sixC sixQb alpha) (fun _ => sixW (sixEb A Bq) alpha) 3
            (lsT2 alpha) N : Nat) : Real) / 8⌉₊ : Real) := h
    rw [hm'] at h'
    exact h'
  have hm1 : (1 : Real) ≤ m :=
    (Real.one_le_rpow (by linarith) hmE.le).trans hmpow
  have hmReq : lsMReq K2 p2 alpha ≤ m :=
    (le_rpow_of_rpow_inv_le hmE ((Nat.cast_nonneg _).trans (le_max_left _ _)) hNR).trans hmpow
  have hmb8 : 8 / lsZeta alpha ≤ (m : Real) ^ lsB p2 alpha :=
    le_rpow_of_rpow_inv_le hb (by positivity)
      (((le_max_left _ _).trans (le_max_right _ _)).trans hmReq)
  have hmbρ : 4 / (lsZeta alpha * lsRho alpha ^ 3) ≤ (m : Real) ^ lsB p2 alpha :=
    le_rpow_of_rpow_inv_le hb (by positivity)
      (((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hmReq)
  have hmb16 : 16 / lsZeta alpha ≤ (m : Real) ^ (lsB p2 alpha / 2) := by
    have h := ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hmReq
    apply le_rpow_of_rpow_inv_le (by positivity) (by positivity)
    simpa only [one_div_div] using h
  have hthr : (familyRecThr 2 K2 p2 (lsQM alpha) : Real) ≤ m := (le_max_left _ _).trans hmReq
  -- the final exponent
  have hρ1eq : singlePieceGlobalRho1 (sixC sixQb alpha) alpha (alpha / 2) 2 = lsRho1 alpha := rfl
  have hthSeq : singlePieceTheta (spectrumPieceRho (fun t => t / 2) (lsRho1 alpha)) 1 =
      lsThS alpha := rfl
  have hcSeq : singlePieceGlobalC sixQb alpha (alpha / 2) 2 (lsThS alpha) = lsCS alpha := rfl
  have hBudeq : globalBudget alpha (alpha / 2) 2 = lsBudget alpha := rfl
  have hZeq : section16Zeta alpha (alpha / 2) 2 = lsZeta alpha := rfl
  have hQeq : singlePieceGlobalQmax sixQb (sixC sixQb alpha) alpha (alpha / 2) 2 =
      singlePieceGlobalQmax sixQb (lsC alpha) alpha (alpha / 2) 2 := rfl
  have hFin : ∀ q : Nat, (q : Real) ≤ singlePieceGlobalQmax sixQb (lsC alpha) alpha (alpha / 2) 2 →
      (N : Real) ^ lsF A Bq p2 alpha ≤
        coverWidth (sixEb A Bq 2 (alpha / 2) (lsBudget alpha)) (lsCS alpha)
          (coverWidth (sixEb A Bq 2 (alpha / 2) (lsBudget alpha)) (lsThS alpha)
            ⌈spectrumCellWidth (lsZeta alpha) m (familyRecExp 2 p2 q) / 8⌉₊) ∧
      2 * lsB p2 alpha ≤ familyRecExp 2 p2 q := by
    intro q hq
    have hqM : q ≤ lsQM alpha := Nat.le_floor hq
    have heps : 2 * lsB p2 alpha ≤ familyRecExp 2 p2 q := by
      unfold lsB
      have := familyRecExp_antitone (k := 2) hp2 hqM
      linarith
    refine ⟨?_, heps⟩
    have hm0 : 0 ≤ (m : Real) ^ (lsB p2 alpha / 2) := Real.rpow_nonneg (by linarith) _
    have hSCW : (m : Real) ^ (lsB p2 alpha / 2) ≤
        spectrumCellWidth (lsZeta alpha) m (familyRecExp 2 p2 q) / 8 := by
      have hmono := spectrumCellWidth_mono_exp hζ.le (by exact_mod_cast hm1) heps
      rw [spectrumCellWidth_eq] at hmono
      have hpow : (m : Real) ^ (2 * lsB p2 alpha / 2) =
          (m : Real) ^ (lsB p2 alpha / 2) * (m : Real) ^ (lsB p2 alpha / 2) := by
        rw [← Real.rpow_add (by linarith)]; ring_nf
      rw [hpow] at hmono
      have hk : 16 ≤ lsZeta alpha * (m : Real) ^ (lsB p2 alpha / 2) := by
        have := mul_le_mul_of_nonneg_left hmb16 hζ.le
        have h16 : lsZeta alpha * (16 / lsZeta alpha) = 16 := by field_simp
        linarith
      have hprod := mul_le_mul_of_nonneg_left hk hm0
      have hxx : (m : Real) ^ (lsB p2 alpha / 2) *
          (lsZeta alpha * (m : Real) ^ (lsB p2 alpha / 2)) =
          lsZeta alpha / 2 *
            ((m : Real) ^ (lsB p2 alpha / 2) * (m : Real) ^ (lsB p2 alpha / 2)) * 2 := by ring
      rw [hxx] at hprod
      linarith
    obtain ⟨L, hLdef⟩ : ∃ L : Nat,
        ⌈spectrumCellWidth (lsZeta alpha) m (familyRecExp 2 p2 q) / 8⌉₊ = L := ⟨_, rfl⟩
    rw [hLdef]
    have hLge : (m : Real) ^ (lsB p2 alpha / 2) ≤ L := by
      rw [← hLdef]; exact hSCW.trans (Nat.le_ceil _)
    have hin := coverWidth_powerLB (sixEb A Bq 2 (alpha / 2) (lsBudget alpha)) (lsThS alpha)
      hEth.le L (by positivity)
    obtain ⟨X, hXdef⟩ : ∃ X : Nat,
        coverWidth (sixEb A Bq 2 (alpha / 2) (lsBudget alpha)) (lsThS alpha) L = X := ⟨_, rfl⟩
    rw [hXdef] at hin
    rw [hXdef]
    have hout := coverWidth_powerLB (sixEb A Bq 2 (alpha / 2) (lsBudget alpha)) (lsCS alpha)
      hEc.le X (by positivity)
    refine le_trans ?_ hout
    have hstep1 : ((m : Real) ^ (lsB p2 alpha / 2)) ^ lsEth A Bq alpha ≤
        (L : Real) ^ lsEth A Bq alpha :=
      Real.rpow_le_rpow hm0 hLge hEth.le
    have hstep2 : (((m : Real) ^ (lsB p2 alpha / 2)) ^ lsEth A Bq alpha) ^ lsEc A Bq alpha ≤
        (X : Real) ^ lsEc A Bq alpha :=
      Real.rpow_le_rpow (Real.rpow_nonneg hm0 _) (hstep1.trans hin) hEc.le
    refine le_trans ?_ hstep2
    have hNm : ((N : Real) ^ lsMExp A Bq alpha) ^
        (lsB p2 alpha / 2 * lsEth A Bq alpha * lsEc A Bq alpha) ≤
        (m : Real) ^ (lsB p2 alpha / 2 * lsEth A Bq alpha * lsEc A Bq alpha) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hNpos.le _) hmpow
        (mul_nonneg (mul_nonneg (by positivity) hEth.le) hEc.le)
    rw [← Real.rpow_mul (by linarith), ← Real.rpow_mul (by linarith)]
    rw [← Real.rpow_mul hNpos.le] at hNm
    have hexp1 : lsF A Bq p2 alpha =
        lsMExp A Bq alpha * (lsB p2 alpha / 2 * (lsEth A Bq alpha * lsEc A Bq alpha)) := by
      unfold lsF; ring
    have e3 : lsB p2 alpha / 2 * lsEth A Bq alpha * lsEc A Bq alpha =
        lsB p2 alpha / 2 * (lsEth A Bq alpha * lsEc A Bq alpha) := by ring
    rw [e3] at hNm
    rw [hexp1]
    exact hNm
  unfold SinglePieceModulusConditions SinglePieceGlobalScale singlePieceGlobalWidth
  simp only [hρ1eq, hthSeq, hcSeq, hBudeq, hZeq, hQeq]
  refine ⟨hodd, hN156, ?_, m, ⟨by rw [hNW]; exact_mod_cast hNW4, by exact_mod_cast hm1,
    by rw [hNW]; exact le_of_eq hm.symm, ?_⟩, ?_⟩
  · -- `4 ≤ N^e`
    have h6 := le_rpow_of_rpow_inv_le he (by norm_num) hN6
    linarith
  · intro q hq
    obtain ⟨hFq, heps⟩ := hFin q hq
    have hqM : q ≤ lsQM alpha := Nat.le_floor hq
    have hthrq : (familyRecThr 2 K2 p2 q : Real) ≤ familyRecThr 2 K2 p2 (lsQM alpha) :=
      Nat.cast_le.mpr (familyRecThr_mono (by omega) hqM)
    have hSCWq := spectrumCellWidth_mono_exp hζ.le (by exact_mod_cast hm1) heps
    rw [spectrumCellWidth_eq] at hSCWq
    rw [show 2 * lsB p2 alpha / 2 = lsB p2 alpha by ring] at hSCWq
    refine ⟨Nat.cast_le.mp (hthrq.trans hthr), ?_, ?_, ?_⟩
    · have := mul_le_mul_of_nonneg_left hmb8 (by positivity : (0 : Real) ≤ lsZeta alpha / 2)
      have h4 : lsZeta alpha / 2 * (8 / lsZeta alpha) = 4 := by field_simp; ring
      linarith
    · have := mul_le_mul_of_nonneg_left hmbρ (by positivity : (0 : Real) ≤ lsZeta alpha / 2)
      have h2 : lsZeta alpha / 2 * (4 / (lsZeta alpha * lsRho alpha ^ 3)) = 2 / lsRho alpha ^ 3 := by
        field_simp; ring
      have hρ3 : 0 < lsRho alpha ^ 3 := by positivity
      have hge : 2 / lsRho alpha ^ 3 ≤
          spectrumCellWidth (lsZeta alpha) m (familyRecExp 2 p2 q) := by linarith
      have := mul_le_mul_of_nonneg_left hge hρ3.le
      rw [mul_div_cancel₀ _ hρ3.ne'] at this
      exact this
    · have hN8' : (8 : Real) ^ (1 / (lsF A Bq p2 alpha / 2)) ≤ N := by
        rw [show 1 / (lsF A Bq p2 alpha / 2) = 2 / lsF A Bq p2 alpha by field_simp]
        exact hN8
      have h8 := le_rpow_of_rpow_inv_le (by positivity : 0 < lsF A Bq p2 alpha / 2)
        (by norm_num) hN8'
      have hNF : (8 : Real) ≤ (N : Real) ^ lsF A Bq p2 alpha := by
        have h1 : (1 : Real) ≤ (N : Real) ^ (lsF A Bq p2 alpha / 2) :=
          Real.one_le_rpow (by linarith) (by positivity)
        have hsplit : (N : Real) ^ lsF A Bq p2 alpha =
            (N : Real) ^ (lsF A Bq p2 alpha / 2) * (N : Real) ^ (lsF A Bq p2 alpha / 2) := by
          rw [← Real.rpow_add hNpos]; ring_nf
        rw [hsplit]
        exact h8.trans (le_mul_of_one_le_right (by linarith) h1)
      have h2 := hNF.trans hFq
      exact (Nat.cast_le (α := Real)).mp (by rw [Nat.cast_ofNat]; linarith)
  · intro q hq
    obtain ⟨hFq, -⟩ := hFin q hq
    have h6 := le_rpow_of_rpow_inv_le he (by norm_num) hN6
    have hN8' : (8 : Real) ^ (1 / (lsF A Bq p2 alpha / 2)) ≤ N := by
      rw [show 1 / (lsF A Bq p2 alpha / 2) = 2 / lsF A Bq p2 alpha by field_simp]
      exact hN8
    have h8 := le_rpow_of_rpow_inv_le (by positivity : 0 < lsF A Bq p2 alpha / 2)
      (by norm_num) hN8'
    have hx4 : ((N : Real) ^ lsE A Bq p2 alpha) ^ 4 / 8 ≤ (N : Real) ^ lsF A Bq p2 alpha := by
      have hpow4 : ((N : Real) ^ lsE A Bq p2 alpha) ^ 4 = (N : Real) ^ (lsF A Bq p2 alpha / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; unfold lsE; push_cast; ring_nf
      rw [hpow4]
      have hsplit : (N : Real) ^ lsF A Bq p2 alpha =
          (N : Real) ^ (lsF A Bq p2 alpha / 2) * (N : Real) ^ (lsF A Bq p2 alpha / 2) := by
        rw [← Real.rpow_add hNpos]; ring_nf
      have h0 : 0 ≤ (N : Real) ^ (lsF A Bq p2 alpha / 2) := Real.rpow_nonneg hNpos.le _
      rw [hsplit]
      have hx8 : (N : Real) ^ (lsF A Bq p2 alpha / 2) / 8 ≤ (N : Real) ^ (lsF A Bq p2 alpha / 2) := by
        linarith
      exact hx8.trans (le_mul_of_one_le_right h0 (by linarith))
    exact nat_sqrt_pred_pred_ge h6 (hx4.trans hFq)


theorem familyRecExp_le_one (k p q : Nat) (hp : 0 < p) : familyRecExp k p q ≤ 1 := by
  unfold familyRecExp
  apply inv_le_one_of_one_le₀
  have : 1 ≤ 2 * (p * (q + 1) ^ (2 * 2 ^ (k + 1))) := by
    have h1 : 1 ≤ (q + 1) ^ (2 * 2 ^ (k + 1)) := Nat.one_le_pow _ _ (by omega)
    have h2 : 1 ≤ p * (q + 1) ^ (2 * 2 ^ (k + 1)) := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (by omega))
    omega
  exact_mod_cast this

/-- The localization exponent lies in `(0, 1/2]`. -/
theorem lsE_pos_le {A Bq : Nat → Real} (hB : ∀ q, 0 < Bq q) {p2 : Nat} (hp2 : 0 < p2)
    {alpha : Real} (ha : 0 < alpha) (haHalf : alpha ≤ 1 / 2) :
    0 < lsE A Bq p2 alpha ∧ lsE A Bq p2 alpha ≤ 1 / 2 := by
  have hE : ∀ l g u s, 0 < s → s ≤ 1 → 0 < sixEb A Bq l g u s ∧ sixEb A Bq l g u s ≤ 1 :=
    fun l g u s hs hs1 => ⟨sixEb_pos hB l g u s hs hs1, sixEb_le_one l g u s hs hs1⟩
  have hC := sixC_pos_le (fun l g t s _ _ => sixQb_ge_one l g t s) alpha
  have ha1 : alpha ≤ 1 := by linarith
  obtain ⟨hθ₂, hθ₂1⟩ := section16ThetaTwo_pos_le (gamma := alpha / 2) 2 ha ha1 (by positivity)
    (by linarith)
  have ht2 : 0 < lsT2 alpha := by unfold lsT2 globalTheta2; positivity
  have ht21 : lsT2 alpha ≤ 1 := by unfold lsT2 globalTheta2; linarith
  obtain ⟨hc1, hc1'⟩ := hC _ ht2 ht21
  obtain ⟨hc2, hc2'⟩ := hC _ hc1 hc1'
  obtain ⟨hr1, hr1'⟩ := hC _ hc2 hc2'
  have hρ1 : 0 < lsRho1 alpha := hr1
  have hρ1' : lsRho1 alpha ≤ 1 := hr1'
  have hρ : 0 < lsRho alpha := by unfold lsRho spectrumPieceRho; positivity
  have hρ' : lsRho alpha ≤ 1 := by
    unfold lsRho spectrumPieceRho
    have : lsRho1 alpha / 2 * (lsRho1 alpha / 2 / 2) ≤ 1 * 1 :=
      mul_le_mul (by linarith) (by linarith) (by positivity) zero_le_one
    linarith
  have hthS : 0 < lsThS alpha := by unfold lsThS singlePieceTheta; positivity
  have hthS' : lsThS alpha ≤ 1 := by
    unfold lsThS singlePieceTheta
    have h3 : lsRho alpha ^ 3 ≤ 1 := pow_le_one₀ hρ.le hρ'
    rw [div_le_one (by positivity)]
    norm_num
    linarith
  have hcS : 0 < lsCS alpha ∧ lsCS alpha ≤ 1 := by
    have hq := sixQb_ge_one 2 (alpha / 2) (globalBudget alpha (alpha / 2) 2) (lsThS alpha / 2)
    unfold lsCS singlePieceGlobalC
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by linarith)]
    linarith
  obtain ⟨hEm, hEm'⟩ := hE 2 (lsDelta alpha) (lsBudget alpha) (lsRho1 alpha / 2 / 2)
    (by positivity) (by linarith)
  obtain ⟨hEth, hEth'⟩ := hE 2 (alpha / 2) (lsBudget alpha) (lsThS alpha / 2)
    (by positivity) (by linarith)
  obtain ⟨hEc, hEc'⟩ := hE 2 (alpha / 2) (lsBudget alpha) (lsCS alpha / 2)
    (by linarith [hcS.1]) (by linarith [hcS.2])
  have haN := lsNestExp_pos (alpha := alpha) hE hC ht2 ht21
  have haN' := lsNestExp_le_one (alpha := alpha) hE hC ht2 ht21
  have hb := familyRecExp_pos 2 p2 (lsQM alpha) hp2
  have hb' := familyRecExp_le_one 2 p2 (lsQM alpha) hp2
  have hm : 0 < lsMExp A Bq alpha ∧ lsMExp A Bq alpha ≤ 1 := by
    have hEm2 : 0 < lsEm A Bq alpha := hEm
    have hEm2' : lsEm A Bq alpha ≤ 1 := hEm'
    unfold lsMExp
    refine ⟨mul_pos haN (by positivity), ?_⟩
    calc lsNestExp (sixEb A Bq) (lsC alpha) alpha (lsT2 alpha) * (lsEm A Bq alpha / 2)
        ≤ 1 * 1 := mul_le_mul haN' (by linarith) (by positivity) zero_le_one
      _ = 1 := one_mul 1
  have hBpos : 0 < lsB p2 alpha := by unfold lsB; positivity
  have hBle : lsB p2 alpha ≤ 1 := by unfold lsB; linarith
  have hEthEc : 0 < lsEth A Bq alpha * lsEc A Bq alpha ∧
      lsEth A Bq alpha * lsEc A Bq alpha ≤ 1 := by
    have h1 : 0 < lsEth A Bq alpha := hEth
    have h2 : 0 < lsEc A Bq alpha := hEc
    refine ⟨mul_pos h1 h2, ?_⟩
    calc lsEth A Bq alpha * lsEc A Bq alpha ≤ 1 * 1 :=
          mul_le_mul hEth' hEc' h2.le zero_le_one
      _ = 1 := one_mul 1
  have hinner : 0 < lsB p2 alpha * (lsEth A Bq alpha * lsEc A Bq alpha) / 2 ∧
      lsB p2 alpha * (lsEth A Bq alpha * lsEc A Bq alpha) / 2 ≤ 1 := by
    refine ⟨by have := hEthEc.1; positivity, ?_⟩
    have : lsB p2 alpha * (lsEth A Bq alpha * lsEc A Bq alpha) ≤ 1 * 1 :=
      mul_le_mul hBle hEthEc.2 hEthEc.1.le zero_le_one
    linarith
  have hF : 0 < lsF A Bq p2 alpha ∧ lsF A Bq p2 alpha ≤ 1 := by
    unfold lsF
    refine ⟨mul_pos hm.1 hinner.1, ?_⟩
    calc lsMExp A Bq alpha * (lsB p2 alpha * (lsEth A Bq alpha * lsEc A Bq alpha) / 2)
        ≤ 1 * 1 := mul_le_mul hm.2 hinner.2 hinner.1.le zero_le_one
      _ = 1 := one_mul 1
  unfold lsE
  exact ⟨by linarith [hF.1], by linarith [hF.2]⟩

/-- **The degree-four discrepancy bound of the length-six route**, from the
two recurrence profiles alone. -/
theorem length_six_function_discrepancy {K1 p1 K2 p2 : Nat} (hK1 : 2 ≤ K1) (hp1 : 0 < p1)
    (hrec1 : Section16RecurrenceProfileWith 1 (familyRecThr 1 K1 p1) (familyRecExp 1 p1))
    (hK2 : 2 ≤ K2) (hp2 : 0 < p2)
    (hrec2 : Section16RecurrenceProfileWith 2 (familyRecThr 2 K2 p2) (familyRecExp 2 p2))
    {alpha : Real} (ha : 0 < alpha) (haHalf : alpha ≤ 1 / 2) :
    FunctionDiscrepancyBound 4 alpha
      (singlePieceEta sixQb (sixC sixQb alpha) alpha 2 *
        fejerCubicDiscrepancyParameter (singlePieceCubicInput sixQb (sixC sixQb alpha) alpha) / 4)
      (inverseStepExponent (2 + 1) (lsE (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) p2 alpha)
        (min (fejerCubicDiscrepancyExponent (singlePieceCubicInput sixQb (sixC sixQb alpha) alpha)) 16))
      (max (shortLocalizationThreshold (2 + 1)
          (lsE (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) p2 alpha) (6 * ((2 + 1 : Nat) : Real))
          (fejerCubicInverseThreshold (singlePieceCubicInput sixQb (sixC sixQb alpha) alpha))
          (lsTloc (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) K2 p2 alpha))
        (inverseStepThreshold (2 + 1) (singlePieceEta sixQb (sixC sixQb alpha) alpha 2)
          (fejerCubicDiscrepancyParameter (singlePieceCubicInput sixQb (sixC sixQb alpha) alpha))
          (lsE (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) p2 alpha)
          (6 * ((2 + 1 : Nat) : Real))
          (min (fejerCubicDiscrepancyExponent (singlePieceCubicInput sixQb (sixC sixQb alpha) alpha)) 16))) := by
  have hB : ∀ q, 0 < familyWidthDivisor 1 p1 q := familyWidthDivisor_pos hp1
  obtain ⟨he0, he⟩ := lsE_pos_le (A := familyWidthPrefactor K1) hB hp2 ha haHalf
  exact length_six_quartic_inverse hK1 hp1 hrec1 hK2 hrec2 ha haHalf he0 he
    (fun N _ _ hN => ls_modulus_conditions hB hK2 hp2 ha haHalf N hN)
end LeanProofs.GowersSzemeredi
