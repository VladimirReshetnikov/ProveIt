import GowersSzemeredi.Proofs16IntegerClassTwo
import GowersSzemeredi.Proofs16AllDimensions

/-! Actual uniform classes carry integer cover certificates in every
positive dimension above one, with the same degree and threshold bounds. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem PowerUniformClass.integerCover_weaken {k : Nat} {V : Real} {dC dE dT : Nat}
    (C : PowerUniformClass k V dC dE dT) (hInt : C.IntegerCover) (hV : 1 ≤ V)
    {V' : Real} (hVV : V ≤ V') {dC' dE' dT' : Nat}
    (hC : dC ≤ dC') (hE : dE ≤ dE') (hT : dT ≤ dT') :
    (C.weaken hV hVV hC hE hT).IntegerCover := by
    intro theta gamma ht ht1 hg hg1 N _ _ n Gamma hU
    refine (hInt theta gamma ht ht1 hg hg1 N n Gamma hU).weaken ?_ ?_ ?_
    · intro rho hr hr1
      have h2 := uniformBase_two_le hV n ht ht1 hg hg1 hr hr1
      have hmono := uniformBase_mono_V hVV n ht hg hr.le
      calc uniformBase V n theta gamma rho ^ dC ≤ uniformBase V n theta gamma rho ^ dC' :=
            pow_le_pow_right₀ (by linarith) hC
        _ ≤ uniformBase V' n theta gamma rho ^ dC' := pow_le_pow_left₀ (by linarith) hmono _
    · intro rho hr hr1
      have h2 := uniformBase_two_le (hV.trans hVV) n ht ht1 hg hg1 hr hr1
      positivity
    · intro rho hr hr1
      have h2 := uniformBase_two_le hV n ht ht1 hg hg1 hr hr1
      have hmono := uniformBase_mono_V hVV n ht hg hr.le
      refine inv_anti₀ (pow_pos (by linarith) _) ?_
      calc uniformBase V n theta gamma rho ^ dE ≤ uniformBase V n theta gamma rho ^ dE' :=
            pow_le_pow_right₀ (by linarith) hE
        _ ≤ uniformBase V' n theta gamma rho ^ dE' := pow_le_pow_left₀ (by linarith) hmono _

theorem powerUniformClass_all_integer (Kc pc : Nat → Nat) (hK : ∀ k, 1 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))))
    (hIntegerLemma : ∀ k, 1 ≤ k → IntegerAbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k)))) :
    ∀ k, 2 ≤ k →
      ∃ C : PowerUniformClass k (classV Kc pc k) (classDeg k) (classDeg k) (classDeg k), C.IntegerCover := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    have hV1 := one_le_classV Kc pc 2
    have hc1 := const_le_classV_succ Kc pc 1
    have hmono := classV_le_succ Kc pc 1
    obtain ⟨C, hC⟩ := powerUniformClass_two_integer (hK 1) (hp 1) (hlem 1 le_rfl) (hIntegerLemma 1 le_rfl) hV1
      (hc1.1.trans le_rfl) (hc1.2.trans le_rfl)
    have hdeg : ∀ d : Nat, d ≤ 2 ^ 130 → d ≤ classDeg 2 := by
      intro d hd
      refine hd.trans ?_
      unfold classDeg
      exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
    exact ⟨C.weaken hV1 le_rfl (hdeg _ (by norm_num)) (hdeg _ le_rfl) (hdeg _ (by norm_num)),
      C.integerCover_weaken hC hV1 le_rfl (hdeg _ (by norm_num)) (hdeg _ le_rfl) (hdeg _ (by norm_num))⟩
  | succ k hk ih =>
    obtain ⟨C, hC⟩ := ih
    have hV1 := one_le_classV Kc pc k
    have hc := const_le_classV_succ Kc pc k
    obtain ⟨C', hC'⟩ := powerUniformClass_succ_integer (by omega) hV1 (classDeg_pos k) C hC (hK k) (hp k)
      (hlem k (by omega)) (hIntegerLemma k (by omega)) (classV_le_succ Kc pc k) hc.1 hc.2
    have hsum := (step_degrees_le (k := k) (classDeg_pos k)).trans (step_degree_closed k)
    exact ⟨C'.weaken (one_le_classV Kc pc (k + 1)) le_rfl (by omega) (by omega) (by omega),
      C'.integerCover_weaken hC' (one_le_classV Kc pc (k + 1)) le_rfl (by omega) (by omega) (by omega)⟩

theorem PowerUniformClass.integerPolyCoverAt {k : Nat} {V : Real} {dC dE dT : Nat}
    (C : PowerUniformClass k V dC dE dT) (hInt : C.IntegerCover) (hk : 0 < k) (hV : 1 ≤ V) {D : Nat} (hDC : dC ≤ D)
    (hDE : dE ≤ D) (hDT : dT + k + 1 ≤ D) :
    IntegerPolyCoverAt k (fun gamma theta rho => uniformBase V 1 theta gamma rho ^ D)
      (fun gamma theta rho => (uniformBase V 1 theta gamma rho ^ D)⁻¹) := by
  intro N _ _ gamma theta hg hg1 ht ht1 Gamma hsize hprod
  classical
  have hfacts := fun rho (hr : 0 < rho) (hr1 : rho ≤ 1) =>
    uniformBase_facts hV 1 hg hg1 ht ht1 hr hr1
  by_cases hN : (V * (2 / (gamma * theta))) ^ dT ≤ (N : Real)
  · obtain ⟨J, hJ, hU⟩ := C.decomp theta gamma ht ht1 hg hg1 N hN Gamma hsize hprod
    refine ⟨J, hJ, ?_⟩
    have hcov := hInt theta gamma ht ht1 hg hg1 N 1 (fun _ => restrictRelation Gamma J)
      (fun _ => hU)
    refine (hcov.mono ?_).weaken ?_ ?_ ?_
    · intro z hz
      exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ _, hz⟩
    · intro rho hr hr1
      exact pow_le_pow_right₀ (le_trans (by norm_num) (hfacts rho hr hr1).2.2.2.2) hDC
    · intro rho hr _
      have := (hfacts rho hr (by assumption)).2.2.2.2
      positivity
    · intro rho hr hr1
      have hw2 := (hfacts rho hr hr1).2.2.2.2
      exact inv_anti₀ (pow_pos (by linarith) _)
        (pow_le_pow_right₀ (by linarith) hDE)
  · have hNlt : (N : Real) < (V * (2 / (gamma * theta))) ^ dT := lt_of_not_ge hN
    set T := (V * (2 / (gamma * theta))) ^ dT with hT
    obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
    have hVu2 : 2 ≤ V * (2 / (gamma * theta)) := by nlinarith
    have hT1 : 1 ≤ T := one_le_pow₀ (by linarith)
    refine ⟨Finset.univ, ?_, ?_⟩
    · have hc : ((Finset.univ : Finset (Point N k)).card : Real) = (N : Real) ^ k := by
        simp [Point, ZMod.card]
      rw [hc]
      have : (0 : Real) ≤ (N : Real) ^ k := by positivity
      nlinarith
    have hfib : ∀ x : Point N k,
        ((restrictRelation Gamma Finset.univ).filter fun z => z.1 = x).card ≤ ⌈T⌉₊ := by
      intro x
      have h1 : ((restrictRelation Gamma Finset.univ).filter fun z => z.1 = x).card ≤ N := by
        refine (Finset.card_le_card_of_injOn (fun z => z.2) (fun _ _ => Finset.mem_univ _)
          ?_).trans (by simp [ZMod.card])
        intro z hz z' hz' h
        exact Prod.ext ((Finset.mem_filter.mp hz).2.trans (Finset.mem_filter.mp hz').2.symm) h
      refine h1.trans ?_
      have : (N : Real) ≤ ⌈T⌉₊ := hNlt.le.trans (Nat.le_ceil _)
      exact_mod_cast this
    have hcov := integerMultiplyLinearWith_of_large_box_covers hk
      (Gamma := restrictRelation Gamma Finset.univ) ⌈T⌉₊ hfib
      (fun rho => uniformBase V 1 theta gamma rho ^ D)
      (fun rho => (uniformBase V 1 theta gamma rho ^ D)⁻¹) (fun _ => T)
      (fun s hs hs1 => by have := (hfacts s hs hs1).2.2.2.2; positivity) (by
        intro s _ _ P hP hlarge
        exfalso
        have hw : (P.width : Real) ≤ N := by exact_mod_cast P.width_le_modulus hP.isProper
        linarith)
    refine hcov.weaken ?_ ?_ ?_
    · intro rho hr hr1
      obtain ⟨-, -, -, hVw, hw2⟩ := hfacts rho hr hr1
      set w := uniformBase V 1 theta gamma rho
      have hw1 : 1 ≤ w := by linarith
      refine max_le le_rfl ?_
      -- `3^k ⌈T⌉ ≤ w^k · w^(dT+1)`
      have hTw : T ≤ w ^ dT := pow_le_pow_left₀ (by linarith) hVw dT
      have hceil : ((⌈T⌉₊ : Nat) : Real) ≤ w ^ (dT + 1) := by
        have h := Nat.ceil_lt_add_one (show 0 ≤ T by linarith)
        rw [pow_succ]
        have : T + 1 ≤ w ^ dT * w := by nlinarith [one_le_pow₀ hw1 (n := dT)]
        linarith
      have h3 : ((3 : Nat) : Real) ^ k ≤ w ^ k := by
        refine pow_le_pow_left₀ (by norm_num) ?_ k
        have := (hfacts rho hr hr1).2.2.2.1
        have hV2 : (2 : Real) * 2 ≤ w := by
          have h22 : (2 : Real) * 2 ≤ 2 * (V * (2 / (gamma * theta))) := by nlinarith
          have : 2 * (V * (2 / (gamma * theta))) ≤ w := by
            show 2 * (V * (2 / (gamma * theta))) ≤ uniformBase V 1 theta gamma rho
            unfold uniformBase
            have hri : 1 ≤ rho⁻¹ := one_le_inv₀ hr |>.mpr hr1
            have hs : 2 / (gamma * theta * rho) = 2 / (gamma * theta) * rho⁻¹ := by field_simp
            rw [hs]
            have hpos : 0 ≤ V * (2 / (gamma * theta)) := by positivity
            push_cast
            nlinarith
          linarith
        push_cast
        linarith
      calc ((3 ^ k * ⌈T⌉₊ : Nat) : Real) = ((3 : Nat) : Real) ^ k * ((⌈T⌉₊ : Nat) : Real) := by
            push_cast; ring
        _ ≤ w ^ k * w ^ (dT + 1) :=
            mul_le_mul h3 hceil (Nat.cast_nonneg _) (pow_nonneg (by linarith) _)
        _ = w ^ (dT + k + 1) := by rw [← pow_add]; ring_nf
        _ ≤ w ^ D := pow_le_pow_right₀ hw1 hDT
    · intro rho hr hr1
      have := (hfacts rho hr hr1).2.2.2.2
      positivity
    · intro rho hr hr1
      obtain ⟨-, -, -, hVw, hw2⟩ := hfacts rho hr hr1
      set w := uniformBase V 1 theta gamma rho
      have hw1 : 1 ≤ w := by linarith
      refine le_min le_rfl ?_
      -- `(w^D)⁻¹ ≤ log 2 / log (max 2 T)`
      have hM2 : 1 < max 2 T := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
      have hlog : Real.log (max 2 T) ≤ max 2 T := (Real.log_le_sub_one_of_pos
        (by linarith)).trans (by linarith)
      have hlogpos : 0 < Real.log (max 2 T) := Real.log_pos hM2
      have hl2 : (1 / 2 : Real) ≤ Real.log 2 := by
        have := Real.log_two_gt_d9; linarith
      have hTw : T ≤ w ^ dT := pow_le_pow_left₀ (by linarith) hVw dT
      have hmax : 2 * max 2 T ≤ w ^ D := by
        rcases le_total 2 T with h | h
        · rw [max_eq_right h]
          calc 2 * T ≤ w * w ^ dT := mul_le_mul hw2 hTw (by linarith) (by linarith)
            _ = w ^ (dT + 1) := by rw [pow_succ]; ring
            _ ≤ w ^ D := pow_le_pow_right₀ hw1 (by omega)
        · rw [max_eq_left h]
          calc (2 : Real) * 2 ≤ w ^ 2 := by nlinarith
            _ ≤ w ^ D := pow_le_pow_right₀ hw1 (by omega)
      have hm0 : 0 < max 2 T := lt_trans zero_lt_one hM2
      calc (w ^ D)⁻¹ ≤ (2 * max 2 T)⁻¹ := inv_anti₀ (by positivity) hmax
        _ = (1 / 2) / max 2 T := by field_simp
        _ ≤ Real.log 2 / max 2 T := div_le_div_of_nonneg_right hl2 hm0.le
        _ ≤ Real.log 2 / Real.log (max 2 T) :=
            div_le_div_of_nonneg_left (Real.log_nonneg (by norm_num)) hlogpos hlog

end LeanProofs.GowersSzemeredi
