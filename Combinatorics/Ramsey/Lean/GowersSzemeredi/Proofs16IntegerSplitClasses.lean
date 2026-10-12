import GowersSzemeredi.Proofs16IntegerClassesAll
import GowersSzemeredi.Proofs16SplitAllDimensions

/-! Integer progression covers with split family and parameter degrees.
The split recurrence retains the sharper bounds while every covering box
has ascending integer representatives. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem SplitUniformClass.integerCover_toPower {k : Nat} {V : Real} {a D : Nat}
    (C : SplitUniformClass k V a D) (hInt : C.IntegerCover) (hV : 1 ≤ V) :
    (C.toPower hV).IntegerCover := by
    intro theta gamma ht ht1 hg hg1 N _ _ n Gamma hU
    refine (hInt theta gamma ht ht1 hg hg1 N n Gamma hU).weaken ?_ ?_ ?_
    · intro rho hr hr1
      obtain ⟨hw2, -, -, -⟩ := splitW_facts hV hg hg1 ht ht1 hr hr1
      have hn1 : (1 : Real) ≤ (n : Real) + 1 := by
        have := Nat.cast_nonneg (α := Real) n; linarith
      show ((n : Real) + 1) ^ a * splitW V theta gamma rho ^ D ≤ uniformBase V n theta gamma rho ^ (a + D)
      rw [uniformBase_eq_split, mul_pow, pow_add, pow_add]
      have h1 : ((n : Real) + 1) ^ a ≤ ((n : Real) + 1) ^ a * ((n : Real) + 1) ^ D :=
        le_mul_of_one_le_right (by positivity) (one_le_pow₀ hn1)
      have h2 : splitW V theta gamma rho ^ D ≤ splitW V theta gamma rho ^ a *
          splitW V theta gamma rho ^ D :=
        le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by linarith))
      calc ((n : Real) + 1) ^ a * splitW V theta gamma rho ^ D
          ≤ (((n : Real) + 1) ^ a * ((n : Real) + 1) ^ D) *
              (splitW V theta gamma rho ^ a * splitW V theta gamma rho ^ D) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = _ := by ring
    · intro rho hr hr1
      have h2 := uniformBase_two_le hV n ht ht1 hg hg1 hr hr1
      positivity
    · intro rho hr hr1
      obtain ⟨hw2, -, -, -⟩ := splitW_facts hV hg hg1 ht ht1 hr hr1
      have hn1 : (1 : Real) ≤ (n : Real) + 1 := by
        have := Nat.cast_nonneg (α := Real) n; linarith
      show (uniformBase V n theta gamma rho ^ (a + D))⁻¹ ≤
        (((n : Real) + 1) ^ a * splitW V theta gamma rho ^ D)⁻¹
      refine inv_anti₀ (by positivity) ?_
      rw [uniformBase_eq_split, mul_pow, pow_add, pow_add]
      have h1 : ((n : Real) + 1) ^ a ≤ ((n : Real) + 1) ^ a * ((n : Real) + 1) ^ D :=
        le_mul_of_one_le_right (by positivity) (one_le_pow₀ hn1)
      have h2 : splitW V theta gamma rho ^ D ≤ splitW V theta gamma rho ^ a *
          splitW V theta gamma rho ^ D :=
        le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by linarith))
      calc ((n : Real) + 1) ^ a * splitW V theta gamma rho ^ D
          ≤ (((n : Real) + 1) ^ a * ((n : Real) + 1) ^ D) *
              (splitW V theta gamma rho ^ a * splitW V theta gamma rho ^ D) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = _ := by ring

theorem PowerUniformClass.integerCover_toSplit {k : Nat} {V : Real} {d : Nat}
    (C : PowerUniformClass k V d d d) (hInt : C.IntegerCover) :
    C.toSplit.IntegerCover := by
    intro theta gamma ht ht1 hg hg1 N _ _ n Gamma hU
    have h := hInt theta gamma ht ht1 hg hg1 N n Gamma hU
    have hfun : ∀ rho, uniformBase V n theta gamma rho ^ d =
        ((n : Real) + 1) ^ d * splitW V theta gamma rho ^ d := fun rho => by
      rw [uniformBase_eq_split, mul_pow]
    simp only [hfun] at h
    exact h

theorem splitUniformClass_two_integer {K1 p1 : Nat} (hK1 : 1 ≤ K1) (hp1 : 0 < p1)
    (hlemma6 : AbstractFamilyLemma166At 1
      (section16PowerWidth (familyWidthPrefactor K1) (familyWidthDivisor 1 p1)))
    (hIntegerLemma6 : IntegerAbstractFamilyLemma166At 1
      (section16PowerWidth (familyWidthPrefactor K1) (familyWidthDivisor 1 p1)))
    {V : Real} (hV : 1 ≤ V) (hKV : (K1 : Real) ≤ V) (hpV : (p1 : Real) ≤ V) {d : Nat}
    (hd : (2 : Nat) ^ 130 ≤ d) :
    ∃ C : SplitUniformClass 2 V d d, C.IntegerCover := by
  obtain ⟨C, hC⟩ := powerUniformClass_two_integer hK1 hp1 hlemma6 hIntegerLemma6 hV hKV hpV
  have h89 : (2 : Nat) ^ 89 ≤ d := le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) hd
  have h45 : (2 : Nat) ^ 45 ≤ d := le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) hd
  exact ⟨(C.weaken hV le_rfl h89 hd h45).toSplit,
    (C.weaken hV le_rfl h89 hd h45).integerCover_toSplit
      (C.integerCover_weaken hC hV le_rfl h89 hd h45)⟩

theorem splitUniformClass_succ_integer {k : Nat} (hk : 1 ≤ k) {V : Real} (hV : 1 ≤ V) {a D : Nat}
    (ha : 1 ≤ a) (hD : 1 ≤ D) (C : SplitUniformClass k V a D) (hInt : C.IntegerCover) {K p : Nat} (hK : 1 ≤ K)
    (hp : 0 < p)
    (hlemma6 : AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor K) (familyWidthDivisor k p)))
    (hIntegerLemma6 : IntegerAbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor K) (familyWidthDivisor k p)))
    {V' : Real} (hVV : V ≤ V') (hKV : (K : Real) ≤ V') (hpV : (p : Real) ≤ V') :
    ∃ C' : SplitUniformClass (k + 1) V' (splitStepA k a) (splitStepD k a D), C'.IntegerCover := by
  classical
  obtain ⟨hCnt, hExp, hCntMono, hExpAnti⟩ := splitCnt_controls hV a D
  refine ⟨{
    U := fun N _ theta gamma Gamma =>
      ∃ P : Fin (classPieces gamma theta k) → StepPiece C N theta gamma,
        Gamma ⊆ stepPieceGraphs C P
    mono := fun N _ theta gamma Gamma Gamma' hsub ⟨P, hP⟩ => ⟨P, hsub.trans hP⟩
    empty := fun N _ theta gamma =>
      ⟨fun _ => ClassPiece.empty C _ _ _ _ _ _, Finset.empty_subset _⟩
    decomp := ?_
    cover := ?_ }, ?_⟩
  · intro theta gamma ht ht1 hg hg1 N _ _ hN Gamma hsize hprod
    obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
    have hVu : 1 ≤ V' * (2 / (gamma * theta)) :=
      one_le_mul_of_one_le_of_one_le (hV.trans hVV) (le_trans (by norm_num) hu2)
    have hN' : classStepThr (fun theta gamma => (V * (2 / (gamma * theta))) ^ D) theta gamma k ≤ N := by
      rw [← classStepThreshold_eq]
      refine (step_thr_le hk hV hVV hg hg1 ht ht1).trans (le_trans ?_ hN)
      exact pow_le_pow_right₀ hVu (by unfold splitStepD; omega)
    obtain ⟨J, hJ, P, hP⟩ := class_step_decomp C hk ht ht1 hg hg1 hN' Gamma hsize hprod
    exact ⟨J, hJ, P, hP⟩
  · intro theta gamma ht ht1 hg hg1 N _ _ n Gamma hU
    choose P hP using hU
    have h := class_step_cover_gen C hk hCnt hExp hCntMono hExpAnti (familyWidthPrefactor_pos hK)
      (familyWidthDivisor_pos hp) hlemma6 ht ht1 hg hg1 Gamma P hP
    refine h.weaken ?_ ?_ ?_
    · intro rho hr hr1
      have hc := split_count_le (k := k) ha hD hV hVV hg hg1 ht ht1 hr hr1 n
      obtain ⟨hw2, -, -, -, -⟩ := split_w_facts hV hVV hg hg1 ht ht1 hr hr1
      have hν : (1 : Real) ≤ (n : Real) + 1 := by
        have := Nat.cast_nonneg (α := Real) n; linarith
      refine hc.trans (tb_mono hν (by linarith) (by unfold splitStepA; omega)
        (by unfold splitStepD; omega))
    · intro rho hr hr1
      obtain ⟨hw2, -, -, -, -⟩ := split_w_facts hV hVV hg hg1 ht ht1 hr hr1
      have hν : (1 : Real) ≤ (n : Real) + 1 := by
        have := Nat.cast_nonneg (α := Real) n; linarith
      exact inv_pos.mpr (lt_of_lt_of_le zero_lt_one (tb_one_le hν (by linarith)))
    · intro rho hr hr1
      obtain ⟨he0, hei⟩ := split_exp_inv_le (k := k) ha hD hV hVV hK hp hKV hpV hg hg1 ht ht1 hr hr1 n
      obtain ⟨hw2, -, -, -, -⟩ := split_w_facts hV hVV hg hg1 ht ht1 hr hr1
      have hν : (1 : Real) ≤ (n : Real) + 1 := by
        have := Nat.cast_nonneg (α := Real) n; linarith
      have hmono := tb_mono (a := sExpN k a) (b := sExpW k a D) (a' := splitStepA k a)
        (b' := splitStepD k a D) hν (by linarith) (by unfold splitStepA; omega)
        (by unfold splitStepD; omega)
      have h1 := inv_anti₀ (lt_of_lt_of_le zero_lt_one (tb_one_le hν (by linarith))) hmono
      have h2 := inv_anti₀ (inv_pos.mpr he0) hei
      rw [inv_inv] at h2
      exact h1.trans h2

  · intro theta gamma ht ht1 hg hg1 N _ _ n Gamma hU
    choose P hP using hU
    have h := integer_class_step_cover_gen C hInt hk hCnt hExp hCntMono hExpAnti (familyWidthPrefactor_pos hK)
      (familyWidthDivisor_pos hp) hIntegerLemma6 ht ht1 hg hg1 Gamma P hP
    refine h.weaken ?_ ?_ ?_
    · intro rho hr hr1
      have hc := split_count_le (k := k) ha hD hV hVV hg hg1 ht ht1 hr hr1 n
      obtain ⟨hw2, -, -, -, -⟩ := split_w_facts hV hVV hg hg1 ht ht1 hr hr1
      have hν : (1 : Real) ≤ (n : Real) + 1 := by
        have := Nat.cast_nonneg (α := Real) n; linarith
      refine hc.trans (tb_mono hν (by linarith) (by unfold splitStepA; omega)
        (by unfold splitStepD; omega))
    · intro rho hr hr1
      obtain ⟨hw2, -, -, -, -⟩ := split_w_facts hV hVV hg hg1 ht ht1 hr hr1
      have hν : (1 : Real) ≤ (n : Real) + 1 := by
        have := Nat.cast_nonneg (α := Real) n; linarith
      exact inv_pos.mpr (lt_of_lt_of_le zero_lt_one (tb_one_le hν (by linarith)))
    · intro rho hr hr1
      obtain ⟨he0, hei⟩ := split_exp_inv_le (k := k) ha hD hV hVV hK hp hKV hpV hg hg1 ht ht1 hr hr1 n
      obtain ⟨hw2, -, -, -, -⟩ := split_w_facts hV hVV hg hg1 ht ht1 hr hr1
      have hν : (1 : Real) ≤ (n : Real) + 1 := by
        have := Nat.cast_nonneg (α := Real) n; linarith
      have hmono := tb_mono (a := sExpN k a) (b := sExpW k a D) (a' := splitStepA k a)
        (b' := splitStepD k a D) hν (by linarith) (by unfold splitStepA; omega)
        (by unfold splitStepD; omega)
      have h1 := inv_anti₀ (lt_of_lt_of_le zero_lt_one (tb_one_le hν (by linarith))) hmono
      have h2 := inv_anti₀ (inv_pos.mpr he0) hei
      rw [inv_inv] at h2
      exact h1.trans h2

theorem splitUniformClass_all_integer (Kc pc : Nat → Nat) (hK : ∀ k, 1 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))))
    (hIntegerLemma : ∀ k, 1 ≤ k → IntegerAbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k)))) :
    ∀ k, 2 ≤ k →
      ∃ C : SplitUniformClass k (classV Kc pc k) (splitPair k).1 (splitPair k).2, C.IntegerCover := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    have hV1 := one_le_classV Kc pc 2
    have hc1 := const_le_classV_succ Kc pc 1
    rw [splitPair_two]
    exact splitUniformClass_two_integer (hK 1) (hp 1) (hlem 1 le_rfl) (hIntegerLemma 1 le_rfl) hV1 (hc1.1.trans le_rfl)
      (hc1.2.trans le_rfl) (by unfold splitSeed; exact Nat.pow_le_pow_right (by norm_num) (by norm_num))
  | succ k hk ih =>
    obtain ⟨C, hC⟩ := ih
    obtain ⟨ha, hD, -, -⟩ := split_pair_bounds k hk
    have hV1 := one_le_classV Kc pc k
    have hc := const_le_classV_succ Kc pc k
    rw [splitPair_succ hk]
    exact splitUniformClass_succ_integer (by omega) hV1 ha hD C hC (hK k) (hp k) (hlem k (by omega)) (hIntegerLemma k (by omega))
      (classV_le_succ Kc pc k) hc.1 hc.2

end LeanProofs.GowersSzemeredi
