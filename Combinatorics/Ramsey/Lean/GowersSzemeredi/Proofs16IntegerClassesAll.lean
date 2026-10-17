import GowersSzemeredi.Proofs16IntegerClassTwo
import GowersSzemeredi.Proofs16AllDimensions
import GowersSzemeredi.Proofs16AllDimensionsSide

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
    refine ⟨Finset.univ, ?_, ?_⟩
    · have hc : ((Finset.univ : Finset (Point N k)).card : Real) = (N : Real) ^ k := by
        simp [Point, ZMod.card]
      rw [hc]
      have : (0 : Real) ≤ (N : Real) ^ k := by positivity
      nlinarith
    have hfib : ∀ x : Point N k,
        ((restrictRelation Gamma Finset.univ).filter fun z => z.1 = x).card ≤ ⌈T⌉₊ := by
      intro x
      refine (relation_fiber_card_le_modulus _ x).trans ?_
      exact_mod_cast hNlt.le.trans (Nat.le_ceil T)
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
      exact max_le le_rfl (uniformBase_small_controls hV hg hg1 ht ht1 hr hr1 hDT).1
    · intro rho hr hr1
      have := (hfacts rho hr hr1).2.2.2.2
      positivity
    · intro rho hr hr1
      exact (uniformBase_small_controls hV hg hg1 ht ht1 hr hr1 hDT).2

end LeanProofs.GowersSzemeredi
