import IPRADerivations.Analysis.Gamma.GaussianGammaPoleZeros
import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianGammaShiftTrajectory
import IPRADerivations.Core.CongruenceTactic

/-!
# Quantitative pole guards on the punctured unit disk

For an encoded step h/B about -n, the original pole test at n is
exactly the lower bound on h/B. Every other pole is separated by
the remaining distance to the unit circle. The actual native shift
trajectory ending at 1+h/B has this latter guard at every index.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaLocalPoleGuards

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Probability.Variance (ad)
open ComplexLogarithmRemainder (normSq normSq_eval normSq_scale normSq_neg scale oneCode re im bounded)
open GaussianRootAlgebra
  (equal equal_of_values equal_trans normSq_equal re_add im_add re_scale im_scale re_neg im_neg re_one im_one)
open GaussianGammaEulerHeadLower (translated poleAt poleGuard)
open GaussianGammaPoleZeros (poleNumerator)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def center (h B j : PTm n) : PTm n := ComplexLogarithmRemainder.add h (poleNumerator B j)
def reMagnitude (z : PTm n) : PTm n := ad (re z).pos (re z).neg
def imMagnitude (z : PTm n) : PTm n := ad (im z).pos (im z).neg

def localMargin (h B A S D : PTm n) : Fm PTm n :=
  le (A+S) D ⋏ (bounded (scale D h) (S*B) ⋏ le ((A*B)*(A*B)) (D*D*normSq h))

@[simp] theorem subst_center {l : ℕ} (σ : Fin n → PTm l) (h B j : PTm n) :
    Syn.subst σ (center h B j) = center (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ j) := by
  simp [center,poleNumerator]
@[simp] theorem subst_localMargin {l : ℕ} (σ : Fin n → PTm l) (h B A S D : PTm n) :
    (localMargin h B A S D).subst σ =
      localMargin (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ S) (Syn.subst σ D) := by
  simp [localMargin,bounded]

private theorem norm_components (z : PTm n) : Γ ⊢[PRAAx]
    normSq z ≐ reMagnitude z*reMagnitude z+imMagnitude z*imMagnitude z := by
  have hr := sq_nat (Γ := Γ) (re z)
  have hi := sq_nat (Γ := Γ) (im z)
  simp only [ZT.toZ_sq] at hr hi
  apply deriveNat
  ipra_simps
  rw [normSq_eval,hr,hi]
  unfold reMagnitude imMagnitude
  ipra_simps

private theorem magnitude_bound (z U : PTm n) (h : Γ ⊢[PRAAx] bounded z U) :
    Γ ⊢[PRAAx] le (reMagnitude z) U :=
  nat_sqrt_mono (le_trans (le_of_eq_add (norm_components z)) h)

private theorem real_lower (z U : PTm n) (h : Γ ⊢[PRAAx] bounded z U) :
    Γ ⊢[PRAAx] zle (-ZT.ofNat U) (re z) := by
  let a := (re z).pos
  let b := (re z).neg
  refine .orE (le_total b a) ?_ ?_
  · have ha : le b a :: Γ ⊢[PRAAx] le b a := Prf.hyp0
    have e := natEq (eq_add_of_le ha)
    refine zle_of_toZ (U+monus a b) ?_
    simp only [ZT.toZ_neg,ZT.toZ_ofNat,toZ_def (u := re z),a,b,Q.mk_add,map_add] at *
    linear_combination -e
  · have hb : le a b :: Γ ⊢[PRAAx] le a b := Prf.hyp0
    have hz : le a b :: Γ ⊢[PRAAx] monus a b ≐ zero := hb
    have hmag : le a b :: Γ ⊢[PRAAx] reMagnitude z ≐ monus b a := by
      change _ ⊢[PRAAx] monus a b + monus b a ≐ monus b a
      exact (congrAdd hz (.eqRefl _)).eqTrans (zero_add _)
    have hu := le_congr hmag (.eqRefl _) (magnitude_bound z U h.wk)
    have r := natEq (eq_add_of_le hb)
    have s := natEq (eq_add_of_le hu)
    refine zle_of_toZ (monus U (monus b a)) ?_
    simp only [ZT.toZ_neg,ZT.toZ_ofNat,toZ_def (u := re z),a,b,Q.mk_add,map_add] at *
    linear_combination r - s

/-- A positive horizontal displacement lower-bounds the full Euclidean norm. -/
private theorem lower_after_displacement (z h A U M : PTm n)
    (hh : Γ ⊢[PRAAx] bounded h U) (hm : Γ ⊢[PRAAx] le (A+U) M)
    (he : ZT.toZ Γ (re z) = ZT.toZ Γ (re h) + 𝔞 M) :
    Γ ⊢[PRAAx] le (A*A) (normSq z) := by
  let r := re h
  let s := -ZT.ofNat U
  let W := monus (r.pos+s.neg) (s.pos+r.neg)
  let T := monus M (A+U)
  let K := W+T
  have w : ZT.toZ Γ s + 𝔞 W = ZT.toZ Γ r := zle_toZ (real_lower h U hh)
  have t := natEq (eq_add_of_le hm)
  have value : ZT.toZ Γ (re z) = 𝔞 A+𝔞 K := by
    simp only [s,r,K,T,ZT.toZ_neg,ZT.toZ_ofNat,Q.mk_add,map_add] at w t he ⊢
    linear_combination he - w + t
  have hi := sq_nat (Γ := Γ) (im z)
  simp only [ZT.toZ_sq] at hi
  refine le_of_eq_add (d := A*K+A*K+K*K+imMagnitude z*imMagnitude z) ?_
  apply deriveNat
  ipra_simps
  rw [normSq_eval,value,hi]
  unfold imMagnitude
  ipra_simps
  ring

theorem translation_at_center (h B j : PTm n) : Γ ⊢[PRAAx] equal (translated (center h B j) B j) h := by
  apply equal_of_values <;>
    simp only [center,translated,poleNumerator,re_add,im_add,re_neg,im_neg,re_scale,im_scale,re_one,im_one] <;> ring

private theorem right_displacement (h B D j k i : PTm n)
    (e : Γ ⊢[PRAAx] k ≐ j+i) :
    ZT.toZ Γ (re (scale D (translated (center h B j) B k))) = ZT.toZ Γ (re (scale D h)) + 𝔞 (D*B*i) := by
  have ek := natEq e
  simp only [center,translated,poleNumerator,re_add,re_neg,re_scale,re_one]
  ipra_simps
  rw [ek]
  ring

private theorem left_displacement (h B D j k i : PTm n)
    (e : Γ ⊢[PRAAx] j ≐ k+i) :
    ZT.toZ Γ (re (ComplexLogarithmRemainder.neg (scale D (translated (center h B j) B k)))) =
      ZT.toZ Γ (re (ComplexLogarithmRemainder.neg (scale D h))) + 𝔞 (D*B*i) := by
  have ej := natEq e
  simp only [center,translated,poleNumerator,re_add,re_neg,re_scale,re_one]
  ipra_simps
  rw [ej]
  ring

private theorem displacement_budget (B D A S i : PTm n)
    (hi : Γ ⊢[PRAAx] le one i) (hm : Γ ⊢[PRAAx] le (A+S) D) :
    Γ ⊢[PRAAx] le (A*B+S*B) (D*B*i) := by
  have h := mul_le_mul_right B hm
  have upper := le_mul_mono (le_refl (D*B)) hi
  exact le_trans (le_congr (by ipra_ring) (.eqRefl _) h) (le_congr (by ipra_ring) (.eqRefl _) upper)

theorem translated_pole_right (h B A S D j k : PTm n)
    (hm : Γ ⊢[PRAAx] le (A+S) D) (hh : Γ ⊢[PRAAx] bounded (scale D h) (S*B))
    (hk : Γ ⊢[PRAAx] lt j k) :
    Γ ⊢[PRAAx] poleAt (center h B j) B A D k := by
  let i := succ (monus k (succ j))
  have e : Γ ⊢[PRAAx] k ≐ j+i := (eq_add_of_le hk).eqTrans (by unfold i; ipra_ring)
  have h := lower_after_displacement _ _ (A*B) (S*B) (D*B*i) hh
    (displacement_budget _ _ _ _ i (zero_lt_succ _) hm) (right_displacement h B D j k i e)
  exact le_congr (.eqRefl _) (normSq_scale D _) h

theorem translated_pole_left (h B A S D j k : PTm n)
    (hm : Γ ⊢[PRAAx] le (A+S) D) (hh : Γ ⊢[PRAAx] bounded (scale D h) (S*B))
    (hk : Γ ⊢[PRAAx] lt k j) :
    Γ ⊢[PRAAx] poleAt (center h B j) B A D k := by
  let i := succ (monus j (succ k))
  have e : Γ ⊢[PRAAx] j ≐ k+i := (eq_add_of_le hk).eqTrans (by unfold i; ipra_ring)
  have h := lower_after_displacement _ _ (A*B) (S*B) (D*B*i) (ComplexLogarithmRemainder.bounded_neg hh)
    (displacement_budget _ _ _ _ i (zero_lt_succ _) hm) (left_displacement h B D j k i e)
  exact le_congr (.eqRefl _) ((normSq_neg _).eqTrans (normSq_scale D _)) h

theorem original_local_pole_at (h B A S D j k : PTm n) (hm : Γ ⊢[PRAAx] localMargin h B A S D) :
    Γ ⊢[PRAAx] poleAt (center h B j) B A D k := by
  refine .orE (lt_or_le k j) ?_ ?_
  · exact translated_pole_left _ _ _ _ _ _ _ hm.andE₁.wk hm.andE₂.andE₁.wk Prf.hyp0
  · have hk : le j k :: Γ ⊢[PRAAx] le j k := Prf.hyp0
    refine .orE (lt_or_eq_of_le hk) ?_ ?_
    · exact translated_pole_right _ _ _ _ _ _ _ hm.andE₁.wk.wk hm.andE₂.andE₁.wk.wk Prf.hyp0
    · let C := (j ≐ k) :: (le j k) :: Γ
      have e : C ⊢[PRAAx] j ≐ k := Prf.hyp0
      have he : C ⊢[PRAAx] translated (center h B j) B j ≐ translated (center h B j) B k := by
        ipra_congr (translated (var 0) (var 1) (var 2) : PTm 3) with [.eqRefl (center h B j), .eqRefl B, e]
      exact le_congr (.eqRefl _) (congrMul (.eqRefl _)
        ((normSq_equal (translation_at_center (Γ := C) h B j)).eqSymm.eqTrans
          (ComplexLogarithmRemainder.congr_normSq he))) hm.andE₂.andE₂.wk.wk

theorem original_local_pole_guard (h B A S D j L : PTm n) (hm : Γ ⊢[PRAAx] localMargin h B A S D) :
    Γ ⊢[PRAAx] poleGuard (center h B j) B A D L := by
  refine .allI (.impI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] localMargin (Syn.shift h) (Syn.shift B) (Syn.shift A) (Syn.shift S) (Syn.shift D) :=
    by simpa only [Fm.shift,Syn.shift,subst_localMargin] using hm.shift
  simpa only [Syn.shift,subst_center] using
    original_local_pole_at (Syn.shift h) (Syn.shift B) (Syn.shift A) (Syn.shift S) (Syn.shift D)
      (Syn.shift j) (var 0) hs.wk

def terminal (h B j : PTm n) : PTm n := GaussianGammaShiftTrajectory.point (center h B j) B (succ j)

@[simp] theorem subst_terminal {l : ℕ} (σ : Fin n → PTm l) (h B j : PTm n) :
    Syn.subst σ (terminal h B j) = terminal (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ j) := by
  simp [terminal]

theorem terminal_native (h B j : PTm n) : Γ ⊢[PRAAx] equal (terminal h B j) (translated h B one) := by
  apply equal_trans (GaussianGammaShiftTrajectory.point_native (center h B j) B (succ j))
  apply equal_of_values <;>
    simp only [center,translated,poleNumerator,re_add,im_add,re_neg,im_neg,re_scale,im_scale,re_one,im_one] <;>
    ipra_simps <;> ring

theorem terminal_pole_at (h B A S D j k : PTm n)
    (hm : Γ ⊢[PRAAx] le (A+S) D) (hh : Γ ⊢[PRAAx] bounded (scale D h) (S*B)) :
    Γ ⊢[PRAAx] poleAt (terminal h B j) B A D k := by
  have cover : Γ ⊢[PRAAx] lt j (succ j+k) := le_add_right _ _
  have old := translated_pole_right h B A S D j (succ j+k) hm hh cover
  have same := GaussianGammaShiftTrajectory.translated_native (Γ := Γ) (center h B j) B (succ j) k
  exact le_congr (.eqRefl _) (congrMul (.eqRefl _) (normSq_equal same).eqSymm) old

theorem terminal_pole_guard (h B A S D j L : PTm n)
    (hm : Γ ⊢[PRAAx] le (A+S) D) (hh : Γ ⊢[PRAAx] bounded (scale D h) (S*B)) :
    Γ ⊢[PRAAx] poleGuard (terminal h B j) B A D L := by
  refine .allI (.impI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift A+Syn.shift S) (Syn.shift D) :=
    by simpa [Fm.shift,Syn.shift] using hm.shift
  have hu : Γ.map Fm.shift ⊢[PRAAx] bounded (scale (Syn.shift D) (Syn.shift h)) (Syn.shift S*Syn.shift B) :=
    by simpa [Fm.shift,Syn.shift,bounded] using hh.shift
  simpa only [Syn.shift,subst_terminal] using
    terminal_pole_at (Syn.shift h) (Syn.shift B) (Syn.shift A) (Syn.shift S) (Syn.shift D)
      (Syn.shift j) (var 0) hs.wk hu.wk

theorem local_step_disk (h B S D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hS : Γ ⊢[PRAAx] le S D) (hh : Γ ⊢[PRAAx] bounded (scale D h) (S*B)) :
    Γ ⊢[PRAAx] bounded h B := by
  have hdd := GaussianRationalHorner.positive_product _ _ hD hD
  have scaled := le_congr (normSq_scale D h) (.eqRefl _) hh
  have step := mul_le_mul_right B hS
  have e : Γ ⊢[PRAAx] le (D*D*normSq h) (D*D*(B*B)) :=
    le_congr (.eqRefl _) (by ipra_ring) (le_trans scaled (le_mul_mono step step))
  exact RationalValueBounds.positive_cancel hdd e

private theorem integer_axis_disk (b : PTm n) : Γ ⊢[PRAAx] bounded (scale b oneCode) b := by
  have eq : Γ ⊢[PRAAx] normSq (scale b oneCode) ≐ b*b := (normSq_scale (Γ := Γ) b oneCode).eqTrans
    ((congrMul (.eqRefl _) (ComplexLogarithmRemainder.normSq_one (Γ := Γ))).eqTrans (by ipra_ring))
  exact le_congr eq.eqSymm (.eqRefl _) (le_refl _)

theorem center_source_disk (h B j : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hh : Γ ⊢[PRAAx] bounded h B) :
    Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source (center h B j) (succ j) B :=
  .andI (zero_lt_succ j) (.andI hB
    (le_congr (.eqRefl _) (by ipra_ring)
      (ComplexLogarithmRemainder.bounded_add hh
        (ComplexLogarithmRemainder.bounded_neg (integer_axis_disk (B*j))))))

theorem terminal_source_disk (h B j : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hh : Γ ⊢[PRAAx] bounded h B) :
    Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source (terminal h B j) two B := by
  have old := ComplexLogarithmRemainder.bounded_add hh (integer_axis_disk (B*one))
  exact .andI (le_succ_self one) (.andI hB
    (le_congr (normSq_equal (terminal_native h B j)).eqSymm (by ipra_ring) old))

theorem center_Gamma_domain (h B A S D j : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hA : Γ ⊢[PRAAx] le one A) (hD : Γ ⊢[PRAAx] le one D)
    (hm : Γ ⊢[PRAAx] localMargin h B A S D) :
    Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source (center h B j) (succ j) B A D := by
  have hS := le_trans (le_add_left S A) hm.andE₁
  exact .andI (center_source_disk h B j hB (local_step_disk _ _ _ _ hD hS hm.andE₂.andE₁))
    (.andI hA (.andI hD (original_local_pole_guard h B A S D j (two*succ j) hm)))

theorem terminal_Gamma_domain (h B A S D j : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hA : Γ ⊢[PRAAx] le one A) (hD : Γ ⊢[PRAAx] le one D)
    (hm : Γ ⊢[PRAAx] le (A+S) D) (hh : Γ ⊢[PRAAx] bounded (scale D h) (S*B)) :
    Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source (terminal h B j) two B A D := by
  have hS := le_trans (le_add_left S A) hm
  exact .andI (terminal_source_disk h B j hB (local_step_disk _ _ _ _ hD hS hh))
    (.andI hA (.andI hD (terminal_pole_guard h B A S D j (two*two) hm hh)))

theorem original_local_pole_guard_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (localMargin (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      poleGuard (center (var 0) (var 1) (var 5)) (var 1) (var 2) (var 4) (var 6)) :=
  closeUniv 7 (.impI (original_local_pole_guard _ _ _ _ _ _ _ Prf.hyp0))

theorem original_local_terminal_pole_guard_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le (var 2+var 3) (var 4) ⟶ bounded (scale (var 4) (var 0)) (var 3*var 1) ⟶
      poleGuard (terminal (var 0) (var 1) (var 5)) (var 1) (var 2) (var 4) (var 6)) :=
  closeUniv 7 (.impI (.impI (terminal_pole_guard _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem original_local_pole_domains_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 1) ⟶ le one (var 2) ⟶ le one (var 4) ⟶
      localMargin (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      GaussianGammaReciprocalInverse.source (center (var 0) (var 1) (var 5)) (succ (var 5))
        (var 1) (var 2) (var 4) ⋏
      GaussianGammaReciprocalInverse.source (terminal (var 0) (var 1) (var 5)) two
        (var 1) (var 2) (var 4)) :=
  closeUniv 6 (.impI (.impI (.impI (.impI
    (.andI (center_Gamma_domain _ _ _ _ _ _ hyp2.wk hyp2 Prf.hyp1 Prf.hyp0)
      (terminal_Gamma_domain _ _ _ _ _ _ hyp2.wk hyp2 Prf.hyp1 Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁))))))

end LeanProofs.IPRA.Analysis.GaussianGammaLocalPoleGuards
