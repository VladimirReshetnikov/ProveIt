import IPRADerivations.Probability.MedianSorted
import IPRADerivations.Foundations.BoundedReflection

/-!
# The finite-sample replacement breakdown of the median

Packet: `probability/median_ipra_constructive_proofs`, Theorem `thm:breakdown`, in the
division-free balance form of `MedianCounts` (`t` is a balance median of data `y` of length `N`
when `2B(t) ≤ N` and `2A(t) ≤ N`).

A contamination `z` of the data `x` replaces at most `r` coordinates: the mismatch count
`D = #{i < N : z_i ≠ x_i}` is at most `r`.

* `below_cmp`, `above_cmp`: `B_x(t) ≤ B_z(t) + D` and `A_x(t) ≤ A_z(t) + D` (each changed coordinate
  moves one bit);
* `bounded` (fewer than half replaced): if `2r < N`, every balance median `t` of `z` lies between
  bounds `m ≤ x_i ≤ M` of the original data, whatever the replacement values;
* `zB`: replacing the first `s` coordinates by `H`, with `#{i : z_i ≠ x_i} ≤ s` (`rep_count`);
* `driven_med` (half replaced): if `N ≤ 2s` and `x_i ≤ H`, then `H` itself is a balance median of
  `z`, so the median set reaches every `H`; `driven_above`: if `N < 2s`, every balance median of
  `z` is at least `H`.

So `⌈N/2⌉`, the least `s` with `N ≤ 2s`, is the minimal number of replacements that can drive the
median without bound, and the breakdown fraction is `⌈N/2⌉ / N`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.MedianBreakdown

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Algebra.CubeRootTwo (sg)
open LeanProofs.IPRA.AnalyticNumberTheory.Totatives (sg_lt sg_le)
open LeanProofs.IPRA.AnalyticNumberTheory.EulerDomination (sg_le_one)
open LeanProofs.IPRA.Probability.Expectation (le_zero_of)
open LeanProofs.IPRA.Probability.Variance (sum_one)
open LeanProofs.IPRA.Probability.MedianCounts (belowB aboveB Bc Ac below_pt above_pt isMed congrSg subst_data)
open LeanProofs.IPRA.Probability.MedianSorted (geB inst2_geB count_ge le_shift)
open LeanProofs.IPRA.Combinatorics.LegendreFact (ltB inst2_ltB inst2_one2 count_lt)
open LeanProofs.IPRA.AnalyticNumberTheory.TotientCorollaries (eqb_le_one)
open LeanProofs.IPRA.Foundations.BoundedReflection (eqb_cases eq_of_eqb)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem subst_dataG (i z : PTm n) (g f : PTm 2) :
    Syn.subst ![i, z] (Syn.subst ![var 0, g] f) = inst2 f i (Syn.subst ![i, z] g) := by
  unfold inst2
  rw [Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp

theorem lt_shift {a b : PTm n} (h : Γ ⊢[PRAAx] lt a b) : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift a) (Syn.shift b) := by
  have e := le_shift h
  have hs : Syn.shift (succ a) = succ (Syn.shift a) := by simp [Syn.shift]
  rw [hs] at e
  exact e

theorem monus_one_le (e : PTm n) (h : Γ ⊢[PRAAx] le e one) : Γ ⊢[PRAAx] le (monus one e) one :=
  le_of_eq_add (d := e) ((eq_add_of_le h).eqTrans (add_comm _ _))

/-! ## One changed coordinate moves one bit -/

theorem bit_cmp_below (x z t : PTm n) :
    Γ ⊢[PRAAx] le (sg (monus t x)) (sg (monus t z) + monus one (eqb z x)) := by
  refine .orE (eqb_cases z x) ?_ ?_
  · let C := (eqb z x ≐ zero) :: Γ
    have h : C ⊢[PRAAx] monus one (eqb z x) ≐ one := (congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_zero _)
    have e := natEq h
    refine le_trans (sg_le_one _) (le_of_eq_add (d := sg (monus t z)) ?_)
    apply deriveNat; ipra_simps; linear_combination e
  · let C := (eqb z x ≐ one) :: Γ
    have ex : C ⊢[PRAAx] z ≐ x := eq_of_eqb Prf.hyp0
    have m : C ⊢[PRAAx] monus one (eqb z x) ≐ zero := (congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_self _)
    have c : C ⊢[PRAAx] sg (monus t z) ≐ sg (monus t x) := congrSg (congrMonus (.eqRefl _) ex)
    have e1 := natEq m; have e2 := natEq c
    refine le_of_eq_add (d := zero) ?_
    apply deriveNat; ipra_simps; linear_combination e1 + e2

theorem bit_cmp_above (x z t : PTm n) :
    Γ ⊢[PRAAx] le (sg (monus x t)) (sg (monus z t) + monus one (eqb z x)) := by
  refine .orE (eqb_cases z x) ?_ ?_
  · let C := (eqb z x ≐ zero) :: Γ
    have h : C ⊢[PRAAx] monus one (eqb z x) ≐ one := (congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_zero _)
    have e := natEq h
    refine le_trans (sg_le_one _) (le_of_eq_add (d := sg (monus z t)) ?_)
    apply deriveNat; ipra_simps; linear_combination e
  · let C := (eqb z x ≐ one) :: Γ
    have ex : C ⊢[PRAAx] z ≐ x := eq_of_eqb Prf.hyp0
    have m : C ⊢[PRAAx] monus one (eqb z x) ≐ zero := (congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_self _)
    have c : C ⊢[PRAAx] sg (monus z t) ≐ sg (monus x t) := congrSg (congrMonus ex (.eqRefl _))
    have e1 := natEq m; have e2 := natEq c
    refine le_of_eq_add (d := zero) ?_
    apply deriveNat; ipra_simps; linear_combination e1 + e2

section Compare

variable (X Z : PTm 2)

/-- `[z_i ≠ x_i]`, over `0 = i`, `1 = ⟨q, p⟩` (`z` read at `q`, `x` at `p`). -/
def dB : PTm 2 := monus one (eqb (Syn.subst ![var 0, fstT (var 1)] Z) (Syn.subst ![var 0, sndT (var 1)] X))

/-- The mismatch count `D = #{i < N : z_i ≠ x_i}`. -/
abbrev Dc (N q p : PTm n) : PTm n := ap2 (sumF (dB X Z)) N (pairT q p)

/-- Bodies over `0 = i`, `1 = ⟨t, ⟨q, p⟩⟩`. -/
def bZ : PTm 2 := sg (monus (fstT (var 1)) (Syn.subst ![var 0, fstT (sndT (var 1))] Z))
def aZ : PTm 2 := sg (monus (Syn.subst ![var 0, fstT (sndT (var 1))] Z) (fstT (var 1)))
def dT : PTm 2 :=
  monus one (eqb (Syn.subst ![var 0, fstT (sndT (var 1))] Z) (Syn.subst ![var 0, sndT (sndT (var 1))] X))

theorem dB_eq (i P : PTm n) :
    inst2 (dB X Z) i P = monus one (eqb (inst2 Z i (fstT P)) (inst2 X i (sndT P))) := by
  simp only [inst2, dB, PTm.subst_monus, subst_eqb, subst_dataG, subst_fstT, subst_sndT,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var]
  simp

theorem bZ_eq (i P : PTm n) : inst2 (bZ Z) i P = sg (monus (fstT P) (inst2 Z i (fstT (sndT P)))) := by
  simp only [inst2, bZ, PTm.subst_monus, subst_dataG, subst_fstT, subst_sndT,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var]
  simp

theorem aZ_eq (i P : PTm n) : inst2 (aZ Z) i P = sg (monus (inst2 Z i (fstT (sndT P))) (fstT P)) := by
  simp only [inst2, aZ, PTm.subst_monus, subst_dataG, subst_fstT, subst_sndT,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var]
  simp

theorem dT_eq (i P : PTm n) :
    inst2 (dT X Z) i P = monus one (eqb (inst2 Z i (fstT (sndT P))) (inst2 X i (sndT (sndT P)))) := by
  simp only [inst2, dT, PTm.subst_monus, subst_eqb, subst_dataG, subst_fstT, subst_sndT,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var]
  simp

theorem dB_at (i q p : PTm n) :
    Γ ⊢[PRAAx] inst2 (dB X Z) i (pairT q p) ≐ monus one (eqb (inst2 Z i q) (inst2 X i p)) := by
  rw [dB_eq]
  exact congrMonus (.eqRefl _) (LeanProofs.IPRA.AnalyticNumberTheory.Euler.congrEqb
    (congrInst2 Z (.eqRefl _) (fst_pair _ _)) (congrInst2 X (.eqRefl _) (snd_pair _ _)))

theorem tq_parts (t q p : PTm n) :
    Γ ⊢[PRAAx] (fstT (pairT t (pairT q p)) ≐ t) ⋏ ((fstT (sndT (pairT t (pairT q p))) ≐ q) ⋏
      (sndT (sndT (pairT t (pairT q p))) ≐ p)) :=
  .andI (fst_pair _ _) (.andI ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
    ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)))

theorem bZ_at (i t q p : PTm n) :
    Γ ⊢[PRAAx] inst2 (bZ Z) i (pairT t (pairT q p)) ≐ sg (monus t (inst2 Z i q)) := by
  rw [bZ_eq]
  have h := tq_parts (Γ := Γ) t q p
  exact congrSg (congrMonus (Prf.andE₁ h) (congrInst2 Z (.eqRefl _) (Prf.andE₁ (Prf.andE₂ h))))

theorem aZ_at (i t q p : PTm n) :
    Γ ⊢[PRAAx] inst2 (aZ Z) i (pairT t (pairT q p)) ≐ sg (monus (inst2 Z i q) t) := by
  rw [aZ_eq]
  have h := tq_parts (Γ := Γ) t q p
  exact congrSg (congrMonus (congrInst2 Z (.eqRefl _) (Prf.andE₁ (Prf.andE₂ h))) (Prf.andE₁ h))

theorem dT_at (i t q p : PTm n) :
    Γ ⊢[PRAAx] inst2 (dT X Z) i (pairT t (pairT q p)) ≐ monus one (eqb (inst2 Z i q) (inst2 X i p)) := by
  rw [dT_eq]
  have h := tq_parts (Γ := Γ) t q p
  exact congrMonus (.eqRefl _) (LeanProofs.IPRA.AnalyticNumberTheory.Euler.congrEqb
    (congrInst2 Z (.eqRefl _) (Prf.andE₁ (Prf.andE₂ h))) (congrInst2 X (.eqRefl _) (Prf.andE₂ (Prf.andE₂ h))))

theorem sum_bZ (N t q p : PTm n) : Γ ⊢[PRAAx] ap2 (sumF (bZ Z)) N (pairT t (pairT q p)) ≐ Bc Z N t q := by
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT]
  exact (bZ_at Z _ _ _ _).eqTrans (below_pt Z _ _ _).eqSymm

theorem sum_aZ (N t q p : PTm n) : Γ ⊢[PRAAx] ap2 (sumF (aZ Z)) N (pairT t (pairT q p)) ≐ Ac Z N t q := by
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT]
  exact (aZ_at Z _ _ _ _).eqTrans (above_pt Z _ _ _).eqSymm

theorem sum_dT (N t q p : PTm n) : Γ ⊢[PRAAx] ap2 (sumF (dT X Z)) N (pairT t (pairT q p)) ≐ Dc X Z N q p := by
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT]
  exact (dT_at X Z _ _ _ _).eqTrans (dB_at X Z _ _ _).eqSymm

/-- `B_x(t) ≤ B_z(t) + D`. -/
theorem below_cmp (N t q p : PTm n) : Γ ⊢[PRAAx] le (Bc X N t p) (Bc Z N t q + Dc X Z N q p) := by
  have s := sum_le_params (Γ := Γ) (belowB X) (addBody (bZ Z) (dT X Z)) (pairT t p) (pairT t (pairT q p)) N
    (.allI (.impI (by
      simp only [shift_pairT]
      rw [inst2_addBody]
      exact le_congr (below_pt X _ _ _).eqSymm (congrAdd (bZ_at Z _ _ _ _).eqSymm (dT_at X Z _ _ _ _).eqSymm)
        (bit_cmp_below _ _ _))))
  exact le_congr (.eqRefl _) ((sum_add _ _ _ _).eqTrans (congrAdd (sum_bZ Z _ _ _ _) (sum_dT X Z _ _ _ _))) s

/-- `A_x(t) ≤ A_z(t) + D`. -/
theorem above_cmp (N t q p : PTm n) : Γ ⊢[PRAAx] le (Ac X N t p) (Ac Z N t q + Dc X Z N q p) := by
  have s := sum_le_params (Γ := Γ) (aboveB X) (addBody (aZ Z) (dT X Z)) (pairT t p) (pairT t (pairT q p)) N
    (.allI (.impI (by
      simp only [shift_pairT]
      rw [inst2_addBody]
      exact le_congr (above_pt X _ _ _).eqSymm (congrAdd (aZ_at Z _ _ _ _).eqSymm (dT_at X Z _ _ _ _).eqSymm)
        (bit_cmp_above _ _ _))))
  exact le_congr (.eqRefl _) ((sum_add _ _ _ _).eqTrans (congrAdd (sum_aZ Z _ _ _ _) (sum_dT X Z _ _ _ _))) s

/-! ## Fewer than half replaced: the median stays bounded -/

/-- The counting contradiction: `N ≤ C_x ≤ C_z + D`, `D ≤ r`, `2 C_z ≤ N` and `2r < N` are inconsistent. -/
theorem count_contra {N cx cz D r : PTm n} (φ : Fm PTm n) (h1 : Γ ⊢[PRAAx] le N cx) (h2 : Γ ⊢[PRAAx] le cx (cz + D))
    (h3 : Γ ⊢[PRAAx] le D r) (h4 : Γ ⊢[PRAAx] le (two * cz) N) (h5 : Γ ⊢[PRAAx] lt (two * r) N) : Γ ⊢[PRAAx] φ := by
  have f1 := natEq (eq_add_of_le h1); have f2 := natEq (eq_add_of_le h2); have f3 := natEq (eq_add_of_le h3)
  have f4 := natEq (eq_add_of_le h4); have f5 := natEq (eq_add_of_le h5)
  refine not_succ_le_self N φ (le_of_eq_add (d := two * monus cx N + two * monus (cz + D) cx + two * monus r D +
    monus N (two * cz) + monus N (succ (two * r))) ?_)
  apply deriveNat; ipra_simps
  linear_combination 2 * f1 + 2 * f2 + 2 * f3 + f4 + f5

/-- `thm:breakdown`, bounded half: if at most `r` coordinates of `x` are replaced (`D ≤ r`) and `2r < N`,
every balance median of the contaminated data lies in `[m, M]` for any bounds `m ≤ x_i ≤ M`. -/
theorem bounded {N t q p r m M : PTm n} (hD : Γ ⊢[PRAAx] le (Dc X Z N q p) r) (hr : Γ ⊢[PRAAx] lt (two * r) N)
    (hM : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ le (inst2 X (var 0) (Syn.shift p)) (Syn.shift M)))
    (hm : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ le (Syn.shift m) (inst2 X (var 0) (Syn.shift p))))
    (hmed : Γ ⊢[PRAAx] isMed Z N t q) : Γ ⊢[PRAAx] le m t ⋏ le t M := by
  refine .andI ?_ ?_
  · refine .orE (lt_or_le t m) ?_ Prf.hyp0
    let C := lt t m :: Γ
    have ht : C ⊢[PRAAx] lt t m := Prf.hyp0
    have all : C ⊢[PRAAx] le N (Ac X N t p) := by
      refine le_congr (sum_one N (pairT t p)) (.eqRefl _)
        (sum_le_params (one : PTm 2) (aboveB X) (pairT t p) (pairT t p) N (.allI (.impI ?_)))
      rw [inst2_one2, shift_pairT]
      have ht' := lt_shift ht
      exact le_congr (.eqRefl _) (above_pt X _ _ _).eqSymm
        (le_congr (.eqRefl _) (sg_lt (lt_of_lt_of_le ht'.wk (Prf.impE hm.wk.allOpen.wk Prf.hyp0))).eqSymm (le_refl _))
    exact count_contra _ all (above_cmp X Z N t q p) hD.wk (Prf.andE₂ hmed).wk hr.wk
  · refine .orE (lt_or_le M t) ?_ Prf.hyp0
    let C := lt M t :: Γ
    have ht : C ⊢[PRAAx] lt M t := Prf.hyp0
    have all : C ⊢[PRAAx] le N (Bc X N t p) := by
      refine le_congr (sum_one N (pairT t p)) (.eqRefl _)
        (sum_le_params (one : PTm 2) (belowB X) (pairT t p) (pairT t p) N (.allI (.impI ?_)))
      rw [inst2_one2, shift_pairT]
      have ht' := lt_shift ht
      exact le_congr (.eqRefl _) (below_pt X _ _ _).eqSymm
        (le_congr (.eqRefl _) (sg_lt (lt_of_le_of_lt (Prf.impE hM.wk.allOpen.wk Prf.hyp0) ht'.wk)).eqSymm (le_refl _))
    exact count_contra _ all (below_cmp X Z N t q p) hD.wk (Prf.andE₁ hmed).wk hr.wk

end Compare

/-! ## Half replaced: the median is driven -/

section Driven

variable (X : PTm 2)

/-- Replace the first `s` coordinates by `H`: `z_i = [i < s] H + (1 ∸ [i < s]) x_i`, over `0 = i`,
`1 = ⟨⟨s, H⟩, p⟩`. -/
def zB : PTm 2 := sg (monus (fstT (fstT (var 1))) (var 0)) * sndT (fstT (var 1)) +
  monus one (sg (monus (fstT (fstT (var 1))) (var 0))) * Syn.subst ![var 0, sndT (var 1)] X

theorem zB_eq (i P : PTm n) : inst2 (zB X) i P =
    sg (monus (fstT (fstT P)) i) * sndT (fstT P) + monus one (sg (monus (fstT (fstT P)) i)) * inst2 X i (sndT P) := by
  simp only [inst2, zB, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_data, subst_fstT, subst_sndT,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var]
  simp

theorem z_lt {i s H p : PTm n} (h : Γ ⊢[PRAAx] lt i s) :
    Γ ⊢[PRAAx] inst2 (zB X) i (pairT (pairT s H) p) ≐ H := by
  rw [zB_eq]
  have fs : Γ ⊢[PRAAx] fstT (fstT (pairT (pairT s H) p)) ≐ s := (congrFst (fst_pair _ _)).eqTrans (fst_pair _ _)
  have fH : Γ ⊢[PRAAx] sndT (fstT (pairT (pairT s H) p)) ≐ H := (congrSnd (fst_pair _ _)).eqTrans (snd_pair _ _)
  have g : Γ ⊢[PRAAx] sg (monus (fstT (fstT (pairT (pairT s H) p))) i) ≐ one :=
    (congrSg (congrMonus fs (.eqRefl _))).eqTrans (sg_lt h)
  have m := (congrMonus (.eqRefl one) g).eqTrans (monus_self _)
  refine (congrAdd (congrMul g fH) (congrMul m (.eqRefl _))).eqTrans ?_
  apply deriveNat; ipra_simps; ring

theorem z_ge {i s H p : PTm n} (h : Γ ⊢[PRAAx] le s i) :
    Γ ⊢[PRAAx] inst2 (zB X) i (pairT (pairT s H) p) ≐ inst2 X i p := by
  rw [zB_eq]
  have fs : Γ ⊢[PRAAx] fstT (fstT (pairT (pairT s H) p)) ≐ s := (congrFst (fst_pair _ _)).eqTrans (fst_pair _ _)
  have g : Γ ⊢[PRAAx] sg (monus (fstT (fstT (pairT (pairT s H) p))) i) ≐ zero :=
    (congrSg (congrMonus fs (.eqRefl _))).eqTrans (sg_le h)
  have m := (congrMonus (.eqRefl one) g).eqTrans (monus_zero _)
  have sp : Γ ⊢[PRAAx] inst2 X i (sndT (pairT (pairT s H) p)) ≐ inst2 X i p := congrInst2 X (.eqRefl _) (snd_pair _ _)
  refine (congrAdd (congrMul g (.eqRefl _)) (congrMul m sp)).eqTrans ?_
  apply deriveNat; ipra_simps; ring

/-- The replacement changes at most `s` coordinates. -/
theorem rep_count {N s H p : PTm n} (hs : Γ ⊢[PRAAx] le s N) :
    Γ ⊢[PRAAx] le (Dc X (zB X) N (pairT (pairT s H) p) p) s := by
  refine le_congr (.eqRefl _) (count_lt hs)
    (sum_le_params (dB X (zB X)) ltB (pairT (pairT (pairT s H) p) p) s N (.allI (.impI ?_)))
  simp only [shift_pairT]
  rw [inst2_ltB]
  refine le_congr (dB_at X (zB X) _ _ _).eqSymm (.eqRefl _) ?_
  refine .orE (lt_or_le (var 0) (Syn.shift s)) ?_ ?_
  · exact le_congr (.eqRefl _) (sg_lt Prf.hyp0).eqSymm (monus_one_le _ (eqb_le_one _ _))
  · exact le_zero_of ((congrMonus (.eqRefl _) (eqb_of_eq (z_ge X Prf.hyp0))).eqTrans (monus_self _))

/-- `thm:breakdown`, attained (odd pattern): if more than half the coordinates are replaced by `H`
(`N < 2s`), every balance median of the contaminated data is at least `H`. -/
theorem driven_above {N s H p t : PTm n} (hs : Γ ⊢[PRAAx] le s N) (h2 : Γ ⊢[PRAAx] lt N (two * s))
    (hmed : Γ ⊢[PRAAx] isMed (zB X) N t (pairT (pairT s H) p)) : Γ ⊢[PRAAx] le H t := by
  refine .orE (lt_or_le t H) ?_ Prf.hyp0
  let C := lt t H :: Γ
  have ht : C ⊢[PRAAx] lt t H := Prf.hyp0
  have ht' := lt_shift ht
  have cnt : C ⊢[PRAAx] le s (Ac (zB X) N t (pairT (pairT s H) p)) := by
    refine le_congr (count_lt hs.wk) (.eqRefl _)
      (sum_le_params ltB (aboveB (zB X)) s (pairT t (pairT (pairT s H) p)) N (.allI (.impI ?_)))
    simp only [shift_pairT]
    rw [inst2_ltB]
    refine le_congr (.eqRefl _) (above_pt (zB X) _ _ _).eqSymm ?_
    refine .orE (lt_or_le (var 0) (Syn.shift s)) ?_ ?_
    · exact le_congr (sg_lt Prf.hyp0).eqSymm (sg_lt (lt_congr (.eqRefl _) (z_lt X Prf.hyp0).eqSymm ht'.wk.wk)).eqSymm
        (le_refl _)
    · exact le_zero_of (sg_le Prf.hyp0)
  have f1 := natEq (eq_add_of_le cnt)
  have f2 := natEq (eq_add_of_le (Prf.andE₂ hmed).wk : C ⊢[PRAAx] _)
  have f3 := natEq (eq_add_of_le h2.wk : C ⊢[PRAAx] _)
  refine not_succ_le_self N _ (le_of_eq_add (d := monus (two * s) (succ N) +
    two * monus (Ac (zB X) N t (pairT (pairT s H) p)) s +
    monus N (two * Ac (zB X) N t (pairT (pairT s H) p))) ?_)
  apply deriveNat; ipra_simps
  linear_combination 2 * f1 + f2 + f3

/-- `thm:breakdown`, attained: if at least half the coordinates are replaced by `H` (`N ≤ 2s`) and
`H` bounds the data, then `H` itself is a balance median of the contaminated data. -/
theorem driven_med {N s H p : PTm n} (hs : Γ ⊢[PRAAx] le s N) (h2 : Γ ⊢[PRAAx] le N (two * s))
    (hH : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ le (inst2 X (var 0) (Syn.shift p)) (Syn.shift H))) :
    Γ ⊢[PRAAx] isMed (zB X) N H (pairT (pairT s H) p) := by
  have sB : Γ ⊢[PRAAx] le (Bc (zB X) N H (pairT (pairT s H) p)) (ap2 (sumF geB) N s) := by
    refine sum_le_params (belowB (zB X)) geB (pairT H (pairT (pairT s H) p)) s N (.allI (.impI ?_))
    simp only [shift_pairT]
    rw [inst2_geB]
    refine le_congr (below_pt (zB X) _ _ _).eqSymm (.eqRefl _) ?_
    refine .orE (lt_or_le (var 0) (Syn.shift s)) ?_ ?_
    · exact le_zero_of (sg_le (le_congr (.eqRefl _) (z_lt X Prf.hyp0).eqSymm (le_refl _)))
    · have h : (le (Syn.shift s) (var 0) :: lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx]
          lt (Syn.shift s) (succ (var 0)) := (succ_monus_succ _ _).eqTrans Prf.hyp0
      exact le_congr (.eqRefl _) (sg_lt h).eqSymm (sg_le_one _)
  have hA : Γ ⊢[PRAAx] Ac (zB X) N H (pairT (pairT s H) p) ≐ zero := by
    refine sum_zero_of_bounded _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT]
    refine (above_pt (zB X) _ _ _).eqTrans (sg_le ?_)
    refine .orE (lt_or_le (var 0) (Syn.shift s)) ?_ ?_
    · exact le_congr (z_lt X Prf.hyp0).eqSymm (.eqRefl _) (le_refl _)
    · exact le_congr (z_ge X Prf.hyp0).eqSymm (.eqRefl _) (Prf.impE hH.allOpen.wk.wk Prf.hyp1)
  have f1 := natEq (eq_add_of_le sB)
  have f2 := natEq (count_ge (Γ := Γ) hs)
  have f3 := natEq (eq_add_of_le h2)
  refine .andI (le_of_eq_add (d := two * monus (ap2 (sumF geB) N s) (Bc (zB X) N H (pairT (pairT s H) p)) +
    monus (two * s) N) ?_) (le_zero_of ((congrMul (.eqRefl _) hA).eqTrans (mul_zero _)))
  apply deriveNat; ipra_simps
  linear_combination 2 * f1 - 2 * f2 + f3

end Driven

end LeanProofs.IPRA.Probability.MedianBreakdown
