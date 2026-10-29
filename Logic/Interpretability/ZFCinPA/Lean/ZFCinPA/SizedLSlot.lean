import ZFCinPA.SizedLNumOK

/-!
# Bounded glue: slots of matching environments

`LGlue1.slot_MT` proves `𝗭𝗙 ⊢ SlotT (M_j) (N_a) (x = &a)` for every `a < j`:
every `M_j`-environment holds `&a` at the slot of the numeral `a`. The
induction is on `j`. The slot `0` of `M_{j+1}` compiles `slot0Template`. The
slot `a+1` of `M_{j+1}` compiles `slotSTemplate` against the shifted slot `a`
of `M_j`, the functionality of `M_j`, the two definitional premises and the
right half of `numOK a`. This module proves the bounded twin `slot_MT_leJ`.

* `tsubst_le_n`, `fvar_le`, `xT_le`: substitution of variable terms at any
  arity, and the level of `x = &a`, linear in `a`.
* `slot_MT_leJ`: for a target `J`, every placeholder up to `J` is at level
  `uS J`, so both templates compile at one fixed level. The slot statement at
  `(j, a)` is derived within `wSl J + 20 j`. Each step in `j` adds at most
  `12` levels above the shifted predecessor, the bounded `fun_MT` at `j`, and
  the bounded `numOK` at `a < j`.
-/
set_option autoImplicit false
noncomputable section

namespace LeanProofs.ZFCinPA.SizedLSlot

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic
open LeanProofs.ZFCinPA
open LeanProofs.BoundedPAConsistency.SizedDerivation LeanProofs.BoundedPAConsistency.SubstBound
open LeanProofs.ZFCinPA.SetCodeLevels LeanProofs.ZFCinPA.LevelDerivation
open LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.TemplateTranslateLevel
open LeanProofs.ZFCinPA.SizedCongruence (lt_lvB_succ le_of_add_eq)
open LeanProofs.ZFCinPA.SizedLPlumbing LeanProofs.ZFCinPA.SizedLGlue1 LeanProofs.ZFCinPA.SizedLNumOK
open LeanProofs.ZFCinPA.LGlue1 LeanProofs.ZFCinPA.LMatch LeanProofs.ZFCinPA.LGlueT
open LeanProofs.ZFCinPA.LMatchLevel LeanProofs.ZFCinPA.LDriverBase
open LeanProofs.ZFCinPA.NumeralOmega (numZeroS succRelS numChainQ numChainQ_zero numChainQ_succ
  numChainQ_val)
open LeanProofs.ZFCinPA.SizedOpenTemplateLeaves (cExpG)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local notation "Fm" => Bootstrapping.Formula V ℒₛₑₜ

/-! ## The level of `x = &a` -/

theorem uterm_isVar {t : V} (ht : IsUTerm ℒₛₑₜ t) : IsVarTerm t := by
  rcases term_var ht with ⟨z, rfl⟩ | ⟨x, rfl⟩
  · exact isVarTerm_bvar z
  · exact ⟨x, by simp [qqFvar, lt_succ_iff_le, le_pair_right], Or.inr rfl⟩

/-- `SizedCongruenceAtoms.tsubst_le` at any target arity. -/
theorem tsubst_le_n {k n : ℕ} (ψ : Bootstrapping.Semiformula V ℒₛₑₜ k)
    (v : Bootstrapping.SemitermVec V ℒₛₑₜ k n) {u c : V} (hψ : ψ.val ≤ lvB u) (hc : 1 ≤ c)
    (hv : ∀ i, (v i).val ≤ lvB c) : (ψ.subst v).val ≤ lvB (10 * (u + 1) + c) := by
  rw [Bootstrapping.Semiformula.val_substs]
  refine subst_level u ψ.val hψ ψ.isSemiformula.isUFormula c k n v.val hc
    (by simpa using v.isSemitermVec) (fun i hi => ?_) (fun i hi => ?_)
  · obtain ⟨j, rfl⟩ := eq_fin_of_lt_nat hi
    rw [Bootstrapping.SemitermVec.val_nth_eq]; exact hv j
  · obtain ⟨j, rfl⟩ := eq_fin_of_lt_nat hi
    rw [Bootstrapping.SemitermVec.val_nth_eq]
    exact uterm_isVar (v j).isSemiterm.isUTerm

theorem fvar_le (a : V) : (^&a : V) ≤ lvB (a + 4) := by
  show ⟪1, a⟫ + 1 ≤ _
  have h2 : (2 : V) ≤ a + 2 := le_add_self
  exact le_trans (pair_lvB h2 (tag_le_lvB (k := 1) (by norm_num) h2)
    (lift_lvB (le_lvB_self a) le_self_add)) (lvB_mono (le_of_eq (by ring)))

/-- The level constant of `x = y`. -/
def Ce : V := 10 * ((⌜LGlueT2.eq2S⌝ : SF V 2).val + 1)

theorem xT_le (a : V) : (xT a).val ≤ lvB (Ce + a + 4) := by
  rw [xT_eq]
  have hc : (1 : V) ≤ a + 4 := le_trans (by norm_num) le_add_self
  refine le_trans (tsubst_le_n _ _ (le_lvB_self _) hc (fun i => ?_))
    (lvB_mono (le_of_eq (by unfold Ce; ring)))
  match i with
  | 0 =>
      have : (^#0 : V) ≤ lvB (a + 4) :=
        le_trans (show (^#0 : V) ≤ 4 by simp [qqBvar, pair] <;> norm_num) (four_le_lvB hc)
      simpa using this
  | 1 => simpa using fvar_le a

/-! ## Uniform levels -/

/-- The placeholder level of the slot induction up to `J`. -/
def uS (J : V) : V := uM J + uN J + Ce + J + 6

theorem uM_le_U (J : V) : uM J ≤ uS J := le_of_add_eq (y := uN J + Ce + J + 6) (by unfold uS; ring)

theorem uN_le_U (J : V) : uN J ≤ uS J := le_of_add_eq (y := uM J + Ce + J + 6) (by unfold uS; ring)

theorem two_le_U (J : V) : (2 : V) ≤ uS J := le_trans (two_le_uM J) (uM_le_U J)

theorem xT_le' {a J : V} (h : a ≤ J) : (xT a).val ≤ lvB (uS J) :=
  lift_lvB (xT_le a) (le_trans (_root_.add_le_add (_root_.add_le_add le_rfl h) le_rfl)
    (le_of_add_eq (y := uM J + uN J + 2) (by unfold uS; ring)))

/-- An eight-placeholder tuple at level `u`. -/
theorem K8_le {u : V} {a b c d e f g h : SF V 1} (ha : a.val ≤ lvB u) (hb : b.val ≤ lvB u)
    (hc : c.val ≤ lvB u) (hd : d.val ≤ lvB u) (he : e.val ≤ lvB u) (hf : f.val ≤ lvB u)
    (hg : g.val ≤ lvB u) (hh : h.val ≤ lvB u) : ∀ k, (K8 a b c d e f g h k).val ≤ lvB u := by
  intro k
  match k with
  | 0 => exact ha
  | 1 => exact hb
  | 2 => exact hc
  | 3 => exact hd
  | 4 => exact he
  | 5 => exact hf
  | 6 => exact hg
  | 7 => exact hh

/-! ## The translated slot templates -/

/-- The placeholder tuple of slot zero. -/
def Kz (j : V) : (k : Fin 8) → SF V (arG k) :=
  K8 (MT j).shift (MT (j + 1)) zT (numChainQ 0) ⊤ ⊤ ⊤ ⊤

/-- The placeholder tuple of a slot step. -/
def Kp (j a : V) : (k : Fin 8) → SF V (arG k) :=
  K8 (MT j).shift (MT (j + 1)) zT (numChainQ a) (xT (a + 1)) (numChainQ (a + 1)) ⊤ ⊤

theorem tr_slot0T (j : V) :
    translateFormula (Kz j) (Rewriting.emb slot0Template) =
      ((∀⁰ (∼(MT j).shift ⋎ (⌜funcS⌝ : SF V 1))) ⋏
        ((∀⁰ (MT (j + 1) 🡘 MpT (MT j).shift zT)) ⋏ (∀⁰ (numChainQ 0 🡘 ⌜numZeroS⌝)))) 🡒
        SlotT (MT (j + 1)) (numChainQ 0) zT := by
  simp only [slot0Template, LogicalConnective.HomClass.map_imply,
    LogicalConnective.HomClass.map_and, translateFormula_imp, tr_andG, tr_funM, tr_mpDef,
    tr_zeroDef, tr_slotS]
  rfl

theorem tr_slotST (j a : V) :
    translateFormula (Kp j a) (Rewriting.emb slotSTemplate) =
      (SlotT (MT j).shift (numChainQ a) (xT (a + 1)) ⋏
        ((∀⁰ (∼(MT j).shift ⋎ (⌜funcS⌝ : SF V 1))) ⋏
          ((∀⁰ (MT (j + 1) 🡘 MpT (MT j).shift zT)) ⋏
            ((∀⁰ (numChainQ (a + 1) 🡘 SuccT (numChainQ a))) ⋏
              (∀⁰ (∼(numChainQ a) ⋎ ⌜LStepAtom.natP⌝)))))) 🡒
        SlotT (MT (j + 1)) (numChainQ (a + 1)) (xT (a + 1)) := by
  simp only [slotSTemplate, LogicalConnective.HomClass.map_imply,
    LogicalConnective.HomClass.map_and, translateFormula_imp, tr_andG, tr_funM, tr_mpDef,
    tr_succDef, tr_natN, tr_slotS]
  rfl

/-- The translation constant of the two slot templates. -/
def tSl : ℕ := tA (Rewriting.emb slot0Template : Proposition GL) +
  tA (Rewriting.emb slotSTemplate : Proposition GL)

/-- The member level of the slot induction. -/
def mSl (J : V) : V := (tSl : V) * (uS J + 1)

/-- The compile levels of the two slot templates at `uS J`. -/
def cZ (J : V) : V := cExpG (tmA slot0Template_provable) (tmB slot0Template_provable) (uS J) +
  (tmK slot0Template_provable : ℕ) + 1

def cP (J : V) : V := cExpG (tmA slotSTemplate_provable) (tmB slotSTemplate_provable) (uS J) +
  (tmK slotSTemplate_provable : ℕ) + 1

/-- The base level of the bounded slot induction. -/
def wSl (J : V) : V := wF J + wN J + cZ J + cP J + 1000 * (mSl J + 1) + 100 * uS J + 300

theorem trS_le {J : V} (σ : Sentence GL) (hσ : tA (Rewriting.emb σ : Proposition GL) ≤ tSl)
    (Ks : (i : Fin 8) → SF V (arG i)) (hK : ∀ i, (Ks i).val ≤ lvB (uS J)) :
    (translateFormula Ks (Rewriting.emb σ)).val ≤ lvB (mSl J) :=
  lift_lvB (translate_level _ (uS J) Ks hK)
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hσ) (Arithmetic.zero_le _))

theorem wSl_4 (J : V) : (4 : V) ≤ wSl J := le_of_add_eq
  (y := wF J + wN J + cZ J + cP J + 1000 * (mSl J + 1) + 100 * uS J + 296) (by unfold wSl; ring)

theorem wSl_m (J : V) : 10 * (mSl J + 1) + 1 ≤ wSl J := le_of_add_eq
  (y := wF J + wN J + cZ J + cP J + 990 * mSl J + 100 * uS J + 1289) (by unfold wSl; ring)

theorem wSl_u (J : V) : 100 * uS J + 238 ≤ wSl J := le_of_add_eq
  (y := wF J + wN J + cZ J + cP J + 1000 * (mSl J + 1) + 62) (by unfold wSl; ring)

theorem wSl_f (J : V) : wF J ≤ wSl J := le_of_add_eq
  (y := wN J + cZ J + cP J + 1000 * (mSl J + 1) + 100 * uS J + 300) (by unfold wSl; ring)

theorem wSl_n (J : V) : wN J + 3 ≤ wSl J := le_of_add_eq
  (y := wF J + cZ J + cP J + 1000 * (mSl J + 1) + 100 * uS J + 297) (by unfold wSl; ring)

theorem wSl_z (J : V) : cZ J ≤ wSl J := le_of_add_eq
  (y := wF J + wN J + cP J + 1000 * (mSl J + 1) + 100 * uS J + 300) (by unfold wSl; ring)

theorem wSl_s (J : V) : cP J ≤ wSl J := le_of_add_eq
  (y := wF J + wN J + cZ J + 1000 * (mSl J + 1) + 100 * uS J + 300) (by unfold wSl; ring)

theorem add2 (x : V) : x ≤ x + 1 + 1 := le_of_add_eq (y := 2) (by ring)

/-! ## The bounded induction -/

set_option maxHeartbeats 8000000 in
/-- **Slot zero, bounded.** -/
theorem slot_zero_le {J j : V} (hjJ : j + 1 ≤ J) :
    DLv 𝗭𝗙 (insert (SlotT (MT (j + 1)) (numChainQ 0) (xT 0)).val ∅) (wSl J + 20 * (j + 1)) := by
  have hu2 := two_le_U J
  have hj : j ≤ J := le_trans le_self_add hjJ
  set w := wSl J + 20 * j with hw
  have hW : wSl J ≤ w := le_self_add
  have hw4 : (4 : V) ≤ w := le_trans (wSl_4 J) hW
  have hmw : 10 * (mSl J + 1) + 1 ≤ w := le_trans (wSl_m J) hW
  have huw : 100 * uS J + 238 ≤ w := le_trans (wSl_u J) hW
  have h10j : 10 * j ≤ 20 * j := mul_le_mul_of_nonneg_right (by norm_num) (Arithmetic.zero_le _)
  -- functionality of `M_j`
  have f0 := fun_MT_leJ hj
  rw [← funT_val] at f0
  have f0w := f0.mono (show wF J + 10 * j ≤ w by
    rw [hw]; exact _root_.add_le_add (wSl_f J) h10j)
  -- the definitional premise of `M_{j+1}`
  have pm := (dall_iff (MT (j + 1)) (lift_lvB (mT_le hjJ) (uM_le_U J)) hu2).mono
    (le_trans huw (le_self_add : w ≤ w + 1))
  rw [show (∀⁰ (MT (j + 1) 🡘 MT (j + 1)) : Fm) = ∀⁰ (MT (j + 1) 🡘 MpT (MT j).shift zT) by
    rw [← MT_succ]] at pm
  have hK := K8_le (lift_lvB (mTs_le hj) (uM_le_U J)) (lift_lvB (mT_le hjJ) (uM_le_U J))
    (lift_lvB (zT_le' J) (uM_le_U J)) (lift_lvB (numQ_le (Arithmetic.zero_le J)) (uN_le_U J))
    (top_le hu2) (top_le hu2) (top_le hu2) (top_le hu2)
  have lt := trS_le slot0Template (by unfold tSl; omega) (Kz j) hK
  have hc := compiledLe (by decide) slot0Template_provable (Kz j) hu2 hK
  rw [tr_slot0T] at lt hc
  have hA := imp_ante_le lt
  have hfs : (∀⁰ (∼(MT j) ⋎ (⌜funcS⌝ : SF V 1)) : Fm).shift.val < lvB w := by
    rw [funT_shift]
    exact lt_of_lt_of_le (lt_lvB_succ (and_left_le hA)) (lvB_mono hmw)
  have pf := dshift hw4 hfs f0w
  rw [funT_shift] at pf
  have pz := (dall_iff (⌜numZeroS⌝ : SF V 1)
    (lift_lvB (zeroQ_le J) (uN_le_U J)) hu2).mono (le_trans huw (le_self_add : w ≤ w + 1))
  rw [show (∀⁰ ((⌜numZeroS⌝ : SF V 1) 🡘 ⌜numZeroS⌝) : Fm) =
      ∀⁰ (numChainQ 0 🡘 ⌜numZeroS⌝) by rw [numChainQ_zero]] at pz
  have c23 := dk_introL (le_trans hw4 le_self_add) (and_right_le hA)
    (le_trans hmw le_self_add) pm pz
  have c123 := dk_introL (le_trans hw4 (le_trans le_self_add (add2 _))) hA
    (le_trans hmw (le_trans le_self_add (add2 _))) (pf.mono (add2 _)) c23
  have d := dmdpL (le_trans hw4 (le_trans le_self_add (le_trans (add2 _) (add2 _)))) lt
    (le_trans hmw (le_trans le_self_add (le_trans (add2 _) (add2 _))))
    (hc.mono (show cZ J ≤ w + 1 + 1 + 1 + 1 + 1 from le_trans (le_trans (wSl_z J) hW)
      (le_trans le_self_add (le_trans (add2 _) (add2 _))))) c123
  rw [xT_zero]
  refine d.mono ?_
  rw [hw]
  exact le_of_add_eq (y := 12) (by ring)

set_option maxHeartbeats 8000000 in
/-- **The slot step, bounded.** -/
theorem slot_succ_le {J j a : V} (hjJ : j + 1 ≤ J) (haj : a < j)
    (s0 : DLv 𝗭𝗙 (insert (SlotT (MT j) (numChainQ a) (xT a)).val ∅) (wSl J + 20 * j)) :
    DLv 𝗭𝗙 (insert (SlotT (MT (j + 1)) (numChainQ (a + 1)) (xT (a + 1))).val ∅)
      (wSl J + 20 * (j + 1)) := by
  have hu2 := two_le_U J
  have hj : j ≤ J := le_trans le_self_add hjJ
  set w := wSl J + 20 * j with hw
  have hW : wSl J ≤ w := le_self_add
  have hw4 : (4 : V) ≤ w := le_trans (wSl_4 J) hW
  have hmw : 10 * (mSl J + 1) + 1 ≤ w := le_trans (wSl_m J) hW
  have huw : 100 * uS J + 238 ≤ w := le_trans (wSl_u J) hW
  have h10j : 10 * j ≤ 20 * j := mul_le_mul_of_nonneg_right (by norm_num) (Arithmetic.zero_le _)
  -- functionality of `M_j`
  have f0 := fun_MT_leJ hj
  rw [← funT_val] at f0
  have f0w := f0.mono (show wF J + 10 * j ≤ w by
    rw [hw]; exact _root_.add_le_add (wSl_f J) h10j)
  -- the definitional premise of `M_{j+1}`
  have pm := (dall_iff (MT (j + 1)) (lift_lvB (mT_le hjJ) (uM_le_U J)) hu2).mono
    (le_trans huw (le_self_add : w ≤ w + 1))
  rw [show (∀⁰ (MT (j + 1) 🡘 MT (j + 1)) : Fm) = ∀⁰ (MT (j + 1) 🡘 MpT (MT j).shift zT) by
    rw [← MT_succ]] at pm
  have ha1 : a + 1 ≤ J := le_trans (lt_iff_succ_le.mp haj) hj
  have haJ : a ≤ J := le_trans le_self_add ha1
  have hK := K8_le (lift_lvB (mTs_le hj) (uM_le_U J)) (lift_lvB (mT_le hjJ) (uM_le_U J))
    (lift_lvB (zT_le' J) (uM_le_U J)) (lift_lvB (numQ_le haJ) (uN_le_U J)) (xT_le' ha1)
    (lift_lvB (numQ_le ha1) (uN_le_U J)) (top_le hu2) (top_le hu2)
  have lt := trS_le slotSTemplate (by unfold tSl; omega) (Kp j a) hK
  have hc := compiledLe (by decide) slotSTemplate_provable (Kp j a) hu2 hK
  rw [tr_slotST] at lt hc
  have hA := imp_ante_le lt
  have hA2 := and_right_le hA
  have hA3 := and_right_le hA2
  have hA4 := and_right_le hA3
  -- the shifted predecessor slot
  have hss : (SlotT (MT j) (numChainQ a) (xT a)).shift.val < lvB w := by
    rw [slotT_shift, numChainQ_shiftT, xT_shift]
    exact lt_of_lt_of_le (lt_lvB_succ (and_left_le hA)) (lvB_mono hmw)
  have ps := dshift hw4 hss s0
  rw [slotT_shift, numChainQ_shiftT, xT_shift] at ps
  -- functionality, shifted
  have hfs : (∀⁰ (∼(MT j) ⋎ (⌜funcS⌝ : SF V 1)) : Fm).shift.val < lvB w := by
    rw [funT_shift]
    exact lt_of_lt_of_le (lt_lvB_succ (and_left_le hA2)) (lvB_mono hmw)
  have pf := dshift hw4 hfs f0w
  rw [funT_shift] at pf
  -- the successor numeral premise
  have pd := (dall_iff (numChainQ (a + 1)) (lift_lvB (numQ_le ha1) (uN_le_U J)) hu2).mono
    (le_trans huw (le_self_add : w ≤ w + 1))
  rw [show (∀⁰ (numChainQ (a + 1) 🡘 numChainQ (a + 1)) : Fm) =
      ∀⁰ (numChainQ (a + 1) 🡘 SuccT (numChainQ a)) by rw [succT_numChain]] at pd
  -- the numeral's members are natural numbers
  have pn := (numOK_right_leJ haJ).mono (show wN J + 10 * a + 1 + 1 + 1 ≤ w + 1 by
    rw [hw, show wN J + 10 * a + 1 + 1 + 1 = (wN J + 3) + 10 * a by ring]
    refine le_trans (_root_.add_le_add (wSl_n J) ?_) le_self_add
    exact le_trans (mul_le_mul_of_nonneg_left haj.le (by norm_num)) h10j)
  -- the conjunction
  have c4 := dk_introL (le_trans hw4 le_self_add) hA4 (le_trans hmw le_self_add) pd pn
  have c3 := dk_introL (le_trans hw4 (le_trans le_self_add (add2 _))) hA3
    (le_trans hmw (le_trans le_self_add (add2 _))) (pm.mono (add2 _)) c4
  have c2 := dk_introL (le_trans hw4 (le_trans le_self_add (le_trans (add2 _) (add2 _)))) hA2
    (le_trans hmw (le_trans le_self_add (le_trans (add2 _) (add2 _))))
    (pf.mono (le_trans (add2 _) (add2 _))) c3
  have c1 := dk_introL (le_trans hw4 (le_trans le_self_add
      (le_trans (add2 _) (le_trans (add2 _) (add2 _))))) hA
    (le_trans hmw (le_trans le_self_add (le_trans (add2 _) (le_trans (add2 _) (add2 _)))))
    (ps.mono (le_trans (add2 _) (le_trans (add2 _) (add2 _)))) c2
  have up8 : w ≤ w + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 :=
    le_of_add_eq (y := 9) (by ring)
  have d := dmdpL (le_trans hw4 up8) lt (le_trans hmw up8)
    (hc.mono (show cP J ≤ w + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from
      le_trans (le_trans (wSl_s J) hW) up8)) c1
  refine d.mono ?_
  rw [hw]
  exact le_of_add_eq (y := 8) (by ring)

/-- The slot sequent along the diagonal `j = b + 1 + d`, on codes. -/
def diagSeq (d b : V) : V := insert (slotVal (b + 1 + d) b) ∅

instance diagSeq_definable (d : V) : 𝚺₁-Function₁ (diagSeq d) := by
  have hs : 𝚺₁.DefinableFunction (fun v : Fin 1 → V ↦ slotVal (v 0 + 1 + d) (v 0)) :=
    HierarchySymbol.DefinableFunction₂.comp (F := slotVal) (by definability)
      (HierarchySymbol.DefinableFunction.var 0)
  exact HierarchySymbol.DefinableFunction₂.comp (F := (insert : V → V → V)) hs
    (HierarchySymbol.DefinableFunction.const _)

set_option maxHeartbeats 8000000 in
/-- **A matching environment holds `&a` at the slot of the numeral `a`, bounded**,
for every `a < j ≤ J`, at the compile level of `J`. The induction runs along the
diagonal `j = a + 1 + d` for each fixed `d`, matching the recursion of
`LGlue1.slot_MT`: the slot `a + 1` of `M_{j+1}` is built from the slot `a` of
`M_j`. -/
theorem slot_MT_leJ {J : V} : ∀ j ≤ J, ∀ a < j,
    DLv 𝗭𝗙 (insert (SlotT (MT j) (numChainQ a) (xT a)).val ∅) (wSl J + 20 * j) := by
  obtain ⟨W0, hW0⟩ : ∃ W0 : V, W0 = wSl J := ⟨_, rfl⟩
  intro j hj a ha
  obtain ⟨d, rfl⟩ := exists_add_of_le (lt_iff_succ_le.mp ha)
  suffices key : ∀ b : V, b + 1 + d ≤ J → DLv 𝗭𝗙 (diagSeq d b) (W0 + 20 * (b + 1 + d)) by
    have := key a hj
    unfold diagSeq at this
    rw [← slotT_val, hW0] at this
    exact this
  intro b
  induction b using ISigma1.sigma1_succ_induction
  · simp only [DLv, DerivableLe, lvB]
    definability
  · intro h
    unfold diagSeq
    rw [show (0 : V) + 1 + d = d + 1 by ring] at h ⊢
    rw [← slotT_val, hW0]
    exact slot_zero_le h
  · case succ b ih =>
    intro h
    have hj' : b + 1 + d ≤ J :=
      le_trans (show b + 1 + d ≤ b + 1 + 1 + d from le_of_add_eq (y := 1) (by ring)) h
    have s0 := ih hj'
    unfold diagSeq at s0 ⊢
    rw [← slotT_val, hW0] at s0
    rw [show b + 1 + 1 + d = (b + 1 + d) + 1 by ring] at h ⊢
    rw [← slotT_val, hW0]
    exact slot_succ_le h (lt_iff_succ_le.mpr le_self_add) s0

/-- **A matching environment holds `&a` at the slot of the numeral `a`, bounded.** -/
theorem slot_MT_le (J a : V) (ha : a < J) :
    DLv 𝗭𝗙 (insert (SlotT (MT J) (numChainQ a) (xT a)).val ∅) (wSl J + 20 * J) :=
  slot_MT_leJ J le_rfl a ha

end LeanProofs.ZFCinPA.SizedLSlot
