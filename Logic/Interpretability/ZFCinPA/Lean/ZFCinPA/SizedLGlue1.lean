import ZFCinPA.SizedLPlumbing
import ZFCinPA.LGlue1
import ZFCinPA.LMatchLevel

/-!
# Bounded glue: functional matching environments

`LGlue1.fun_MT` proves `𝗭𝗙 ⊢ ∀t (M_j t → t functional)` by induction on
`j`. Each step shifts the previous proof, conjoins it with the definitional
premise `∀(M_{j+1} ↔ Mp(M_j))`, and applies modus ponens against the
compiled glue template `funTemplate`. This module proves the bounded twin
`fun_MT_le` on the level scale `DLv`.

* `dshift`, `dk_intro`, `dmdp`, `dall_em`, `dall_iff`: bounded typed
  combinators (shift, `∧`-introduction, modus ponens, `∀(¬A ∨ A)`,
  `∀(A ↔ A)`), each a fixed number of primitive rules.
* `fun_MT_le`: for a target `J`, the induction runs at the single compile
  level of `J`, since every placeholder up to `J` is at level
  `U J = Cm·2^(4J) + Cm + 2`. Each step then adds `10` levels.
-/
set_option autoImplicit false
noncomputable section

namespace LeanProofs.ZFCinPA.SizedLGlue1

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic
open LeanProofs.ZFCinPA
open LeanProofs.BoundedPAConsistency.SizedDerivation
open LeanProofs.ZFCinPA.SetCodeLevels LeanProofs.ZFCinPA.LevelDerivation
open LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.TemplateTranslateLevel
open LeanProofs.ZFCinPA.SizedCongruence (lt_lvB_succ le_of_add_eq fvar0_le)
open LeanProofs.ZFCinPA.SizedCongruenceAtoms (tsubst_le)
open LeanProofs.ZFCinPA.SizedPlaceholderCongruence (conn_le lt_lvB_of)
open LeanProofs.ZFCinPA.SizedLPlumbing
open LeanProofs.ZFCinPA.LGlue1 LeanProofs.ZFCinPA.LMatch LeanProofs.ZFCinPA.LGlueT
open LeanProofs.ZFCinPA.LMatchLevel LeanProofs.ZFCinPA.LDriverBase
open LeanProofs.ZFCinPA.SizedOpenTemplateLeaves (cExpG)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local notation "Fm" => Bootstrapping.Formula V ℒₛₑₜ

theorem fset1 (φ : Fm) : IsFormulaSet ℒₛₑₜ (insert φ.val (∅ : V)) :=
  SizedTemplateAxioms.singleton_formulaSet φ

theorem fins (φ : Fm) {s : V} (hs : IsFormulaSet ℒₛₑₜ s) : IsFormulaSet ℒₛₑₜ (insert φ.val s) :=
  formulaSet_insert hs

/-! ## Bounded typed combinators -/

/-- Shifting a proof costs one level. -/
theorem dshift {φ : Fm} {w : V} (hw : 4 ≤ w) (h1 : φ.shift.val < lvB w)
    (d : DLv 𝗭𝗙 (insert φ.val ∅) w) : DLv 𝗭𝗙 (insert φ.shift.val ∅) (w + 1) := by
  have hS : setShift ℒₛₑₜ (insert φ.val (∅ : V)) = insert φ.shift.val ∅ := by
    rw [mem_setShift_insert, Bootstrapping.Semiformula.val_shift]
    congr 1
    exact mem_ext fun y => by simp [mem_setShift_iff]
  have := DerivableLe.shift (four_le_lvB' hw) (by rw [hS]; exact ((SeqLt.empty w).insert h1).le) d
  rw [hS] at this
  exact this.mono (step_le hw)

/-- `∧`-introduction costs two levels. -/
theorem dk_intro {φ ψ : Fm} {w : V} (hw : 4 ≤ w) (h : (φ ⋏ ψ).val < lvB w)
    (d1 : DLv 𝗭𝗙 (insert φ.val ∅) w) (d2 : DLv 𝗭𝗙 (insert ψ.val ∅) w) :
    DLv 𝗭𝗙 (insert (φ ⋏ ψ).val ∅) (w + 1 + 1) := by
  have hφ : φ.val < lvB w := lt_trans (lt_K!_left _ _) h
  have hψ : ψ.val < lvB w := lt_trans (lt_K!_right _ _) h
  have hS := (SeqLt.empty w).insert h
  have hsub : ∀ {x : V}, insert x (∅ : V) ⊆ insert x (insert (φ ⋏ ψ).val ∅) := fun {x} =>
    insert_subset_insert_of_subset _ (by intro z hz; simp at hz)
  exact DLv.and_m (le_trans hw le_self_add) (hS.mono le_self_add) (p := φ.val) (q := ψ.val)
    (by simp) (DLv.wk hw (hS.insert hφ) (fins φ (fset1 _)) hsub d1)
    (DLv.wk hw (hS.insert hψ) (fins ψ (fset1 _)) hsub d2)

/-- Modus ponens costs three levels. -/
theorem dmdp {φ ψ : Fm} {w : V} (hw : 4 ≤ w) (hn : (φ ⋏ ∼ψ).val < lvB w)
    (hi : (φ 🡒 ψ).val < lvB w) (d1 : DLv 𝗭𝗙 (insert (φ 🡒 ψ).val ∅) w)
    (d2 : DLv 𝗭𝗙 (insert φ.val ∅) w) : DLv 𝗭𝗙 (insert ψ.val ∅) (w + 1 + 1 + 1) := by
  have himp : (φ 🡒 ψ).val = (∼φ).val ^⋎ ψ.val := by
    rw [Bootstrapping.Semiformula.imp_def, Bootstrapping.Semiformula.val_or]
  have hψ : ψ.val < lvB w := lt_trans (himp ▸ lt_or_right _ _) hi
  have hφ : φ.val < lvB w := lt_trans (lt_K!_left _ _) hn
  have hnψ : (∼ψ).val < lvB w := lt_trans (lt_K!_right _ _) hn
  have hneg : neg ℒₛₑₜ (φ 🡒 ψ).val = (φ ⋏ ∼ψ).val := by
    rw [← Bootstrapping.Semiformula.val_neg]; congr 1; simp [Bootstrapping.Semiformula.imp_def]
  set S := insert ψ.val (∅ : V) with hSd
  have lS : SeqLt S w := (SeqLt.empty w).insert hψ
  have fS : IsFormulaSet ℒₛₑₜ S := fset1 ψ
  set B := insert (φ ⋏ ∼ψ).val S with hBd
  have lB : SeqLt B w := lS.insert hn
  have fB : IsFormulaSet ℒₛₑₜ B := fins _ fS
  have up : ∀ k : V, 4 ≤ w + k := fun k => le_trans hw le_self_add
  have dA : DLv 𝗭𝗙 (insert (φ 🡒 ψ).val S) (w + 1) :=
    DLv.wk hw (lS.insert hi) (fins _ fS) (insert_subset_insert_of_subset _ (by intro z hz; simp at hz)) d1
  have dL : DLv 𝗭𝗙 (insert φ.val B) (w + 1) :=
    DLv.wk hw (lB.insert hφ) (fins _ fB) (insert_subset_insert_of_subset _ (by intro z hz; simp at hz)) d2
  have dR : DLv 𝗭𝗙 (insert (∼ψ).val B) (w + 1) := by
    refine DLv.em hw (lB.insert hnψ) (fins _ fB) ψ.val (by simp [hBd, hSd]) ?_
    rw [← Bootstrapping.Semiformula.val_neg]; simp
  have dB : DLv 𝗭𝗙 B (w + 1 + 1) :=
    DLv.and_m (up 1) (lB.mono le_self_add) (p := φ.val) (q := (∼ψ).val) (by simp [hBd]) dL dR
  have := DLv.cut (le_trans hw (le_trans le_self_add le_self_add) : (4 : V) ≤ w + 1 + 1)
    (lS.mono (le_trans le_self_add le_self_add)) (φ 🡒 ψ).val
    (lt_of_lt_of_le hi (lvB_mono (le_trans le_self_add le_self_add)))
    (dA.mono (le_self_add : w + 1 ≤ w + 1 + 1))
    (by rw [hneg]; exact dB)
  exact this

/-! ## `∀(¬A ∨ A)` and `∀(A ↔ A)` -/

theorem free_iff (A : Bootstrapping.Semiformula V ℒₛₑₜ 1) : (A 🡘 A).free = A.free 🡘 A.free := by
  simp [Bootstrapping.Semiformula.free]

theorem free_em (A : Bootstrapping.Semiformula V ℒₛₑₜ 1) : (∼A ⋎ A).free = ∼A.free ⋎ A.free := by
  simp [Bootstrapping.Semiformula.free]

theorem freeA_le (A : Bootstrapping.Semiformula V ℒₛₑₜ 1) {a : V} (ha : A.val ≤ lvB a) :
    A.free.val ≤ lvB (10 * (a + 1 + 1) + 1) :=
  tsubst_le A.shift ![Bootstrapping.Semiterm.fvar 0]
    (by rw [Bootstrapping.Semiformula.val_shift]; exact shift_level ha) le_rfl
    (fun i => by rcases Fin.eq_zero i with rfl; simpa using fvar0_le (1 : V) le_rfl)

theorem shift_all_le {x b : V} (hx : x ≤ lvB b) : shift ℒₛₑₜ x ≤ lvB (b + 1) := shift_level hx

set_option maxHeartbeats 1000000 in
/-- **`∀(¬A ∨ A)`, bounded.** -/
theorem dall_em (A : Bootstrapping.Semiformula V ℒₛₑₜ 1) {a : V} (ha : A.val ≤ lvB a)
    (h2 : 2 ≤ a) : DLv 𝗭𝗙 (insert (∀⁰ (∼A ⋎ A)).val ∅) (100 * a + 233) := by
  set X := A.free with hX
  have lX : X.val ≤ lvB (10 * (a + 1 + 1) + 1) := freeA_le A ha
  set nb : V := 10 * (10 * (a + 1 + 1) + 1 + 1) with hnb
  have lnX : (∼X).val ≤ lvB nb := by
    rw [Bootstrapping.Semiformula.val_neg]; exact neg_level _ _ lX X.isSemiformula.isUFormula
  have hnb2 : (2 : V) ≤ nb := le_of_add_eq (y := 100 * a + 218) (by rw [hnb]; ring)
  have hxnb : 10 * (a + 1 + 1) + 1 ≤ nb := le_of_add_eq (y := 90 * a + 199) (by rw [hnb]; ring)
  have lP : (∼X ⋎ X).val ≤ lvB (nb + 4) := by
    rw [Bootstrapping.Semiformula.val_or]
    exact conn_le (tag := 5) hnb2 (by norm_num) lnX (lift_lvB lX hxnb)
  -- the closed formula
  have lnA : (∼A).val ≤ lvB (10 * (a + 1)) := by
    rw [Bootstrapping.Semiformula.val_neg]; exact neg_level _ _ ha A.isSemiformula.isUFormula
  have h2' : (2 : V) ≤ 10 * (a + 1) := le_of_add_eq (y := 10 * a + 8) (by ring)
  have lQ : (∼A ⋎ A).val ≤ lvB (10 * (a + 1) + 4) := by
    rw [Bootstrapping.Semiformula.val_or]
    exact conn_le (tag := 5) h2' (by norm_num) lnA (lift_lvB ha (le_of_add_eq (y := 9 * a + 10) (by ring)))
  have lF : (∀⁰ (∼A ⋎ A)).val ≤ lvB (10 * (a + 1) + 4 + 2) := by
    rw [Bootstrapping.Semiformula.val_all]
    exact pair_lvB (le_trans h2' le_self_add) (tag_le_lvB (k := 6) (by norm_num) (le_trans h2' le_self_add)) lQ
  set L : V := 100 * a + 229 with hL
  have hlt : ∀ {x m : V}, x ≤ lvB m → m ≤ 100 * a + 228 → x < lvB L := fun hx hm =>
    lt_of_lt_of_le (lt_lvB_succ (lift_lvB hx hm)) (lvB_mono (le_of_eq (by rw [hL]; ring)))
  have mP := hlt lP (le_of_add_eq (y := 4) (by rw [hnb]; ring))
  have mX := hlt lX (le_of_add_eq (y := 90 * a + 207) (by ring))
  have mnX := hlt lnX (le_of_add_eq (y := 8) (by rw [hnb]; ring))
  have mF := hlt lF (le_of_add_eq (y := 90 * a + 212) (by ring))
  have mFs := hlt (shift_all_le lF) (le_of_add_eq (y := 90 * a + 211) (by ring))
  have hL4 : (4 : V) ≤ L := le_of_add_eq (y := 100 * a + 225) (by rw [hL]; ring)
  -- the derivation
  have hS : setShift ℒₛₑₜ (insert (∀⁰ (∼A ⋎ A)).val (∅ : V)) =
      insert (shift ℒₛₑₜ (∀⁰ (∼A ⋎ A)).val) ∅ := by
    rw [mem_setShift_insert]; congr 1; exact mem_ext fun y => by simp [mem_setShift_iff]
  set S₀ := insert (∼X ⋎ X).val (setShift ℒₛₑₜ (insert (∀⁰ (∼A ⋎ A)).val (∅ : V))) with hS₀
  have fsh : IsFormula ℒₛₑₜ (shift ℒₛₑₜ (∀⁰ (∼A ⋎ A)).val) := by
    have := (∀⁰ (∼A ⋎ A)).shift.isSemiformula; simpa using this
  have lS₀ : SeqLt S₀ L := by rw [hS₀, hS]; exact ((SeqLt.empty L).insert mFs).insert mP
  have fS₀ : IsFormulaSet ℒₛₑₜ S₀ := by rw [hS₀, hS]; simp [fsh, (∼X ⋎ X).isSemiformula]
  have dE : DLv 𝗭𝗙 (insert (∼X).val (insert X.val S₀)) (L + 1) :=
    DLv.em hL4 ((lS₀.insert mX).insert mnX) (fins _ (fins _ fS₀)) X.val (by simp) (by simp)
  have dO : DLv 𝗭𝗙 S₀ (L + 1 + 1) :=
    DLv.or_m (le_trans hL4 le_self_add) (lS₀.mono le_self_add) (p := (∼X).val) (q := X.val)
      (by rw [hS₀]; simp) dE
  have dA := DLv.all_m (le_trans hL4 (le_trans le_self_add le_self_add))
    (((SeqLt.empty L).insert mF).mono (le_trans le_self_add le_self_add)) (p := (∼A ⋎ A).val)
    (by simp) (by rw [← Bootstrapping.Semiformula.free_val, free_em]; exact dO)
  exact dA.mono (le_of_add_eq (y := 1) (by rw [hL]; ring))

set_option maxHeartbeats 1000000 in
/-- **`∀(A ↔ A)`, bounded.** -/
theorem dall_iff (A : Bootstrapping.Semiformula V ℒₛₑₜ 1) {a : V} (ha : A.val ≤ lvB a)
    (h2 : 2 ≤ a) : DLv 𝗭𝗙 (insert (∀⁰ (A 🡘 A)).val ∅) (100 * a + 238) := by
  set X := A.free with hX
  have lX : X.val ≤ lvB (10 * (a + 1 + 1) + 1) := freeA_le A ha
  set nb : V := 10 * (10 * (a + 1 + 1) + 1 + 1) with hnb
  have lnX : (∼X).val ≤ lvB nb := by
    rw [Bootstrapping.Semiformula.val_neg]; exact neg_level _ _ lX X.isSemiformula.isUFormula
  have hnb2 : (2 : V) ≤ nb := le_of_add_eq (y := 100 * a + 218) (by rw [hnb]; ring)
  have hxnb : 10 * (a + 1 + 1) + 1 ≤ nb := le_of_add_eq (y := 90 * a + 199) (by rw [hnb]; ring)
  have lP : (∼X ⋎ X).val ≤ lvB (nb + 4) := by
    rw [Bootstrapping.Semiformula.val_or]
    exact conn_le (tag := 5) hnb2 (by norm_num) lnX (lift_lvB lX hxnb)
  have lQ : ((∼X ⋎ X) ⋏ (∼X ⋎ X)).val ≤ lvB (nb + 4 + 4) := by
    rw [Bootstrapping.Semiformula.val_and]
    exact conn_le (tag := 4) (le_trans hnb2 le_self_add) (by norm_num) lP lP
  have eQ : (X 🡘 X) = (∼X ⋎ X) ⋏ (∼X ⋎ X) := by
    simp [LogicalConnective.iff, Bootstrapping.Semiformula.imp_def]
  -- the closed formula
  have lnA : (∼A).val ≤ lvB (10 * (a + 1)) := by
    rw [Bootstrapping.Semiformula.val_neg]; exact neg_level _ _ ha A.isSemiformula.isUFormula
  have h2' : (2 : V) ≤ 10 * (a + 1) := le_of_add_eq (y := 10 * a + 8) (by ring)
  have lI : (∼A ⋎ A).val ≤ lvB (10 * (a + 1) + 4) := by
    rw [Bootstrapping.Semiformula.val_or]
    exact conn_le (tag := 5) h2' (by norm_num) lnA (lift_lvB ha (le_of_add_eq (y := 9 * a + 10) (by ring)))
  have eA : (A 🡘 A) = (∼A ⋎ A) ⋏ (∼A ⋎ A) := by
    simp [LogicalConnective.iff, Bootstrapping.Semiformula.imp_def]
  have lAA : (A 🡘 A).val ≤ lvB (10 * (a + 1) + 4 + 4) := by
    rw [eA, Bootstrapping.Semiformula.val_and]
    exact conn_le (tag := 4) (le_trans h2' le_self_add) (by norm_num) lI lI
  have lF : (∀⁰ (A 🡘 A)).val ≤ lvB (10 * (a + 1) + 4 + 4 + 2) := by
    rw [Bootstrapping.Semiformula.val_all]
    exact pair_lvB (le_trans h2' (le_trans le_self_add le_self_add))
      (tag_le_lvB (k := 6) (by norm_num) (le_trans h2' (le_trans le_self_add le_self_add))) lAA
  set L : V := 100 * a + 233 with hL
  have hlt : ∀ {x m : V}, x ≤ lvB m → m ≤ 100 * a + 232 → x < lvB L := fun hx hm =>
    lt_of_lt_of_le (lt_lvB_succ (lift_lvB hx hm)) (lvB_mono (le_of_eq (by rw [hL]; ring)))
  have mQ := hlt lQ (le_of_add_eq (y := 4) (by rw [hnb]; ring))
  have mP := hlt lP (le_of_add_eq (y := 8) (by rw [hnb]; ring))
  have mX := hlt lX (le_of_add_eq (y := 90 * a + 211) (by ring))
  have mnX := hlt lnX (le_of_add_eq (y := 12) (by rw [hnb]; ring))
  have mF := hlt lF (le_of_add_eq (y := 90 * a + 212) (by ring))
  have mFs := hlt (shift_all_le lF) (le_of_add_eq (y := 90 * a + 211) (by ring))
  have hL4 : (4 : V) ≤ L := le_of_add_eq (y := 100 * a + 229) (by rw [hL]; ring)
  have hS : setShift ℒₛₑₜ (insert (∀⁰ (A 🡘 A)).val (∅ : V)) =
      insert (shift ℒₛₑₜ (∀⁰ (A 🡘 A)).val) ∅ := by
    rw [mem_setShift_insert]; congr 1; exact mem_ext fun y => by simp [mem_setShift_iff]
  set S₀ := insert ((∼X ⋎ X) ⋏ (∼X ⋎ X)).val (setShift ℒₛₑₜ (insert (∀⁰ (A 🡘 A)).val (∅ : V)))
    with hS₀
  have fsh : IsFormula ℒₛₑₜ (shift ℒₛₑₜ (∀⁰ (A 🡘 A)).val) := by
    have := (∀⁰ (A 🡘 A)).shift.isSemiformula; simpa using this
  have lS₀ : SeqLt S₀ L := by rw [hS₀, hS]; exact ((SeqLt.empty L).insert mFs).insert mQ
  have fS₀ : IsFormulaSet ℒₛₑₜ S₀ := by
    rw [hS₀, hS]; simp [fsh, ((∼X ⋎ X) ⋏ (∼X ⋎ X)).isSemiformula]
  set S₁ := insert (∼X ⋎ X).val S₀ with hS₁
  have lS₁ : SeqLt S₁ L := lS₀.insert mP
  have fS₁ : IsFormulaSet ℒₛₑₜ S₁ := fins _ fS₀
  have dE : DLv 𝗭𝗙 (insert (∼X).val (insert X.val S₁)) (L + 1) :=
    DLv.em hL4 ((lS₁.insert mX).insert mnX) (fins _ (fins _ fS₁)) X.val (by simp) (by simp)
  have dO : DLv 𝗭𝗙 S₁ (L + 1 + 1) :=
    DLv.or_m (le_trans hL4 le_self_add) (lS₁.mono le_self_add) (p := (∼X).val) (q := X.val)
      (by rw [hS₁]; simp) dE
  have dAnd : DLv 𝗭𝗙 S₀ (L + 1 + 1 + 1) :=
    DLv.and_m (le_trans hL4 (le_trans le_self_add le_self_add))
      (lS₀.mono (le_trans le_self_add le_self_add)) (p := (∼X ⋎ X).val) (q := (∼X ⋎ X).val)
      (by rw [hS₀]; simp) dO dO
  have dA := DLv.all_m (le_trans hL4 (le_trans le_self_add (le_trans le_self_add le_self_add)))
    (((SeqLt.empty L).insert mF).mono (le_trans le_self_add (le_trans le_self_add le_self_add)))
    (p := (A 🡘 A).val) (by simp)
    (by rw [← Bootstrapping.Semiformula.free_val, free_iff, ← hX, eQ]; exact dAnd)
  exact dA.mono (le_of_add_eq (y := 1) (by rw [hL]; ring))

/-! ## Functional matching environments, bounded -/

/-- The placeholder level of the matching induction up to `J`. -/
def uM (J : V) : V := Cm * Exp.exp (4 * J) + Cm + 2

theorem two_le_uM (J : V) : (2 : V) ≤ uM J := le_add_self

theorem mT_le {i J : V} (h : i ≤ J) : (MT i).val ≤ lvB (uM J) := by
  refine lift_lvB (mVal_le i) ?_
  unfold uM
  refine le_trans ?_ (le_trans le_self_add le_self_add)
  exact mul_le_mul_of_nonneg_left (exp_monotone_le.mpr (mul_le_mul_of_nonneg_left h (by norm_num)))
    (Arithmetic.zero_le _)

theorem mTs_le {i J : V} (h : i ≤ J) : (MT i).shift.val ≤ lvB (uM J) := by
  rw [Bootstrapping.Semiformula.val_shift]
  refine lift_lvB (shift_level (mVal_le i)) ?_
  unfold uM
  rw [add_assoc]
  refine _root_.add_le_add (mul_le_mul_of_nonneg_left (exp_monotone_le.mpr
    (mul_le_mul_of_nonneg_left h (by norm_num))) (Arithmetic.zero_le _)) ?_
  exact le_trans (by norm_num : (1 : V) ≤ 2) le_add_self

theorem zT_le' (J : V) : (zT (V := V)).val ≤ lvB (uM J) :=
  le_trans zT_le_Cm (le_trans (le_lvB_self _) (lvB_mono (le_trans le_add_self le_self_add)))

theorem fT_le' (J : V) : (fT (V := V)).val ≤ lvB (uM J) :=
  le_trans fT_le_Cm (le_trans (le_lvB_self _) (lvB_mono (le_trans le_add_self le_self_add)))

/-- The placeholder tuple of one step. -/
def Kf (i : V) : (k : Fin 8) → SF V (arG k) := K8 (MT i).shift (MT (i + 1)) zT ⊤ ⊤ ⊤ ⊤ ⊤

theorem Kf_le {i J : V} (h : i + 1 ≤ J) : ∀ k, (Kf i k).val ≤ lvB (uM J) := by
  have hi : i ≤ J := le_trans le_self_add h
  have ht : (⊤ : SF V 1).val ≤ lvB (uM J) := by
    simpa using SizedPlaceholderCongruence.verum_le (two_le_uM J)
  intro k
  match k with
  | 0 => exact mTs_le hi
  | 1 => exact mT_le h
  | 2 => exact zT_le' J
  | 3 => exact ht
  | 4 => exact ht
  | 5 => exact ht
  | 6 => exact ht
  | 7 => exact ht

/-- The translation of `funTemplate` at one step. -/
theorem tr_funTemplate (i : V) :
    translateFormula (Kf i) (Rewriting.emb funTemplate) =
      ((∀⁰ (∼(MT i).shift ⋎ (⌜funcS⌝ : SF V 1))) ⋏ (∀⁰ (MT (i + 1) 🡘 MpT (MT i).shift zT))) 🡒
        ∀⁰ (∼(MT (i + 1)) ⋎ (⌜funcS⌝ : SF V 1)) := by
  simp only [funTemplate, LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
    translateFormula_imp, tr_andG, tr_funM, tr_mpDef]
  rfl

theorem tr_funM0 (i : V) : translateFormula (Kf i) (Rewriting.emb (funM 0)) =
    ∀⁰ (∼(MT i).shift ⋎ (⌜funcS⌝ : SF V 1)) := tr_funM _ 0

theorem tr_conj (i : V) : translateFormula (Kf i) (Rewriting.emb (funM 0 ⋏ mpDef)) =
    (∀⁰ (∼(MT i).shift ⋎ (⌜funcS⌝ : SF V 1))) ⋏ (∀⁰ (MT (i + 1) 🡘 MpT (MT i).shift zT)) := by
  simp only [LogicalConnective.HomClass.map_and, tr_andG, tr_funM, tr_mpDef]
  rfl

/-- The translation constant of the step. -/
def tS : ℕ := tA (Rewriting.emb funTemplate : Proposition GL) +
  tA (Rewriting.emb (funM 0 ⋏ mpDef) : Proposition GL) + tA (Rewriting.emb (funM 0) : Proposition GL)

/-- The member level of the step. -/
def mM (J : V) : V := (tS : V) * (uM J + 1)

/-- The compile level of `funTemplate` at `uM J`. -/
def cF (J : V) : V :=
  cExpG (tmA funTemplate_provable) (tmB funTemplate_provable) (uM J) + (tmK funTemplate_provable : ℕ) + 1

/-- The base level of the bounded matching induction. -/
def wF (J : V) : V := cF J + 10 * (mM J + 1) + 100 * uM J + 300

/-- **The level of `fun_MT`.** -/
def funW (j : V) : V := wF j + 10 * j

theorem tr_le {i J : V} (h : i + 1 ≤ J) (φ : Proposition GL)
    (hφ : tA φ ≤ tS) : (translateFormula (Kf i) φ).val ≤ lvB (mM J) :=
  lift_lvB (translate_level φ (uM J) (Kf i) (Kf_le h))
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hφ) (Arithmetic.zero_le _))

set_option maxHeartbeats 4000000 in
/-- **Matching environments are functional, bounded**, at every index up to a
target `J`, at the compile level of `J`. -/
theorem fun_MT_leJ {i₀ J : V} (h₀ : i₀ ≤ J) : DLv 𝗭𝗙 (insert (funVal i₀) ∅) (wF J + 10 * i₀) := by
  obtain ⟨W0, hW0⟩ : ∃ W0 : V, W0 = wF J := ⟨_, rfl⟩
  have hu2 := two_le_uM J
  have key : ∀ i : V, i ≤ J → DLv 𝗭𝗙 (insert (funVal i) ∅) (W0 + 10 * i) := by
    intro i
    induction i using ISigma1.sigma1_succ_induction
    · simp only [DLv, DerivableLe, lvB, funVal]
      definability
    · intro _
      have h0 : MT (0 : V) = ⌜funcS⌝ := Bootstrapping.Semiformula.ext (by simp [MT, fT])
      rw [← funT_val, h0]
      refine (dall_em (⌜funcS⌝ : SF V 1) (fT_le' J) hu2).mono ?_
      rw [hW0]
      exact le_of_add_eq (y := cF J + 10 * (mM J + 1) + 67) (by unfold wF; ring)
    · case succ i ih =>
      intro hiJ
      have hi : i ≤ J := le_trans le_self_add hiJ
      have d0 := ih hi
      set w := W0 + 10 * i with hw
      have hW : wF J ≤ w := by rw [hw, hW0]; exact le_self_add
      have hw4 : (4 : V) ≤ w := le_trans (le_of_add_eq (y := cF J + 10 * (mM J + 1) + 100 * uM J + 296)
        (by unfold wF; ring)) hW
      have hMw : 10 * (mM J + 1) + 1 ≤ w :=
        le_trans (le_of_add_eq (y := cF J + 100 * uM J + 299) (by unfold wF; ring)) hW
      have hmlt : ∀ {x : V}, x ≤ lvB (mM J) → x < lvB w := fun hx =>
        lt_of_lt_of_le (lt_lvB_succ hx) (lvB_mono (le_trans (le_of_add_eq (y := 9 * mM J + 10)
          (by ring)) hMw))
      have hnlt : ∀ (φ : Fm), φ.val ≤ lvB (mM J) → (∼φ).val < lvB w := fun φ hφ => by
        rw [Bootstrapping.Semiformula.val_neg]
        exact lt_of_lt_of_le (lt_lvB_succ (neg_level _ _ hφ φ.isSemiformula.isUFormula))
          (lvB_mono hMw)
      -- the shifted hypothesis
      rw [← funT_val] at d0
      have l0 := tr_le hiJ (Rewriting.emb (funM 0)) (by unfold tS; omega)
      rw [tr_funM0] at l0
      have d1 := dshift hw4 (by rw [funT_shift]; exact hmlt l0) d0
      rw [funT_shift] at d1
      -- the definitional premise
      have d2 := (dall_iff (MT (i + 1)) (mT_le hiJ) hu2).mono
        (le_trans (le_trans (le_of_add_eq (y := cF J + 10 * (mM J + 1) + 62) (by unfold wF; ring)) hW)
          (le_self_add : w ≤ w + 1))
      rw [show (∀⁰ (MT (i + 1) 🡘 MT (i + 1)) : Fm) = ∀⁰ (MT (i + 1) 🡘 MpT (MT i).shift zT) by
        rw [← MT_succ]] at d2
      -- the conjunction and modus ponens
      have lc := tr_le hiJ (Rewriting.emb (funM 0 ⋏ mpDef)) (by unfold tS; omega)
      rw [tr_conj] at lc
      have d3 := dk_intro (le_trans hw4 le_self_add)
        (lt_of_lt_of_le (hmlt lc) (lvB_mono le_self_add)) d1 d2
      have lt := tr_le hiJ (Rewriting.emb funTemplate) (by unfold tS; omega)
      rw [tr_funTemplate] at lt
      have hc := (compiledLe (by decide) funTemplate_provable (Kf i) hu2 (Kf_le hiJ)).mono
        (show cF J ≤ w + 1 + 1 + 1 by
          refine le_trans (le_trans ?_ hW) (le_trans le_self_add (le_trans le_self_add le_self_add))
          unfold wF; rw [add_assoc, add_assoc]; exact le_self_add)
      rw [tr_funTemplate] at hc
      have up2 : w ≤ w + 1 + 1 + 1 := le_trans le_self_add (le_trans le_self_add le_self_add)
      set φ : Fm := (∀⁰ (∼(MT i).shift ⋎ (⌜funcS⌝ : SF V 1))) ⋏
        (∀⁰ (MT (i + 1) 🡘 MpT (MT i).shift zT)) with hφd
      set ψ : Fm := ∀⁰ (∼(MT (i + 1)) ⋎ (⌜funcS⌝ : SF V 1)) with hψd
      have hneg : (φ ⋏ ∼ψ).val < lvB (w + 1 + 1 + 1) := by
        have := hnlt (φ 🡒 ψ) lt
        rw [show (∼(φ 🡒 ψ) : Fm) = φ ⋏ ∼ψ by simp [Bootstrapping.Semiformula.imp_def]] at this
        exact lt_of_lt_of_le this (lvB_mono up2)
      have d4 := dmdp (le_trans hw4 up2) hneg (lt_of_lt_of_le (hmlt lt) (lvB_mono up2)) hc d3
      rw [funT_val] at d4
      refine d4.mono ?_
      rw [hw]
      exact le_of_add_eq (y := 4) (by ring)
  have := key i₀ h₀
  rw [hW0] at this
  exact this

/-- **Matching environments are functional, bounded.** -/
theorem fun_MT_le (J : V) : DLv 𝗭𝗙 (insert (funVal J) ∅) (funW J) := fun_MT_leJ le_rfl

end LeanProofs.ZFCinPA.SizedLGlue1
