import ZFCinPA.SizedLSlot
import ZFCinPA.LDriverSteps

/-!
# Bounded driver combinators

`∧`-elimination (`dk_leftL`), `∀`-introduction of a closed derivation
(`dall_intro`), the bounded `∀∀(A ↔ A)` (`dall2_iff`), and the combinators
`dandW`, `dmpW`, `dleftW`, `drightW` whose inputs may sit at any level below
the working level.

Part of the bounded `hSchema` driver (`SizedDriver`), split out of one
module so that each Lean process elaborates only a few step proofs.
-/
set_option autoImplicit false
noncomputable section

namespace LeanProofs.ZFCinPA.SizedDriverSteps

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic
open LeanProofs.ZFCinPA
open LeanProofs.BoundedPAConsistency.SizedDerivation
open LeanProofs.ZFCinPA.SetCodeLevels LeanProofs.ZFCinPA.LevelDerivation
open LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.TemplateTranslateLevel
open LeanProofs.ZFCinPA.SizedCongruence (lt_lvB_succ le_of_add_eq fvar0_le)
open LeanProofs.ZFCinPA.SizedPlaceholderCongruence (conn_le)
open LeanProofs.ZFCinPA.SizedLPlumbing LeanProofs.ZFCinPA.SizedLGlue1 LeanProofs.ZFCinPA.SizedLNumOK
open LeanProofs.ZFCinPA.SizedLSlot (tsubst_le_n)
open LeanProofs.ZFCinPA.LTemplate LeanProofs.ZFCinPA.LInvariant LeanProofs.ZFCinPA.LStepAnd
open LeanProofs.ZFCinPA.LStepBasic LeanProofs.ZFCinPA.LStepAtom LeanProofs.ZFCinPA.LStepExT
open LeanProofs.ZFCinPA.LDriverBase LeanProofs.ZFCinPA.LDriverSteps
open LeanProofs.ZFCinPA.SizedOpenTemplateLeaves (cExpG)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local notation "Fm" => Bootstrapping.Formula V ℒₛₑₜ


/-! ## More bounded combinators -/

/-- `∧`-elimination (left) at a conjunction of level `m`, by a cut on it. -/
theorem dk_leftL {φ ψ : Fm} {w m : V} (hw : 4 ≤ w) (hm : (φ ⋏ ψ).val ≤ lvB m)
    (hmw : 10 * (m + 1) + 1 ≤ w) (d : DLv 𝗭𝗙 (insert (φ ⋏ ψ).val ∅) w) :
    DLv 𝗭𝗙 (insert φ.val ∅) (w + 1 + 1 + 1) := by
  have hmw' : m + 1 ≤ w := le_trans (le_of_add_eq (y := 9 * m + 10) (by ring)) hmw
  have hp : (φ ⋏ ψ).val < lvB w := lt_of_lt_of_le (lt_lvB_succ hm) (lvB_mono hmw')
  have hφ : φ.val < lvB w := lt_trans (lt_K!_left _ _) hp
  have hneg : (∼(φ ⋏ ψ)).val < lvB w := by
    rw [Bootstrapping.Semiformula.val_neg]
    exact lt_of_lt_of_le (lt_lvB_succ (neg_level _ _ hm (φ ⋏ ψ).isSemiformula.isUFormula))
      (lvB_mono hmw)
  have hnn : (∼(φ ⋏ ψ)) = ∼φ ⋎ ∼ψ := by simp
  have e1 : (∼φ).val < (∼(φ ⋏ ψ)).val := by
    rw [hnn, Bootstrapping.Semiformula.val_or]; exact lt_or_left _ _
  have e2 : (∼ψ).val < (∼(φ ⋏ ψ)).val := by
    rw [hnn, Bootstrapping.Semiformula.val_or]; exact lt_or_right _ _
  set S := insert φ.val (∅ : V) with hSd
  have lS : SeqLt S w := (SeqLt.empty w).insert hφ
  have fS : IsFormulaSet ℒₛₑₜ S := fset1 φ
  set B := insert (∼(φ ⋏ ψ)).val S with hBd
  have lB : SeqLt B w := lS.insert hneg
  have fB : IsFormulaSet ℒₛₑₜ B := fins _ fS
  have dE : DLv 𝗭𝗙 (insert (∼φ).val (insert (∼ψ).val B)) (w + 1) := by
    refine DLv.em hw ((lB.insert (lt_trans e2 hneg)).insert (lt_trans e1 hneg))
      (fins _ (fins _ fB)) φ.val (by simp [hBd, hSd]) ?_
    rw [← Bootstrapping.Semiformula.val_neg]; simp
  have dO : DLv 𝗭𝗙 B (w + 1 + 1) := by
    refine DLv.or_m (le_trans hw le_self_add) (lB.mono le_self_add) (p := (∼φ).val)
      (q := (∼ψ).val) ?_ dE
    rw [hBd, hnn, Bootstrapping.Semiformula.val_or]; simp
  have dA : DLv 𝗭𝗙 (insert (φ ⋏ ψ).val S) (w + 1) :=
    DLv.wk hw (lS.insert hp) (fins _ fS)
      (insert_subset_insert_of_subset _ (by intro z hz; simp at hz)) d
  have hneg' : neg ℒₛₑₜ (φ ⋏ ψ).val = (∼(φ ⋏ ψ)).val := (Bootstrapping.Semiformula.val_neg _).symm
  exact DLv.cut (le_trans hw (le_trans le_self_add le_self_add))
    (lS.mono (le_trans le_self_add le_self_add)) (φ ⋏ ψ).val
    (lt_of_lt_of_le hp (lvB_mono (le_trans le_self_add le_self_add))) (dA.mono le_self_add)
    (by rw [hneg']; exact dO)

/-- The level of `∀(A ↔ A)` at any arity. -/
theorem allIff_le {n : ℕ} (A : Bootstrapping.Semiformula V ℒₛₑₜ (n + 1)) {a : V}
    (ha : A.val ≤ lvB a) : (∀⁰ (A 🡘 A)).val ≤ lvB (10 * (a + 1) + 10) := by
  have lnA : (∼A).val ≤ lvB (10 * (a + 1)) := by
    rw [Bootstrapping.Semiformula.val_neg]; exact neg_level _ _ ha A.isSemiformula.isUFormula
  have h2' : (2 : V) ≤ 10 * (a + 1) := le_of_add_eq (y := 10 * a + 8) (by ring)
  have lI : (∼A ⋎ A).val ≤ lvB (10 * (a + 1) + 4) := by
    rw [Bootstrapping.Semiformula.val_or]
    exact conn_le (tag := 5) h2' (by norm_num) lnA
      (lift_lvB ha (le_of_add_eq (y := 9 * a + 10) (by ring)))
  have eA : (A 🡘 A) = (∼A ⋎ A) ⋏ (∼A ⋎ A) := by
    simp [LogicalConnective.iff, Bootstrapping.Semiformula.imp_def]
  have lAA : (A 🡘 A).val ≤ lvB (10 * (a + 1) + 4 + 4) := by
    rw [eA, Bootstrapping.Semiformula.val_and]
    exact conn_le (tag := 4) (le_trans h2' le_self_add) (by norm_num) lI lI
  rw [Bootstrapping.Semiformula.val_all]
  exact le_trans (pair_lvB (le_trans h2' (le_trans le_self_add le_self_add))
      (tag_le_lvB (k := 6) (by norm_num) (le_trans h2' (le_trans le_self_add le_self_add))) lAA)
    (lvB_mono (le_of_eq (by ring)))

/-- `∀`-introduction of a derivation of the free instance. -/
theorem dall_intro {B : SF V 1} {w : V} (hw : 4 ≤ w) (hB : (∀⁰ B : Fm).val < lvB w)
    (hBs : shift ℒₛₑₜ (∀⁰ B : Fm).val < lvB w) (hf : B.free.val < lvB w)
    (d : DLv 𝗭𝗙 (insert B.free.val ∅) w) : DLv 𝗭𝗙 (insert (∀⁰ B : Fm).val ∅) (w + 1 + 1) := by
  have hS : setShift ℒₛₑₜ (insert (∀⁰ B : Fm).val (∅ : V)) = insert (shift ℒₛₑₜ (∀⁰ B : Fm).val) ∅ := by
    rw [mem_setShift_insert]; congr 1; exact mem_ext fun y => by simp
  set S₀ := insert B.free.val (setShift ℒₛₑₜ (insert (∀⁰ B : Fm).val (∅ : V))) with hS₀
  have lS₀ : SeqLt S₀ w := by rw [hS₀, hS]; exact ((SeqLt.empty w).insert hBs).insert hf
  have fS₀ : IsFormulaSet ℒₛₑₜ S₀ := by rw [hS₀, hS]; simp
  have dW : DLv 𝗭𝗙 S₀ (w + 1) :=
    DLv.wk hw lS₀ fS₀ (insert_subset_insert_of_subset _ (by intro z hz; simp at hz)) d
  exact DLv.all_m (le_trans hw le_self_add) (((SeqLt.empty w).insert hB).mono le_self_add)
    (p := B.val) (by simp) (by rw [← Bootstrapping.Semiformula.free_val]; exact dW)

set_option maxHeartbeats 2000000 in
/-- **`∀∀(A ↔ A)`, bounded.** -/
theorem dall2_iff (A : SF V 2) {a : V} (ha : A.val ≤ lvB a) (h2 : 2 ≤ a) :
    DLv 𝗭𝗙 (insert (∀⁰ ∀⁰ (A 🡘 A) : Fm).val ∅) (1000 * a + 3000) := by
  set A' : SF V 1 := A.shift.subst (Bootstrapping.SemitermVec.q
    (![Bootstrapping.Semiterm.fvar 0] : Bootstrapping.SemitermVec V ℒₛₑₜ 1 0)) with hA'
  have hfree : (∀⁰ (A 🡘 A) : SF V 1).free = ∀⁰ (A' 🡘 A') := by
    simp only [Bootstrapping.Semiformula.free, Bootstrapping.Semiformula.shift_all,
      Bootstrapping.Semiformula.shift_iff, Bootstrapping.Semiformula.substs_all,
      Bootstrapping.Semiformula.substs_imply, hA']
  have la' : A'.val ≤ lvB (10 * (a + 1 + 1) + 1) := by
    refine tsubst_le_n _ _ (by rw [Bootstrapping.Semiformula.val_shift]; exact shift_level ha)
      le_rfl (fun i => ?_)
    match i with
    | 0 =>
        have : (^#0 : V) ≤ lvB 1 :=
          le_trans (show (^#0 : V) ≤ 4 by simp [qqBvar, pair]) (le_of_eq lvB_one.symm)
        simpa using this
    | 1 =>
        show (Bootstrapping.SemitermVec.q
          (![Bootstrapping.Semiterm.fvar 0] : Bootstrapping.SemitermVec V ℒₛₑₜ 1 0)
          (Fin.succ 0)).val ≤ _
        rw [Bootstrapping.SemitermVec.q_succ]
        simpa using fvar0_le (1 : V) le_rfl
  have h2' : (2 : V) ≤ 10 * (a + 1 + 1) + 1 := le_of_add_eq (y := 10 * a + 19) (by ring)
  have d := dall_iff A' la' h2'
  rw [← hfree] at d
  have lB := allIff_le A ha
  have lBB : (∀⁰ ∀⁰ (A 🡘 A) : Fm).val ≤ lvB (10 * (a + 1) + 10 + 2) := by
    rw [Bootstrapping.Semiformula.val_all]
    exact pair_lvB (le_trans h2 (le_of_add_eq (y := 9 * a + 20) (by ring)))
      (tag_le_lvB (k := 6) (by norm_num) (le_trans h2 (le_of_add_eq (y := 9 * a + 20) (by ring))))
      lB
  have lF := allIff_le A' la'
  rw [← hfree] at lF
  have hlt : ∀ {x m : V}, x ≤ lvB m → m + 1 ≤ 100 * (10 * (a + 1 + 1) + 1) + 238 →
      x < lvB (100 * (10 * (a + 1 + 1) + 1) + 238) := fun hx hm =>
    lt_of_lt_of_le (lt_lvB_succ hx) (lvB_mono hm)
  have hB := hlt lBB (le_of_add_eq (y := 990 * a + 2315) (by ring))
  have hBs := hlt (shift_level lBB) (le_of_add_eq (y := 990 * a + 2314) (by ring))
  have hf := hlt lF (le_of_add_eq (y := 900 * a + 2107) (by ring))
  have := dall_intro (B := ∀⁰ (A 🡘 A))
    (le_of_add_eq (y := 1000 * a + 2334) (by ring)) hB hBs hf d
  exact this.mono (le_of_add_eq (y := 660) (by ring))

/-! ## Combinators with inputs below the working level -/

theorem dandW {φ ψ : Fm} {w m a b : V} (hw : 4 ≤ w) (hm : (φ ⋏ ψ).val ≤ lvB m) (hmw : m + 1 ≤ w)
    (d1 : DLv 𝗭𝗙 (insert φ.val ∅) a) (ha : a ≤ w) (d2 : DLv 𝗭𝗙 (insert ψ.val ∅) b)
    (hb : b ≤ w) : DLv 𝗭𝗙 (insert (φ ⋏ ψ).val ∅) (w + 2) :=
  (dk_introL hw hm hmw (d1.mono ha) (d2.mono hb)).mono (le_of_eq (by ring))

theorem dmpW {φ ψ : Fm} {w m a b : V} (hw : 4 ≤ w) (hm : (φ 🡒 ψ).val ≤ lvB m)
    (hmw : 10 * (m + 1) + 1 ≤ w) (d1 : DLv 𝗭𝗙 (insert (φ 🡒 ψ).val ∅) a) (ha : a ≤ w)
    (d2 : DLv 𝗭𝗙 (insert φ.val ∅) b) (hb : b ≤ w) : DLv 𝗭𝗙 (insert ψ.val ∅) (w + 3) :=
  (dmdpL hw hm hmw (d1.mono ha) (d2.mono hb)).mono (le_of_eq (by ring))

theorem dleftW {φ ψ : Fm} {w m a : V} (hw : 4 ≤ w) (hm : (φ ⋏ ψ).val ≤ lvB m)
    (hmw : 10 * (m + 1) + 1 ≤ w) (d : DLv 𝗭𝗙 (insert (φ ⋏ ψ).val ∅) a) (ha : a ≤ w) :
    DLv 𝗭𝗙 (insert φ.val ∅) (w + 3) :=
  (dk_leftL hw hm hmw (d.mono ha)).mono (le_of_eq (by ring))

theorem drightW {φ ψ : Fm} {w m a : V} (hw : 4 ≤ w) (hm : (φ ⋏ ψ).val ≤ lvB m)
    (hmw : 10 * (m + 1) + 1 ≤ w) (d : DLv 𝗭𝗙 (insert (φ ⋏ ψ).val ∅) a) (ha : a ≤ w) :
    DLv 𝗭𝗙 (insert ψ.val ∅) (w + 3) :=
  (dk_rightL hw hm hmw (d.mono ha)).mono (le_of_eq (by ring))

end LeanProofs.ZFCinPA.SizedDriverSteps
