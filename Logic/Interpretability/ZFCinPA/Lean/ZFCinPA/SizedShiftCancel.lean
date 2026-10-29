import ZFCinPA.ModelCodedShiftCancellation
import ZFCinPA.SizedTemplateCompiler
import BoundedPAConsistency.ShiftBound

/-!
# Shift cancellation with an explicit size bound

`ModelCodedShiftCancellation.cancelShift` turns an internal proof of
`shift φ` into a proof of `φ` through `TProof.all` and `TProof.specialize`,
whose codes are chosen by `Classical.choose`. This module re-derives the step
from the bounded primitive rules (`cancelShiftLe`): generalize to `∀ φ`, then
specialize at `&0` (a cut against `∃ ¬φ`). It costs four bounded rule
applications. `cancelShiftNLe` iterates it along `shiftN`; this is the last
step of the bounded template compiler.
-/
set_option autoImplicit false
noncomputable section

namespace LeanProofs.ZFCinPA.SizedShiftCancel

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic
open LeanProofs.BoundedPAConsistency.SizedDerivation
open LeanProofs.ZFCinPA.ModelCodedBinderAbsorption LeanProofs.ZFCinPA.ModelCodedShiftCancellation
open LeanProofs.ZFCinPA.SizedTemplateCompiler

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {T : Theory L} [T.Δ₁]

/-- The six formulas a shift cancellation puts into sequents, below `B`. -/
structure CancelBound (p B : V) : Prop where
  hp : p < B
  hall : ^∀ p < B
  hsh : shift L p < B
  hshAll : shift L (^∀ p) < B
  hex : ^∃ (neg L p) < B
  hn : neg L p < B

theorem empty_lt' (B : V) : ∀ y ∈ (∅ : V), y < B := fun y hy => by simp at hy

/-- **Shift cancellation, bounded.** -/
theorem cancelShiftLe {p e B : V} (hp : IsFormula L p) (he : 4 ≤ e) (hBe : B ≤ e)
    (hb : CancelBound (L := L) p B)
    (h : DerivableLe T (insert (shift L p) (∅ : V)) (Exp.exp e)) :
    DerivableLe T (insert p (∅ : V)) (Exp.exp (stg 4 e)) := by
  have hp1 : IsSemiformula L 1 p := ⟨hp.isUFormula, le_trans hp.bv_le (by simp)⟩
  have hS := DerivableLe.insert_lt (B := B) hb.hp (empty_lt' B)
  -- generalize: `⊢ ∀ p` from `⊢ shift p`
  have hprem : DerivableLe T (insert (free L p) (setShift L (insert (^∀ p) (∅ : V))))
      (Exp.exp (1024 * e)) := by
    rw [free_formula hp, mem_setShift_insert]
    have hset : setShift L (∅ : V) = ∅ := mem_ext fun y => by simp [mem_setShift_iff]
    rw [hset]
    refine DerivableLe.wk he (DerivableLe.seq_le hBe (DerivableLe.insert_lt hb.hsh
      (DerivableLe.insert_lt hb.hshAll (empty_lt' B))))
      (by simp [hp.shift, hp1, hp1.shift]) ?_ h
    intro y hy
    rcases mem_bitInsert_iff.mp hy with rfl | hy
    · simp
    · simp at hy
  have dAll := DerivableLe.all_m (T := T) (DerivableLe.four_le_1024 he)
    (le_exp_of_le (DerivableLe.seq_le hBe (DerivableLe.insert_lt hb.hall
      (empty_lt' B))) DerivableLe.le_1024) (by simp) hprem
  -- specialize at `&0`
  have dL := DerivableLe.wk (DerivableLe.four_le_1024 (DerivableLe.four_le_1024 he))
    (le_exp_of_le (DerivableLe.seq_le hBe (DerivableLe.insert_lt hb.hall hS))
      (le_trans DerivableLe.le_1024 DerivableLe.le_1024))
    (by simp [hp, hp1]) (by intro x; simp; tauto) dAll
  have dEm := DerivableLe.em (T := T) he
    (DerivableLe.seq_le hBe (DerivableLe.insert_lt hb.hn (DerivableLe.insert_lt hb.hex hS)))
    (by simp [hp, hp.neg, hp1.neg]) p (by simp) (by simp)
  have dEx := DerivableLe.ex_m (T := T) (p := neg L p) (t := ^&0) (DerivableLe.four_le_1024 he)
    (le_exp_of_le (DerivableLe.seq_le hBe (DerivableLe.insert_lt hb.hex hS)) DerivableLe.le_1024)
    (le_exp_of_le_self (le_trans (show (^&0 : V) ≤ 4 by simp [qqFvar, pair]; norm_num)
      (le_trans he DerivableLe.le_1024)))
    (by simp) (by simp) (by rw [substs1_formula hp.neg 0]; exact dEm)
  have hcut := DerivableLe.cut (DerivableLe.four_le_1024 (DerivableLe.four_le_1024
      (DerivableLe.four_le_1024 he)))
    (le_exp_of_le (DerivableLe.seq_le hBe hS)
      (le_trans DerivableLe.le_1024 (le_trans DerivableLe.le_1024 DerivableLe.le_1024)))
    (^∀ p) (le_exp_of_le_self (le_trans (le_of_lt hb.hall)
      (le_trans hBe (le_trans DerivableLe.le_1024 (le_trans DerivableLe.le_1024
        DerivableLe.le_1024))))) dL (by
      rw [neg_all hp.isUFormula]
      exact dEx.mono (exp_monotone_le.mpr DerivableLe.le_1024))
  exact hcut

theorem stg_add (m n : ℕ) (e : V) : stg m (stg n e) = stg (n + m) e := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [stg, ih]; rfl

/-- **Iterated shift cancellation, bounded.** -/
theorem cancelShiftNLe (φ : Formula V L) {e B : V} (he : 4 ≤ e) (hBe : B ≤ e) :
    ∀ n : ℕ, (∀ k < n, CancelBound (L := L) (shiftN k φ).val B) →
      DerivableLe T (insert (shiftN n φ).val (∅ : V)) (Exp.exp e) →
      DerivableLe T (insert φ.val (∅ : V)) (Exp.exp (stg (4 * n) e))
  | 0, _, h => by simpa [stg, shiftN] using h
  | n + 1, hb, h => by
      have h' := cancelShiftLe (T := T) (shiftN n φ).isSemiformula he hBe (hb n (by omega))
        (by simpa [shiftN] using h)
      have hrec := cancelShiftNLe φ (four_le_stg he 4) (le_trans hBe (le_stg 4 e)) n
        (fun k hk => hb k (by omega)) h'
      have hst : stg (4 * n) (stg 4 e) = stg (4 * (n + 1)) e := by
        rw [stg_add, show 4 + 4 * n = 4 * (n + 1) by ring]
      rw [hst] at hrec
      exact hrec

end LeanProofs.ZFCinPA.SizedShiftCancel
