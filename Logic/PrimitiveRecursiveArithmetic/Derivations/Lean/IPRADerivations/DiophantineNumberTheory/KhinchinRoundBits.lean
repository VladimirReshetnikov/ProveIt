import IPRADerivations.DiophantineNumberTheory.KhinchinGridRound
import IPRADerivations.DiophantineNumberTheory.KhinchinMargin
import IPRADerivations.Foundations.CrossingSearch

/-!
# The bits of one (K2) round in a coarse cell (`hurwitz_khinchin_ipra`)

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`, §"Amplification by the finitely many
residual gaps": "For each gap of positive length, apply the block construction to its interior `J` and add its
block union to `U_j`."

A coarse cell with uncovered bit `w ∈ {0, 1}` is a block of `r` fine cells; `v(k)` is the new block's coverage
count at fine cell `k < r` (zero means uncovered). After the round the fine cell `k` is uncovered iff the coarse cell
was uncovered and the block missed it: `f(k) = w · [v(k) = 0]`. With `rs = Σ_k f(k)` and `cv = Σ_k (1 − f(k))`:

* `cell_sum`: `rs + cv = r`;
* `cell_res`: `rs ≤ r w` (a covered coarse cell stays covered);
* `cell_cov`: the (K11) count `w r ≤ (c+1) Σ_k sg(v(k))` gives `w r ≤ (c+1) cv`

— the four per-cell hypotheses of `KhinchinGridRound.round_grid` (with `w ≤ 1`). The coarse bit travels in the sum
parameter `⟨w, z⟩`, so the bodies `fB v`, `cB v` are closed.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.KhinchinRoundBits

open_ipra exports
open LeanProofs.IPRA.Signum (sg)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinGridRound (bit_cases)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinMargin (monus_le' sg_le_one)
open LeanProofs.IPRA.AnalyticNumberTheory.SumPhi (sum_ones)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Pointwise facts -/

theorem f_le_one {w m : PTm n} (hw : Γ ⊢[PRAAx] le w one) (hm : Γ ⊢[PRAAx] le m one) :
    Γ ⊢[PRAAx] le (w * m) one := by
  ipra_le sl hw + 𝔞 w * sl hm

theorem f_le_w {w m : PTm n} (hm : Γ ⊢[PRAAx] le m one) : Γ ⊢[PRAAx] le (w * m) w := by
  ipra_le 𝔞 w * sl hm

/-- `sg s ≤ 1 − w (1 − sg s)` for a bit `w`. -/
theorem sg_le_cov {w s : PTm n} (hw : Γ ⊢[PRAAx] le w one) :
    Γ ⊢[PRAAx] le (sg s) (monus one (w * monus one (sg s))) := by
  refine .orE (bit_cases hw) ?_ ?_
  · have e : ((w ≐ zero) :: Γ) ⊢[PRAAx] monus one (w * monus one (sg s)) ≐ one :=
      (congrMonus (.eqRefl _) ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _))).eqTrans (monus_zero _)
    exact le_congr (.eqRefl _) e.eqSymm (sg_le_one s)
  · have hs : ((w ≐ one) :: Γ) ⊢[PRAAx] le (sg s) one := sg_le_one s
    have e1 : ((w ≐ one) :: Γ) ⊢[PRAAx] one ≐ monus one (sg s) + sg s :=
      (eq_add_of_le hs).eqTrans (add_comm _ _)
    have e : ((w ≐ one) :: Γ) ⊢[PRAAx] monus one (w * monus one (sg s)) ≐ sg s :=
      (congrMonus (.eqRefl _) ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (one_mul _))).eqTrans (monus_of_eq e1)
    exact le_congr (.eqRefl _) e.eqSymm (le_refl _)

/-! ## The bodies -/

/-- `f(k) = w [v(k) = 0]` over `0 = k`, `1 = ⟨w, z⟩`. -/
def fB (v : PTm 2) : PTm 2 := fstT (var 1) * monus one (sg (Syn.subst ![var 0, sndT (var 1)] v))

/-- `1 − f(k)`. -/
def cB (v : PTm 2) : PTm 2 := monus one (fB v)

theorem sub2' (f : PTm 2) (k x : PTm n) :
    Syn.subst ![k, x] (Syn.subst ![var 0, sndT (var 1)] f) = inst2 f k (sndT x) := by
  simp only [inst2, Syn.subst_subst]; congr 1; funext j; fin_cases j <;> simp

theorem inst2_fB (v : PTm 2) (k x : PTm n) :
    inst2 (fB v) k x = fstT x * monus one (sg (inst2 v k (sndT x))) := by
  simp only [fB, inst2, PTm.subst_mul, Signum.sg, PTm.subst_monus]
  rw [show Syn.subst ![k, x] (Syn.subst ![var 0, sndT (var 1)] v) = inst2 v k (sndT x) from sub2' v k x]
  simp [inst2]

theorem fB_at (v : PTm 2) (k w z : PTm n) :
    Γ ⊢[PRAAx] inst2 (fB v) k (pairT w z) ≐ w * monus one (sg (inst2 v k z)) := by
  rw [inst2_fB]
  exact congrMul (fst_pair _ _)
    (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) (congrInst2 v (.eqRefl _) (snd_pair _ _)))))

theorem inst2_cB (v : PTm 2) (k x : PTm n) : inst2 (cB v) k x = monus one (inst2 (fB v) k x) := by
  simp [cB, inst2]

/-! ## The cell sums -/

/-- `rs + cv = r`. -/
theorem cell_sum (v : PTm 2) {w : PTm n} (r z : PTm n) (hw : Γ ⊢[PRAAx] le w one) :
    Γ ⊢[PRAAx] ap2 (sumF (fB v)) r (pairT w z) + ap2 (sumF (cB v)) r (pairT w z) ≐ r := by
  have hc : Γ ⊢[PRAAx] ap2 (sumF (addBody (fB v) (cB v))) r (pairT w z) ≐ ap2 (sumF (one : PTm 2)) r (pairT w z) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    have hw0 : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift w) one := by simpa [Fm.shift, Syn.shift] using hw.shift
    have hw' : (lt (var 0) (Syn.shift r) :: Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift w) one := hw0.wk
    rw [inst2_addBody, inst2_cB, show Syn.shift (pairT w z) = pairT (Syn.shift w) (Syn.shift z) by simp [Syn.shift],
      show inst2 (one : PTm 2) (var 0 : PTm (n + 1)) (pairT (Syn.shift w) (Syn.shift z)) = one by simp [inst2]]
    have hf := le_congr (fB_at v (var 0) (Syn.shift w) (Syn.shift z)).eqSymm (.eqRefl _)
      (f_le_one hw' (monus_le' one (sg (inst2 v (var 0) (Syn.shift z)))))
    exact (eq_add_of_le hf).eqSymm
  exact (sum_add (fB v) (cB v) r (pairT w z)).eqSymm.eqTrans (hc.eqTrans (sum_ones r _))

/-- `rs ≤ r w`: a covered coarse cell stays covered. -/
theorem cell_res (v : PTm 2) (w r z : PTm n) :
    Γ ⊢[PRAAx] le (ap2 (sumF (fB v)) r (pairT w z)) (r * w) := by
  refine sum_le_const (fB v) (.allI (.impI ?_))
  rw [show Syn.shift (pairT w z) = pairT (Syn.shift w) (Syn.shift z) by simp [Syn.shift]]
  exact le_congr (fB_at v (var 0) (Syn.shift w) (Syn.shift z)).eqSymm (.eqRefl _)
    (f_le_w (monus_le' one (sg (inst2 v (var 0) (Syn.shift z)))))

/-- The (K11) count `w r ≤ (c+1) Σ_k sg(v(k))` gives `w r ≤ (c+1) cv`. -/
theorem cell_cov (v : PTm 2) {w r c z : PTm n} (hw : Γ ⊢[PRAAx] le w one)
    (hK : Γ ⊢[PRAAx] le (w * r) (succ c * ap2 (sumF (sg v)) r z)) :
    Γ ⊢[PRAAx] le (w * r) (succ c * ap2 (sumF (cB v)) r (pairT w z)) := by
  have hs : Γ ⊢[PRAAx] le (ap2 (sumF (sg v)) r z) (ap2 (sumF (cB v)) r (pairT w z)) := by
    refine sum_le_params _ _ _ _ _ (.allI (.impI ?_))
    have hw0 : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift w) one := by simpa [Fm.shift, Syn.shift] using hw.shift
    have hw' : (lt (var 0) (Syn.shift r) :: Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift w) one := hw0.wk
    rw [inst2_cB, show Syn.shift (pairT w z) = pairT (Syn.shift w) (Syn.shift z) by simp [Syn.shift],
      show inst2 (sg v) (var 0 : PTm (n + 1)) (Syn.shift z) = sg (inst2 v (var 0) (Syn.shift z)) by simp [inst2]]
    exact le_congr (.eqRefl _) (congrMonus (.eqRefl _) (fB_at v (var 0) (Syn.shift w) (Syn.shift z))).eqSymm
      (sg_le_cov hw')
  ipra_le sl hK + (𝔞 c + 1) * sl hs

end LeanProofs.IPRA.DiophantineNumberTheory.KhinchinRoundBits
