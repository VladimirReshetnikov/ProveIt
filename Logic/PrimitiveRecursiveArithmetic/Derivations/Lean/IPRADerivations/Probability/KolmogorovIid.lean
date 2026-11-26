import IPRADerivations.Probability.KolmogorovAssembly
import IPRADerivations.Probability.ProductSplit
import IPRADerivations.Probability.FirstCrossing

/-!
# Kolmogorov's maximal inequality for an iid sample: the data of one crossing step

Packet: `probability/expected_value_ipra_2026-11-16`, `thm:kolmogorov`, for the `n`-fold product law of
`Probability/ProductPower` (outcomes `a < M` with weight `w`, values `X`, `W = ∑ w`, `S = ∑ w X`). The
partial sums are centred and cleared, `W S_l − l S = W (S_l − l μ)`, and the levels are
`D_l = |W S_l − l S|²`; the threshold is a body `a` (`c = a²`).

For one crossing index `k` and the future length `m`, the parameter `Y = ⟨k, ⟨m, ⟨M, x⟩⟩⟩` carries both
block lengths, and the data of `Probability/KolmogorovStep.crossing_step` are:

* the past weight `P_k(j) I_k(j)` (`I_k` the first-crossing indicator of `Probability/FirstCrossing`) and
  the future weight `P_m(i)`;
* the past partial sum `W S_k(j) − k S` and the increment `W S_m(i) − m S`, by their natural parts.

This file derives the two hypotheses of `crossing_step` for these data:

* `past_hyp`: on the past outcomes, `P_k I_k a² ≤ P_k I_k (W S_k − k S)²` (the crossing condition);
* `future_mean`: the increment has mean zero, `∑_i P_m(i) W S_m(i) = ∑_i P_m(i) m S`, from
  `sample_moments` (`W A_m = m S T_m`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.KolmogorovIid

open_ipra
open LeanProofs.IPRA.Probability.Expectation (Ew Wt inst2_mul' inst2_add')
open LeanProofs.IPRA.Probability.Independence (sum_scale shift_sum)
open LeanProofs.IPRA.Probability.Variance (ad)
open LeanProofs.IPRA.Probability.ProductPower (Pr Sr TB SB TB_at SB_at AB At Tt sample_moments wdB xdB)
open LeanProofs.IPRA.Probability.FirstCrossing (Ib inst2_Ib crossing_bound)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem congrAd {a a' b b' : PTm n} (h₁ : Γ ⊢[PRAAx] a ≐ a') (h₂ : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] ad a b ≐ ad a' b' :=
  congrAdd (congrMonus h₁ h₂) (congrMonus h₂ h₁)

/-! ## Reparametrized bodies -/

/-- `f(j, ρ(j, y))`. -/
def rp (f ρ : PTm 2) : PTm 2 := Syn.subst ![var 0, ρ] f

theorem inst2_rp (f ρ : PTm 2) (j y : PTm n) : inst2 (rp f ρ) j y = inst2 f j (inst2 ρ j y) := by
  simp only [inst2, rp, Syn.subst_subst]
  congr 1; funext i; fin_cases i <;> simp

/-- `⟨k, ⟨M, x⟩⟩` from `⟨k, ⟨m, ⟨M, x⟩⟩⟩`. -/
abbrev ρk : PTm 2 := pairT (fstT (var 1)) (sndT (sndT (var 1)))
/-- `⟨m, ⟨M, x⟩⟩` from `⟨k, ⟨m, ⟨M, x⟩⟩⟩`. -/
abbrev ρm : PTm 2 := pairT (fstT (sndT (var 1))) (sndT (sndT (var 1)))

/-- The parameter `⟨k, ⟨m, ⟨M, x⟩⟩⟩`. -/
abbrev Yp (k m M x : PTm n) : PTm n := pairT k (pairT m (pairT M x))

theorem rpk_at (f : PTm 2) (j k m M x : PTm n) :
    Γ ⊢[PRAAx] inst2 (rp f ρk) j (Yp k m M x) ≐ inst2 f j (pairT k (pairT M x)) := by
  rw [inst2_rp]
  have e : inst2 ρk j (Yp k m M x) =
      pairT (fstT (Yp k m M x)) (sndT (sndT (Yp k m M x))) := by simp [inst2]
  rw [e]
  exact congrInst2 f (.eqRefl _) (congrPairT (fst_pair _ _) (snd_pair _ _).sndE)

theorem rpm_at (f : PTm 2) (j k m M x : PTm n) :
    Γ ⊢[PRAAx] inst2 (rp f ρm) j (Yp k m M x) ≐ inst2 f j (pairT m (pairT M x)) := by
  rw [inst2_rp]
  have e : inst2 ρm j (Yp k m M x) =
      pairT (fstT (sndT (Yp k m M x))) (sndT (sndT (Yp k m M x))) := by simp [inst2]
  rw [e]
  exact congrInst2 f (.eqRefl _) (congrPairT (snd_pair _ _).fstE
    (snd_pair _ _).sndE)

/-- The constant `∑_{a<M} g(a, x)`, over `(j, ⟨r, ⟨M, x⟩⟩)`. -/
abbrev Cs (g : PTm 2) : PTm 2 := ap2 (sumF g) (fstT (sndT (var 1))) (sndT (sndT (var 1)))

theorem Cs_at (g : PTm 2) (j r M x : PTm n) :
    Γ ⊢[PRAAx] inst2 (Cs g) j (pairT r (pairT M x)) ≐ ap2 (sumF g) M x := by
  have e : inst2 (Cs g) j (pairT r (pairT M x)) =
      ap2 (sumF g) (fstT (sndT (pairT r (pairT M x)))) (sndT (sndT (pairT r (pairT M x)))) := by simp [inst2]
  rw [e]
  exact congrAp2 (sumF g) (snd_pair _ _).fstE
    (snd_pair _ _).sndE

/-- The block length `r`, over `(j, ⟨r, ⟨M, x⟩⟩)`. -/
abbrev rv : PTm 2 := fstT (var 1)

theorem rv_at (j r z : PTm n) : Γ ⊢[PRAAx] inst2 rv j (pairT r z) ≐ r := by
  have e : inst2 rv j (pairT r z) = fstT (pairT r z) := by simp [inst2]
  rw [e]; exact fst_pair _ _

/-- `g(r, ⟨j, z⟩)` over `(j, ⟨r, z⟩)`: a body of the index `r` read at the past outcome `j`. -/
def kB (g : PTm 2) : PTm 2 := Syn.subst ![fstT (var 1), pairT (var 0) (sndT (var 1))] g

theorem kB_at (g : PTm 2) (j r z : PTm n) : Γ ⊢[PRAAx] inst2 (kB g) j (pairT r z) ≐ inst2 g r (pairT j z) := by
  have e : inst2 (kB g) j (pairT r z) = inst2 g (fstT (pairT r z)) (pairT j (sndT (pairT r z))) := by
    simp only [inst2, kB, Syn.subst_subst]
    congr 1; funext i; fin_cases i <;> simp
  rw [e]
  exact congrInst2 g (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))

section Data

variable (w X aB : PTm 2)

/-- The level `D_l(t) = |W S_l(t) − l S|²`, over `(l, ⟨t, ⟨M, x⟩⟩)`. -/
abbrev DB : PTm 2 :=
  ad (Cs w * ap2 (sumF (xdB X)) (var 0) (var 1)) (var 0 * Cs (w * X)) *
    ad (Cs w * ap2 (sumF (xdB X)) (var 0) (var 1)) (var 0 * Cs (w * X))

/-- The first-crossing indicator `I_k(t)` for the levels `D` and the threshold `a²`. -/
abbrev IB : PTm 2 := Ib (aB * aB) (DB w X)

theorem DB_at (l t M x : PTm n) :
    Γ ⊢[PRAAx] inst2 (DB w X) l (pairT t (pairT M x)) ≐
      ad (ap2 (sumF w) M x * Sr X l t M x) (l * ap2 (sumF (w * X)) M x) *
        ad (ap2 (sumF w) M x * Sr X l t M x) (l * ap2 (sumF (w * X)) M x) := by
  have e : inst2 (DB w X) l (pairT t (pairT M x)) =
      ad (inst2 (Cs w) l (pairT t (pairT M x)) * Sr X l t M x) (l * inst2 (Cs (w * X)) l (pairT t (pairT M x))) *
        ad (inst2 (Cs w) l (pairT t (pairT M x)) * Sr X l t M x)
          (l * inst2 (Cs (w * X)) l (pairT t (pairT M x))) := by
    simp [inst2]
  rw [e]
  have a := congrAd (congrMul (Cs_at (Γ := Γ) w l t M x) (.eqRefl (Sr X l t M x)))
    (congrMul (.eqRefl l) (Cs_at (Γ := Γ) (w * X) l t M x))
  exact congrMul a a

/-- The past weight `P_k(j) I_k(j)`. -/
abbrev wP : PTm 2 := rp (TB w * kB (IB w X aB)) ρk
/-- The future weight `P_m(i)`. -/
abbrev vF : PTm 2 := rp (TB w) ρm
/-- The natural parts of the past partial sum `W S_k − k S`. -/
abbrev Pp : PTm 2 := rp (Cs w * SB X) ρk
abbrev Np : PTm 2 := rp (rv * Cs (w * X)) ρk
/-- The natural parts of the increment `W S_m − m S`. -/
abbrev Pf : PTm 2 := rp (Cs w * SB X) ρm
abbrev Nf : PTm 2 := rp (rv * Cs (w * X)) ρm
/-- The threshold at the crossing index `k`. -/
abbrev aP : PTm 2 := rp (kB aB) ρk

section At

variable (j k m M x : PTm n)

theorem wP_at : Γ ⊢[PRAAx] inst2 (wP w X aB) j (Yp k m M x) ≐
    Pr w k j M x * inst2 (IB w X aB) k (pairT j (pairT M x)) := by
  refine (rpk_at _ j k m M x).eqTrans ?_
  rw [inst2_mul']
  exact congrMul (TB_at w j k M x) (kB_at _ j k (pairT M x))

theorem vF_at : Γ ⊢[PRAAx] inst2 (vF w) j (Yp k m M x) ≐ Pr w m j M x :=
  (rpm_at _ j k m M x).eqTrans (TB_at w j m M x)

theorem Pp_at : Γ ⊢[PRAAx] inst2 (Pp w X) j (Yp k m M x) ≐ ap2 (sumF w) M x * Sr X k j M x := by
  refine (rpk_at _ j k m M x).eqTrans ?_
  rw [inst2_mul']
  exact congrMul (Cs_at w j k M x) (SB_at X j k M x)

theorem Np_at : Γ ⊢[PRAAx] inst2 (Np w X) j (Yp k m M x) ≐ k * ap2 (sumF (w * X)) M x := by
  refine (rpk_at _ j k m M x).eqTrans ?_
  rw [inst2_mul']
  exact congrMul (rv_at j k (pairT M x)) (Cs_at (w * X) j k M x)

theorem Pf_at : Γ ⊢[PRAAx] inst2 (Pf w X) j (Yp k m M x) ≐ ap2 (sumF w) M x * Sr X m j M x := by
  refine (rpm_at _ j k m M x).eqTrans ?_
  rw [inst2_mul']
  exact congrMul (Cs_at w j m M x) (SB_at X j m M x)

theorem Nf_at : Γ ⊢[PRAAx] inst2 (Nf w X) j (Yp k m M x) ≐ m * ap2 (sumF (w * X)) M x := by
  refine (rpm_at _ j k m M x).eqTrans ?_
  rw [inst2_mul']
  exact congrMul (rv_at j m (pairT M x)) (Cs_at (w * X) j m M x)

theorem aP_at : Γ ⊢[PRAAx] inst2 (aP aB) j (Yp k m M x) ≐ inst2 aB k (pairT j (pairT M x)) :=
  (rpk_at _ j k m M x).eqTrans (kB_at aB j k (pairT M x))

end At

/-! ## The two hypotheses of the crossing step -/

/-- The crossing condition at one past outcome. -/
theorem past_pt (j k m M x : PTm n) :
    Γ ⊢[PRAAx] le (inst2 (wP w X aB) j (Yp k m M x) *
        (inst2 (aP aB) j (Yp k m M x) * inst2 (aP aB) j (Yp k m M x)))
      (inst2 (wP w X aB) j (Yp k m M x) *
        (ad (inst2 (Pp w X) j (Yp k m M x)) (inst2 (Np w X) j (Yp k m M x)) *
          ad (inst2 (Pp w X) j (Yp k m M x)) (inst2 (Np w X) j (Yp k m M x)))) := by
  have hc := crossing_bound (Γ := Γ) (aB * aB) (DB w X) k (pairT j (pairT M x))
  rw [show inst2 (aB * aB) k (pairT j (pairT M x)) =
      inst2 aB k (pairT j (pairT M x)) * inst2 aB k (pairT j (pairT M x)) from inst2_mul' _ _ _ _] at hc
  have u := congrAd (Pp_at (Γ := Γ) w X j k m M x) (Np_at (Γ := Γ) w X j k m M x)
  have hc' := le_congr (.eqRefl _) (congrMul (.eqRefl _) (DB_at (Γ := Γ) w X k j M x)) hc
  have ew := wP_at (Γ := Γ) w X aB j k m M x
  have ea := aP_at (Γ := Γ) aB j k m M x
  refine le_congr (congrMul ew.eqSymm (congrMul ea.eqSymm ea.eqSymm))
    (congrMul ew.eqSymm (congrMul u.eqSymm u.eqSymm)) ?_
  ipra_le 𝔟 (Pr w k j M x) * sl hc'

theorem past_hyp (k m M x : PTm n) :
    Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (pw M k)) ⟶
      le (inst2 (wP w X aB) (var 0) (Syn.shift (Yp k m M x)) *
          (inst2 (aP aB) (var 0) (Syn.shift (Yp k m M x)) * inst2 (aP aB) (var 0) (Syn.shift (Yp k m M x))))
        (inst2 (wP w X aB) (var 0) (Syn.shift (Yp k m M x)) *
          (ad (inst2 (Pp w X) (var 0) (Syn.shift (Yp k m M x))) (inst2 (Np w X) (var 0) (Syn.shift (Yp k m M x))) *
            ad (inst2 (Pp w X) (var 0) (Syn.shift (Yp k m M x)))
              (inst2 (Np w X) (var 0) (Syn.shift (Yp k m M x)))))) := by
  refine .allI (.impI ?_)
  simp only [Yp, shift_pairT]
  exact past_pt w X aB (var 0) _ _ _ _

/-- The increment has mean zero: `∑_i P_m(i) W S_m(i) = ∑_i P_m(i) m S`. -/
theorem future_mean {M x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (k m : PTm n) :
    Γ ⊢[PRAAx] Ew (vF w) (Pf w X) (pw M m) (Yp k m M x) ≐ Ew (vF w) (Nf w X) (pw M m) (Yp k m M x) := by
  have s₁ := sum_scale (Γ := Γ) (vF w * Pf w X) (AB w X) (pw M m) (ap2 (sumF w) M x) (pairT m (pairT M x))
    (Yp k m M x) (.allI (.impI (by
      simp only [Yp, shift_pairT, shift_sum]
      rw [inst2_mul']
      have a := vF_at (Γ := lt (var 0) (Syn.shift (pw M m)) :: Γ.map Fm.shift) w (var 0)
        (Syn.shift k) (Syn.shift m) (Syn.shift M) (Syn.shift x)
      have b := Pf_at (Γ := lt (var 0) (Syn.shift (pw M m)) :: Γ.map Fm.shift) w X (var 0)
        (Syn.shift k) (Syn.shift m) (Syn.shift M) (Syn.shift x)
      have c : inst2 (AB w X) (var 0) (pairT (Syn.shift m) (pairT (Syn.shift M) (Syn.shift x))) =
          inst2 (TB w) (var 0) (pairT (Syn.shift m) (pairT (Syn.shift M) (Syn.shift x))) *
            inst2 (SB X) (var 0) (pairT (Syn.shift m) (pairT (Syn.shift M) (Syn.shift x))) := by
        simp [inst2]
      rw [c]
      have t := natEq (TB_at (Γ := lt (var 0) (Syn.shift (pw M m)) :: Γ.map Fm.shift) w (var 0)
        (Syn.shift m) (Syn.shift M) (Syn.shift x))
      have s := natEq (SB_at (Γ := lt (var 0) (Syn.shift (pw M m)) :: Γ.map Fm.shift) X (var 0)
        (Syn.shift m) (Syn.shift M) (Syn.shift x))
      have a' := natEq a
      have b' := natEq b
      apply deriveNat; ipra_simps
      rw [a', b', t, s]; ring)))
  have s₂ := sum_scale (Γ := Γ) (vF w * Nf w X) (TB w) (pw M m) (m * ap2 (sumF (w * X)) M x)
    (pairT m (pairT M x)) (Yp k m M x) (.allI (.impI (by
      simp only [Yp, shift_pairT, shift_sum]
      rw [inst2_mul']
      have a := natEq (vF_at (Γ := lt (var 0) (Syn.shift (pw M m)) :: Γ.map Fm.shift) w (var 0)
        (Syn.shift k) (Syn.shift m) (Syn.shift M) (Syn.shift x))
      have b := natEq (Nf_at (Γ := lt (var 0) (Syn.shift (pw M m)) :: Γ.map Fm.shift) w X (var 0)
        (Syn.shift k) (Syn.shift m) (Syn.shift M) (Syn.shift x))
      have t := natEq (TB_at (Γ := lt (var 0) (Syn.shift (pw M m)) :: Γ.map Fm.shift) w (var 0)
        (Syn.shift m) (Syn.shift M) (Syn.shift x))
      have e : Syn.shift (m * ap2 (sumF (w * X)) M x) =
          Syn.shift m * ap2 (sumF (w * X)) (Syn.shift M) (Syn.shift x) := by simp [Syn.shift]
      rw [e]
      apply deriveNat; ipra_simps
      rw [a, b, t]; ring)))
  have sm := natEq (Prf.andE₁ (sample_moments (Γ := Γ) (x := x) w X hM m))
  have e₁ := natEq s₁
  have e₂ := natEq s₂
  apply deriveNat; ipra_simps
  rw [e₁, e₂]
  linear_combination sm

end Data

end LeanProofs.IPRA.Probability.KolmogorovIid
