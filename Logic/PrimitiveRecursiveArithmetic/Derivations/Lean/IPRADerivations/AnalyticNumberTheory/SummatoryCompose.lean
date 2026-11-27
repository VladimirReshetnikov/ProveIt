import IPRADerivations.AnalyticNumberTheory.SymmetryBound

/-!
# Hyperbola sums of monotone functions (`pnt_ipra_constructive_2026-11-14`, towards `sb:weighted-sum`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `selberg.tex`, proof of Lemma `sb:weighted-sum`:
the exact identity for `R(x)(log x)²` rearranges sums `Σ_{n≤x} a(n) H(x/n)` of a monotone step function
`H` (`ψ`, `ψ · log`, `⌊·⌋`) and sums over `ab ≤ x`. In finite form every such sum is a summatory function of a
Dirichlet convolution: for a body `H` with `H(0) = 0` and `H(k) ≤ H(k+1)`,

  `Σ_{1≤d≤x} a(d) H(⌊x/d⌋) = Σ_{n≤x} (a * ΔH)(n)`,  `ΔH(j) = H(j) − H(j − 1)`.

* `dH`, `inst2_dH`, `tele`: `Σ_{k≤m} ΔH(k) = H(m) − H(0)` (closed QF induction; monotonicity is a schematic
  hypothesis on the body, so it is used at the induction variable itself);
* `hRB`, `compose`: the displayed identity, from `ConvSummatory.conv_summatory` with `b = ΔH`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.SummatoryCompose

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.ConvSummatory (bS inst2_bS Bs RB RB_at conv_summatory)
open LeanProofs.IPRA.Signum (sg)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

section Compose

variable (h : PTm 2)

/-- `ΔH(j) = H(j) − H(j − 1)` (truncated; `ΔH(0) = 0`). -/
def dH : PTm 2 := monus h (Syn.subst ![pred (var 0), var 1] h)

theorem inst2_dH (k y : PTm n) : inst2 (dH h) k y = monus (inst2 h k y) (inst2 h (pred k) y) := by
  have e : Syn.subst ![k, y] (Syn.subst ![pred (var 0), var 1] h) = inst2 h (pred k) y := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext i; fin_cases i <;> simp
  simp only [inst2, dH, PTm.subst_monus] at e ⊢
  rw [e]

/-- Monotonicity of `H` at every argument and parameter, as a schematic hypothesis. -/
def Mono : Prop := ∀ {m : ℕ} {Δ : List (Fm PTm m)} (k y : PTm m), Δ ⊢[PRAAx] le (inst2 h k y) (inst2 h (succ k) y)

/-- `Σ_{k≤m} ΔH(k) + H(0) = H(m)`, over `0 = m`, `1 = y`. -/
private abbrev teleF : Fm PTm 2 := Bs (dH h) (var 0) (var 1) + inst2 h zero (var 1) ≐ inst2 h (var 0) (var 1)

private theorem tele₀ (hm : Mono h) : ([] : List (Fm PTm 2)) ⊢[PRAAx] teleF h := by
  ipra_ind [subst_ap2, subst_inst2]
  · exact (congrAdd (sum_zero _ _) (.eqRefl _)).eqTrans (zero_add _)
  · have s := sum_succ' (Γ := [teleF h]) (bS (dH h)) (var 0) (var 1)
    rw [inst2_bS, inst2_dH] at s
    have mo := natEq (eq_add_of_le (hm (Δ := [teleF h]) (var 0) (var 1)))
    have mo' : [teleF h] ⊢[PRAAx] monus (inst2 h (succ (var 0)) (var 1)) (inst2 h (pred (succ (var 0))) (var 1)) ≐
        monus (inst2 h (succ (var 0)) (var 1)) (inst2 h (var 0) (var 1)) :=
      congrMonus (.eqRefl _) (congrInst2 h (pred_succ _) (.eqRefl _))
    ipra_lc natEq s + natEq (Prf.hyp0 : [teleF h] ⊢[PRAAx] _) + natEq mo' - mo

/-- `Σ_{k<m} ΔH(k + 1) = H(m) − H(0)`. -/
theorem tele (hm : Mono h) (m y : PTm n) : Γ ⊢[PRAAx] Bs (dH h) m y + inst2 h zero y ≐ inst2 h m y := by
  have i := inst (Γ := Γ) (tele₀ h hm) (![m, y] : Fin 2 → PTm n)
  simpa using i

variable (a : PTm 2)

/-- `[d ≥ 1] a(d, y) H(⌊x/d⌋, y)` over `0 = d`, `1 = (x, y)`. -/
def hRB : PTm 2 := (sg (var 0) * Syn.subst ![var 0, sndT (var 1)] a) *
  Syn.subst ![quo (fstT (var 1)) (var 0), sndT (var 1)] h

theorem inst2_hRB (d z : PTm n) :
    inst2 (hRB h a) d z = (sg d * inst2 a d (sndT z)) * inst2 h (quo (fstT z) d) (sndT z) := by
  have ha : Syn.subst ![d, z] (Syn.subst ![var 0, sndT (var 1)] a) = inst2 a d (sndT z) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext i; fin_cases i <;> simp
  have hh : Syn.subst ![d, z] (Syn.subst ![quo (fstT (var 1)) (var 0), sndT (var 1)] h) =
      inst2 h (quo (fstT z) d) (sndT z) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext i; fin_cases i <;> simp
  simp only [inst2, hRB, PTm.subst_mul, ha, hh]
  simp [sg]

/-- `Σ_{1≤d≤x} a(d) H(⌊x/d⌋) = Σ_{n≤x} (a * ΔH)(n)` for monotone `H` with `H(0) = 0`. -/
theorem compose (hm : Mono h) (h0 : ∀ {m : ℕ} {Δ : List (Fm PTm m)} (y : PTm m), Δ ⊢[PRAAx] inst2 h zero y ≐ zero)
    (x y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (hRB h a)) (succ x) (pairT x y) ≐ ap2 (sumF (cvF a (dH h))) (succ x) y := by
  refine .eqTrans ?_ (conv_summatory a (dH h) x y).eqSymm
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [inst2_hRB, shift_pairT]
  refine .eqTrans ?_ (RB_at a (dH h) _ _ _).eqSymm
  ipra_lc (𝔞 (sg (var 0)) * 𝔞 (inst2 h (quo (fstT (pairT (Syn.shift x) (Syn.shift y))) (var 0)) (sndT (pairT (Syn.shift x) (Syn.shift y))))) * natEq (congrInst2 (Γ := (lt (var 0) (Syn.shift (succ x)) :: Γ.map Fm.shift)) a (.eqRefl (var 0)) (snd_pair (Syn.shift x) (Syn.shift y))) +
    𝔞 (sg (var 0)) * 𝔞 (inst2 a (var 0) (Syn.shift y)) * (natEq (congrInst2 (Γ := (lt (var 0) (Syn.shift (succ x)) :: Γ.map Fm.shift)) h (congrAp2 quoF (fst_pair (Syn.shift x) (Syn.shift y)) (.eqRefl (var 0))) (snd_pair (Syn.shift x) (Syn.shift y))) - natEq (tele (Γ := (lt (var 0) (Syn.shift (succ x)) :: Γ.map Fm.shift)) h hm (quo (Syn.shift x) (var 0)) (Syn.shift y)) + natEq (h0 (Δ := (lt (var 0) (Syn.shift (succ x)) :: Γ.map Fm.shift)) (Syn.shift y)))

end Compose

end LeanProofs.IPRA.AnalyticNumberTheory.SummatoryCompose

export_ipra AnalyticNumberTheory.SummatoryCompose (Mono inst2_hRB)
