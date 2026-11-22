import IPRADerivations.DiophantineNumberTheory.KhinchinK2Step
import IPRADerivations.DiophantineNumberTheory.KhinchinRounds

/-!
# The divergent Khinchin theorem (K2), end to end (`hurwitz_khinchin_ipra`)

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`, (K2): "Suppose `ψ` is nonincreasing and a
unit-tail modulus `D` satisfies `D(s) ≥ s`, `Σ_{q=s}^{D(s)} ψ(q) ≥ 1` (K-D). There is a primitive recursive
construction … that takes `N ≥ 1` and `m ≥ 0` and returns … `|[0,1] ∖ U(N,m)| < 2^{-m}`", proved in §"Amplification
by the finitely many residual gaps": "Set `b₀ = 16384`. Start with the empty union `U₀` … After `T = b₀(m+1)`
stages we therefore have `R_T ≤ 2^{-(m+1)} < 2^{-m}`."

Here `ψ(q) = Ψ(q, x)/C` with a natural-valued numerator body `Ψ`, denominator `C ≥ 1`, monotonicity `monoF` and
the modulus `D` as a body `Dm` with (K-D) cleared (`kdF`: `C + Σ_{q<s} Ψ ≤ Σ_{q<D(s)+1} Ψ` for `s ≥ 1`;
`D(s) ≥ s` is not needed). The construction is one primitive recursion on the round `j`, with parameter
`P = ⟨N, ⟨C, x⟩⟩` and state `S_j = ⟨p_j, c_j⟩`:

* the coarse grid of round `j` has `G_j = p_j + 1` cells, `c_j` is the binary code of their residual bits
  (`G_0 = 1`, `c_0 = 1`: the whole interval is uncovered);
* round `j` places the block of `KhinchinK2Widths.cell_cover` in every cell (with `K₀ = 512 G_j + N`, so all
  denominators exceed `2^{K₀−2} ≥ N`) and refines every cell into `r_j` fine cells
  (`KhinchinK2Step.nextS`): `G_{j+1} = r_j G_j` and `c_{j+1}` codes the fine cells missed by all blocks so far;
* `resK j P = Σ_{g<G_j} w_g` counts the uncovered cells of the grid `gridK j P = G_j`, so the residual measure
  `|[0,1] ∖ U_j|` is at most `resK / gridK` (the block intervals have endpoints on the fine grid).

Results:

* `step_ineq`: `16384^{j+1} ρ_{j+1} ≤ 16383^{j+1} G_{j+1}` from the same at `j` (`KhinchinK2Step.round_step`,
  `G_{j+1} = r_j G_j`);
* `inv_all`: `16384^j ρ_j ≤ 16383^j G_j` for every round `j` (one QF induction);
* `khinchin_k2`: after `T = 16384 (m+1)` rounds, `2^{m+1} ρ_T ≤ G_T`, i.e. `|[0,1] ∖ U| ≤ 2^{−(m+1)}`
  (the binomial bound `KhinchinAmplify.half_bound` raised to the power `m+1`, then cancelling `16384^T`);
* `khinchin_k2_strict`: `2^m ρ_T < G_T`, i.e. the packet's `|[0,1] ∖ U(N, m)| < 2^{−m}`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.KhinchinK2

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.FiniteSetExponential (code dg_lt)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinAmplify (half_bound pow_amp)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinK2Widths (monoF kdF subst_monoF subst_kdF mono_shift sh
  pos_of_one wbK)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinK2Step (rr xr tB evB inst2_evB two_pos round_step hr_r)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Transport of the hypotheses on `ψ` -/

theorem monoF_congr (Ψ : PTm 2) {x x' : PTm n} (e : Γ ⊢[PRAAx] x' ≐ x) (h : Γ ⊢[PRAAx] monoF Ψ x) :
    Γ ⊢[PRAAx] monoF Ψ x' := by
  have a := mono_shift Ψ h (var 0)
  have e' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift x' ≐ Syn.shift x := by simpa [Fm.shift, Syn.shift] using e.shift
  unfold monoF
  exact .allI (le_congr (congrInst2 Ψ (.eqRefl _) e'.eqSymm) (congrInst2 Ψ (.eqRefl _) e'.eqSymm) a)

theorem kdF_congr (Ψ Dm : PTm 2) {C C' x x' : PTm n} (eC : Γ ⊢[PRAAx] C' ≐ C) (ex : Γ ⊢[PRAAx] x' ≐ x)
    (h : Γ ⊢[PRAAx] kdF Ψ Dm C x) : Γ ⊢[PRAAx] kdF Ψ Dm C' x' := by
  unfold kdF at h ⊢
  refine .allI (.impI ?_)
  have a := Prf.impE (h.allOpen.wk (ψ := le one (var 0))) Prf.hyp0
  have eC' : (le one (var 0) :: Γ.map Fm.shift) ⊢[PRAAx] Syn.shift C' ≐ Syn.shift C := by
    simpa [Fm.shift, Syn.shift] using eC.shift.wk (ψ := le one (var 0))
  have ex' : (le one (var 0) :: Γ.map Fm.shift) ⊢[PRAAx] Syn.shift x' ≐ Syn.shift x := by
    simpa [Fm.shift, Syn.shift] using ex.shift.wk (ψ := le one (var 0))
  exact le_congr (congrAdd eC'.eqSymm (congrAp2 (sumF Ψ) (.eqRefl _) ex'.eqSymm))
    (congrAp2 (sumF Ψ) (congrSucc (congrInst2 Dm (.eqRefl _) ex'.eqSymm)) ex'.eqSymm) a

/-! ## The construction -/

/-- The next state `⟨p', c'⟩`: `p' + 1 = r (p + 1)` fine cells, `c'` the code of their residual bits. -/
def nextS (Ψ Dm : PTm 2) (p c N C x : PTm n) : PTm n :=
  pairT (pred (rr Dm p N C x * succ p))
    (code (tB (wbK Ψ)) (rr Dm p N C x * succ p) two (pairT c (xr Dm p N C x)))

@[simp] theorem subst_nextS {m : ℕ} (σ : Fin n → PTm m) (Ψ Dm : PTm 2) (p c N C x : PTm n) :
    Syn.subst σ (nextS Ψ Dm p c N C x) =
      nextS Ψ Dm (Syn.subst σ p) (Syn.subst σ c) (Syn.subst σ N) (Syn.subst σ C) (Syn.subst σ x) := by
  simp [nextS, xr, LeanProofs.IPRA.DiophantineNumberTheory.KhinchinRoundWrapper.px, subst_ap2]

/-- The round step as a body over `0 = j`, `1 = S_j`, `2 = P = ⟨N, ⟨C, x⟩⟩`. -/
def stepB (Ψ Dm : PTm 2) : PTm 3 :=
  nextS Ψ Dm (fstT (var 1)) (sndT (var 1)) (fstT (var 2)) (fstT (sndT (var 2))) (sndT (sndT (var 2)))

/-- The initial state: one cell, uncovered. -/
def baseB : PTm 1 := pairT zero one

/-- The state `S_j` after `j` rounds. -/
def Sk (Ψ Dm : PTm 2) (j P : PTm n) : PTm n := ap2 (rec2 baseB (stepB Ψ Dm)) j P

/-- The uncovered cells after `j` rounds: `ρ_j = Σ_{g<G_j} w_g`. -/
def resK (Ψ Dm : PTm 2) (j P : PTm n) : PTm n := ap2 (sumF evB) (succ (fstT (Sk Ψ Dm j P))) (sndT (Sk Ψ Dm j P))

/-- The grid after `j` rounds: `G_j` cells. -/
def gridK (Ψ Dm : PTm 2) (j P : PTm n) : PTm n := succ (fstT (Sk Ψ Dm j P))

/-- The amplification invariant `16384^j ρ_j ≤ 16383^j G_j`. -/
def invF (Ψ Dm : PTm 2) (j P : PTm n) : Fm PTm n :=
  le (pw (succ (num 16383)) j * resK Ψ Dm j P) (pw (num 16383) j * gridK Ψ Dm j P)

@[simp] theorem subst_Sk {m : ℕ} (σ : Fin n → PTm m) (Ψ Dm : PTm 2) (j P : PTm n) :
    Syn.subst σ (Sk Ψ Dm j P) = Sk Ψ Dm (Syn.subst σ j) (Syn.subst σ P) := by simp [Sk, subst_ap2]

@[simp] theorem subst_resK {m : ℕ} (σ : Fin n → PTm m) (Ψ Dm : PTm 2) (j P : PTm n) :
    Syn.subst σ (resK Ψ Dm j P) = resK Ψ Dm (Syn.subst σ j) (Syn.subst σ P) := by simp [resK, subst_ap2]

@[simp] theorem subst_gridK {m : ℕ} (σ : Fin n → PTm m) (Ψ Dm : PTm 2) (j P : PTm n) :
    Syn.subst σ (gridK Ψ Dm j P) = gridK Ψ Dm (Syn.subst σ j) (Syn.subst σ P) := by simp [gridK]

@[simp] theorem subst_invF {m : ℕ} (σ : Fin n → PTm m) (Ψ Dm : PTm 2) (j P : PTm n) :
    (invF Ψ Dm j P).subst σ = invF Ψ Dm (Syn.subst σ j) (Syn.subst σ P) := by
  simp [invF, subst_ap2]

theorem S_zero (Ψ Dm : PTm 2) (P : PTm n) : Γ ⊢[PRAAx] Sk Ψ Dm zero P ≐ pairT zero one := by
  simpa [baseB, Sk] using rec2_zero (Γ := Γ) baseB (stepB Ψ Dm) P

theorem S_succ (Ψ Dm : PTm 2) (j P : PTm n) :
    Γ ⊢[PRAAx] Sk Ψ Dm (succ j) P ≐
      nextS Ψ Dm (fstT (Sk Ψ Dm j P)) (sndT (Sk Ψ Dm j P)) (fstT P) (fstT (sndT P)) (sndT (sndT P)) := by
  have h := rec2_succ (Γ := Γ) baseB (stepB Ψ Dm) j P
  have e : Syn.subst ![j, ap2 (rec2 baseB (stepB Ψ Dm)) j P, P] (stepB Ψ Dm) =
      nextS Ψ Dm (fstT (Sk Ψ Dm j P)) (sndT (Sk Ψ Dm j P)) (fstT P) (fstT (sndT P)) (sndT (sndT P)) := by
    simp [stepB, Sk]
  rw [e] at h
  exact h

/-! ## The invariant -/

/-- Round `0`: `ρ_0 ≤ G_0 = 1`. -/
theorem base_ineq (Ψ Dm : PTm 2) {S : PTm n} (hS : Γ ⊢[PRAAx] S ≐ pairT zero one) :
    Γ ⊢[PRAAx] le (pw (succ (num 16383)) zero * ap2 (sumF evB) (succ (fstT S)) (sndT S))
      (pw (num 16383) zero * succ (fstT S)) := by
  have ef0 : Γ ⊢[PRAAx] fstT S ≐ zero := (congrFst hS).eqTrans (fst_pair _ _)
  have es0 : Γ ⊢[PRAAx] sndT S ≐ one := (congrSnd hS).eqTrans (snd_pair _ _)
  have eA0 : Γ ⊢[PRAAx] ap2 (sumF evB) (succ (fstT S)) (sndT S) ≐ ap2 (sumF evB) zero one + inst2 evB zero one :=
    (congrAp2 (sumF evB) (congrSucc ef0) es0).eqTrans (sum_succ evB zero one)
  have hd : Γ ⊢[PRAAx] lt (inst2 evB zero one) two := by
    rw [inst2_evB]; exact dg_lt two_pos zero one
  have eZ := natEq (sum_zero (Γ := Γ) evB one)
  have e1 := natEq (pw_zero (Γ := Γ) (succ (num 16383)))
  have e2 := natEq (pw_zero (Γ := Γ) (num 16383))
  have eG := natEq ef0
  have eA := natEq eA0
  ipra_le sl hd with (𝔞 (fstT S) + 1) * e2 + eG - 𝔞 (ap2 (sumF evB) (succ (fstT S)) (sndT S)) * e1 - eA - eZ

/-- One round of the invariant. -/
theorem step_ineq (Ψ Dm : PTm 2) {j p c N C x S' : PTm n}
    (hS' : Γ ⊢[PRAAx] S' ≐ nextS Ψ Dm p c N C x) (hC : Γ ⊢[PRAAx] le one C) (hmono : Γ ⊢[PRAAx] monoF Ψ x)
    (hKD : Γ ⊢[PRAAx] kdF Ψ Dm C x)
    (IH : Γ ⊢[PRAAx] le (pw (succ (num 16383)) j * ap2 (sumF evB) (succ p) c) (pw (num 16383) j * succ p)) :
    Γ ⊢[PRAAx] le (pw (succ (num 16383)) (succ j) * ap2 (sumF evB) (succ (fstT S')) (sndT S'))
      (pw (num 16383) (succ j) * succ (fstT S')) := by
  have RS := round_step Ψ Dm (p := p) (c := c) (N := N) hC hmono hKD
  have ef : Γ ⊢[PRAAx] fstT S' ≐ pred (rr Dm p N C x * succ p) := (congrFst hS').eqTrans (fst_pair _ _)
  have es : Γ ⊢[PRAAx] sndT S' ≐ code (tB (wbK Ψ)) (rr Dm p N C x * succ p) two (pairT c (xr Dm p N C x)) :=
    (congrSnd hS').eqTrans (snd_pair _ _)
  have er := natEq (hr_r (Γ := Γ) Dm (p := p) (N := N) (x := x) hC)
  have hN : Γ ⊢[PRAAx] rr Dm p N C x * succ p ≐ succ (pred (rr Dm p N C x * succ p)) := by
    refine pos_of_one ?_
    ipra_le 𝔞 (pred (rr Dm p N C x)) * 𝔞 p + 𝔞 (pred (rr Dm p N C x)) + 𝔞 p with (𝔞 p + 1) * er
  have eR := natEq (congrAp2 (sumF evB) (congrSucc ef) es)
  have eG := natEq ((congrSucc ef).eqTrans hN.eqSymm)
  have pb := natEq (pw_succ (Γ := Γ) (succ (num 16383)) j)
  have pc := natEq (pw_succ (Γ := Γ) (num 16383) j)
  ipra_le 𝔞 (pw (succ (num 16383)) j) * sl RS + 16383 * 𝔞 (rr Dm p N C x) * sl IH with
    (𝔞 (fstT S') + 1) * pc + 16383 * 𝔞 (pw (num 16383) j) * eG -
      𝔞 (ap2 (sumF evB) (succ (fstT S')) (sndT S')) * pb - 16384 * 𝔞 (pw (succ (num 16383)) j) * eR

/-- The invariant for every round, with the hypotheses on the decoded parameters. -/
theorem inv_all (Ψ Dm : PTm 2) {P : PTm n} (hC : Γ ⊢[PRAAx] le one (fstT (sndT P)))
    (hmono : Γ ⊢[PRAAx] monoF Ψ (sndT (sndT P))) (hKD : Γ ⊢[PRAAx] kdF Ψ Dm (fstT (sndT P)) (sndT (sndT P))) :
    Γ ⊢[PRAAx] Fm.all (invF Ψ Dm (var 0) (Syn.shift P)) := by
  refine PRA.qfInd _ (le_QF _ _) ?_ ?_
  · simp only [subst_invF, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
    exact base_ineq Ψ Dm (S_zero Ψ Dm P)
  · simp only [subst_invF, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
    let ψ0 : Fm PTm (n + 1) := invF Ψ Dm (var 0) (Syn.shift P)
    have hC' : (ψ0 :: Γ.map Fm.shift) ⊢[PRAAx] le one (fstT (sndT (Syn.shift P))) := by
      simpa [Fm.shift, Syn.shift] using sh ψ0 hC
    have hm' : (ψ0 :: Γ.map Fm.shift) ⊢[PRAAx] monoF Ψ (sndT (sndT (Syn.shift P))) := by
      simpa [Fm.shift, Syn.shift] using sh ψ0 hmono
    have hk' : (ψ0 :: Γ.map Fm.shift) ⊢[PRAAx] kdF Ψ Dm (fstT (sndT (Syn.shift P))) (sndT (sndT (Syn.shift P))) := by
      simpa [Fm.shift, Syn.shift] using sh ψ0 hKD
    exact step_ineq Ψ Dm (S_succ Ψ Dm (var 0) (Syn.shift P)) hC' hm' hk' Prf.hyp0

/-! ## (K2) -/

/-- **(K2), divergent Khinchin**: for nonincreasing `ψ = Ψ(·, x)/C` with a unit-tail modulus, after
`T = 16384 (m+1)` rounds the uncovered part of the final grid is at most `2^{−(m+1)}`:
`2^{m+1} ρ_T ≤ G_T`. -/
theorem khinchin_k2 (Ψ Dm : PTm 2) {N C x : PTm n} (m : PTm n) (hC : Γ ⊢[PRAAx] le one C)
    (hmono : Γ ⊢[PRAAx] monoF Ψ x) (hKD : Γ ⊢[PRAAx] kdF Ψ Dm C x) :
    Γ ⊢[PRAAx] le (pw two (succ m) * resK Ψ Dm (succ (num 16383) * succ m) (pairT N (pairT C x)))
      (gridK Ψ Dm (succ (num 16383) * succ m) (pairT N (pairT C x))) := by
  have e1 : Γ ⊢[PRAAx] sndT (pairT N (pairT C x)) ≐ pairT C x := snd_pair _ _
  have eC : Γ ⊢[PRAAx] fstT (sndT (pairT N (pairT C x))) ≐ C := (congrFst e1).eqTrans (fst_pair _ _)
  have ex : Γ ⊢[PRAAx] sndT (sndT (pairT N (pairT C x))) ≐ x := (congrSnd e1).eqTrans (snd_pair _ _)
  have inv := inv_all Ψ Dm (le_congr (.eqRefl _) eC.eqSymm hC) (monoF_congr Ψ ex hmono) (kdF_congr Ψ Dm eC ex hKD)
  have hT := Prf.allE (succ (num 16383) * succ m) inv
  simp only [subst_invF, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at hT
  unfold invF at hT
  have pd0 := pow_amp (le_of_lt (half_bound (Γ := Γ) (num 16383))) (succ m)
  have pd : Γ ⊢[PRAAx] le (pw two (succ m) * pw (num 16383) (succ (num 16383) * succ m))
      (pw (succ (num 16383)) (succ (num 16383) * succ m)) :=
    le_congr (congrMul (.eqRefl _) (AnalyticNumberTheory.RSA.pw_mul (num 16383) (succ (num 16383)) (succ m)))
      (AnalyticNumberTheory.RSA.pw_mul (succ (num 16383)) (succ (num 16383)) (succ m)) pd0
  have hB : Γ ⊢[PRAAx] le (pw (succ (num 16383)) (succ (num 16383) * succ m) *
        (pw two (succ m) * resK Ψ Dm (succ (num 16383) * succ m) (pairT N (pairT C x))))
      (pw (succ (num 16383)) (succ (num 16383) * succ m) *
        gridK Ψ Dm (succ (num 16383) * succ m) (pairT N (pairT C x))) := by
    ipra_le 𝔞 (pw two (succ m)) * sl hT + 𝔞 (gridK Ψ Dm (succ (num 16383) * succ m) (pairT N (pairT C x))) * sl pd
  have pos := DiophantineNumberTheory.FLTMultiples.pw_pos (Γ := Γ) (num 16383) (succ (num 16383) * succ m)
  exact mul_le_cancel (le_congr (congrMul pos (.eqRefl _)) (congrMul pos (.eqRefl _)) hB)

/-- **(K2)** in the packet's form `|[0,1] ∖ U(N, m)| < 2^{−m}`: `2^m ρ_T < G_T`. -/
theorem khinchin_k2_strict (Ψ Dm : PTm 2) {N C x : PTm n} (m : PTm n) (hC : Γ ⊢[PRAAx] le one C)
    (hmono : Γ ⊢[PRAAx] monoF Ψ x) (hKD : Γ ⊢[PRAAx] kdF Ψ Dm C x) :
    Γ ⊢[PRAAx] lt (pw two m * resK Ψ Dm (succ (num 16383) * succ m) (pairT N (pairT C x)))
      (gridK Ψ Dm (succ (num 16383) * succ m) (pairT N (pairT C x))) := by
  have h := khinchin_k2 Ψ Dm (N := N) m hC hmono hKD
  have hG : Γ ⊢[PRAAx] le one (gridK Ψ Dm (succ (num 16383) * succ m) (pairT N (pairT C x))) := by
    unfold gridK; ipra_le 𝔞 (fstT (Sk Ψ Dm (succ (num 16383) * succ m) (pairT N (pairT C x))))
  refine .orE (lt_or_le (pw two m * resK Ψ Dm (succ (num 16383) * succ m) (pairT N (pairT C x))) one) ?_ ?_
  · exact lt_of_lt_of_le Prf.hyp0 hG.wk
  · have h' := h.wk (ψ := le one (pw two m * resK Ψ Dm (succ (num 16383) * succ m) (pairT N (pairT C x))))
    have e' := natEq (pw_succ (Γ := le one (pw two m * resK Ψ Dm (succ (num 16383) * succ m) (pairT N (pairT C x)))
      :: Γ) two m)
    ipra_le sl h' + sl Prf.hyp0 with 𝔞 (resK Ψ Dm (succ (num 16383) * succ m) (pairT N (pairT C x))) * e'

end LeanProofs.IPRA.DiophantineNumberTheory.KhinchinK2
