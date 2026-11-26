import IPRADerivations.AnalyticNumberTheory.ChebyshevBlock
import IPRADerivations.AnalyticNumberTheory.HarmonicSignedMean
import IPRADerivations.AnalyticNumberTheory.WeightedBound
import IPRADerivations.DiophantineNumberTheory.KhinchinBlock
import IPRADerivations.Core.CommonLemmas
import IPRADerivations.Core.Header

/-!
# Floor comparisons for the signed block mean (`pnt_ipra_constructive_2026-11-14`, `con:signed`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `selberg.tex`, `sb:signed-integral`
(`∫_1^x R(t)/t² dt = A_1(x) − ψ(x)/x − log x`). In the Chebyshev block identity (`ChebyshevBlock.block_id`) the
sums `Σ_{n≤P} Λ(n)⌊x/n⌋` and `Σ_{n≤P} F⌊x/n⌋` occur; they are compared with `x A_1(P)` and `x F H_P`, i.e. with
`x S_w(P)/P!` (`HarmonicLambda.Sw`) and `x S(P, F)/F`:

* `floor_pair`: `B⌊x/k⌋ ≤ xc ≤ B⌊x/k⌋ + B` when `B = kc`, `k ≥ 1`;
* `lam_pt`: the same with `B = P!`, `c = P!/k` (`k ≤ P`) and a factor `Λ`;
* `lam_sum_lo`, `lam_sum_hi`: `P! Σ_{n≤P} Λ(n)⌊x/n⌋ ≤ x S_w(P) ≤ P! Σ_{n≤P} Λ(n)⌊x/n⌋ + P! ψ(P)`;
* `f_sum_lo`, `f_sum_hi`: `Σ_{n≤P} F⌊x/n⌋ ≤ x S(P, F) ≤ Σ_{n≤P} F⌊x/n⌋ + P F` for `F = L!`, `P ≤ L`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.BlockFloor

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB inst2_h)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (wt)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertens (le_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLambda (AB AB_at Sw)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogSum (fact_quo)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (Psi LamB inst2_LamB)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedMangoldt (Lam)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda (lam_zero)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedSplit (lamW)
open LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevBlock (gB gB_at)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorHarmonic (shift_fact')
open LeanProofs.IPRA.AnalyticNumberTheory.ConvSummatory (shift_succ_x)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (zero_mul_l congrSg)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBlock (sum_le_lin sum_le_lin1)
open LeanProofs.IPRA.Probability.Variance (sum_one)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `Λ(n)` read from the parameter `y = (D, z)`. -/
abbrev lB : PTm 2 := Syn.subst ![var 0, sndT (var 1)] lamW
/-- The constant `F`, read from `y = (D, (K, F))`. -/
abbrev fB : PTm 2 := sndT (sndT (var 1))

theorem lB_at (k D z : PTm n) : Γ ⊢[PRAAx] inst2 lB k (pairT D z) ≐ Lam wt k z := by
  rw [show inst2 lB k (pairT D z) = Lam wt k (sndT (pairT D z)) by simp [inst2]]
  exact congrAp2 _ (.eqRefl _) (congrPairT (.eqRefl _) (snd_pair _ _))

theorem fB_at (k D K F : PTm n) : Γ ⊢[PRAAx] inst2 fB k (pairT D (pairT K F)) ≐ F := by
  rw [show inst2 fB k (pairT D (pairT K F)) = sndT (sndT (pairT D (pairT K F))) by simp [inst2]]
  exact (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)

/-- `B⌊x/k⌋ ≤ xc ≤ B⌊x/k⌋ + B` for `B = kc`, `k ≥ 1`. -/
theorem floor_pair {k x c B : PTm n} (hk : Γ ⊢[PRAAx] k ≐ succ (pred k)) (hB : Γ ⊢[PRAAx] B ≐ k * c) :
    Γ ⊢[PRAAx] le (B * quo x k) (x * c) ⋏ le (x * c) (B * quo x k + B) := by
  have dm := div_mod_at (Γ := Γ) (x := x) hk
  have e1 := natEq (Prf.andE₁ dm)
  have hr := Prf.andE₂ dm
  have e2 := natEq hB
  refine .andI ?_ ?_
  · ipra_le 𝔞 (rem x k) * 𝔞 c with 𝔞 c * e1 - 𝔞 (quo x k) * e2
  · ipra_le 𝔞 c * sl hr + 𝔞 c with 𝔞 c * e1 - (𝔞 (quo x k) + 1) * e2

/-- `P!⌊x/k⌋Λ ≤ xΛ(P!/k) ≤ P!⌊x/k⌋Λ + P!Λ` for `1 ≤ k ≤ P`. -/
theorem lam_pt {k x P : PTm n} (c : PTm n) (hk : Γ ⊢[PRAAx] k ≐ succ (pred k)) (hkP : Γ ⊢[PRAAx] le k P) :
    Γ ⊢[PRAAx] le (fact P * (c * quo x k)) (x * (c * quo (fact P) k)) ⋏
      le (x * (c * quo (fact P) k)) (fact P * (c * quo x k) + fact P * c) := by
  have hf : Γ ⊢[PRAAx] fact P ≐ k * quo (fact P) k :=
    (fact_quo (le_congr hk (.eqRefl _) hkP)).eqTrans (congrMul hk.eqSymm (congrAp2 quoF (.eqRefl _) hk.eqSymm))
  have fp := floor_pair (x := x) hk hf
  have a := le_scale c (Prf.andE₁ fp); have b := le_scale c (Prf.andE₂ fp)
  exact .andI (by ipra_le sl a) (by ipra_le sl b)

theorem lq_at (k x D z : PTm n) :
    Γ ⊢[PRAAx] inst2 (gB lB) k (pairT x (pairT D z)) ≐ (sg k * Lam wt k z) * quo x k :=
  (gB_at _ _ _ _).eqTrans (congrMul (congrMul (.eqRefl _) (lB_at _ _ _)) (.eqRefl _))

alias le_of_lt_succ := Common.le_of_lt_succ

theorem lam_body_lo {k x P D z : PTm n} (hk : Γ ⊢[PRAAx] lt k (succ P)) :
    Γ ⊢[PRAAx] le (fact P * inst2 (gB lB) k (pairT x (pairT D z))) (x * inst2 (AB wt) k (pairT P z)) := by
  have eW := natEq (lq_at (Γ := Γ) k x D z)
  have eA := natEq (AB_at (Γ := Γ) wt k P z)
  refine .orE (zero_or_succ k) ?_ ?_
  · have s := natEq ((congrSg (Prf.hyp0 : ((k ≐ zero) :: Γ) ⊢[PRAAx] k ≐ zero)).eqTrans sg_zero)
    have eW' := natEq (lq_at (Γ := ((k ≐ zero) :: Γ)) k x D z)
    ipra_le 𝔞 x * 𝔞 (inst2 (AB wt) k (pairT P z)) with
      𝔞 (fact P) * eW' + 𝔞 (fact P) * 𝔞 (Lam wt k z) * 𝔞 (quo x k) * s
  · have s := natEq ((congrSg (Prf.hyp0 : ((k ≐ succ (pred k)) :: Γ) ⊢[PRAAx] k ≐ succ (pred k))).eqTrans (sg_succ (pred k)))
    have p := Prf.andE₁ (lam_pt (Lam wt k z) (x := x) (Prf.hyp0 : ((k ≐ succ (pred k)) :: Γ) ⊢[PRAAx] k ≐ succ (pred k)) (le_of_lt_succ hk).wk)
    have eW' := natEq (lq_at (Γ := ((k ≐ succ (pred k)) :: Γ)) k x D z)
    have eA' := natEq (AB_at (Γ := ((k ≐ succ (pred k)) :: Γ)) wt k P z)
    ipra_le sl p with 𝔞 x * eA' - 𝔞 (fact P) * eW' - 𝔞 (fact P) * 𝔞 (Lam wt k z) * 𝔞 (quo x k) * s

theorem lam_body_hi {k x P D z : PTm n} (hk : Γ ⊢[PRAAx] lt k (succ P)) :
    Γ ⊢[PRAAx] le (x * inst2 (AB wt) k (pairT P z))
      (fact P * inst2 (gB lB) k (pairT x (pairT D z)) + fact P * inst2 (LamB wt) k z) := by
  rw [inst2_LamB]
  refine .orE (zero_or_succ k) ?_ ?_
  · have l0 : ((k ≐ zero) :: Γ) ⊢[PRAAx] Lam wt k z ≐ zero := by
      have h := (congrInst2 (Γ := ((k ≐ zero) :: Γ)) (LamB wt) Prf.hyp0 (.eqRefl z)).eqTrans (WeightedBound.lamB0 z)
      rw [inst2_LamB] at h; exact h
    have l := natEq l0
    have eA' := natEq (AB_at (Γ := ((k ≐ zero) :: Γ)) wt k P z)
    ipra_le 𝔞 (fact P) * 𝔞 (inst2 (gB lB) k (pairT x (pairT D z))) with
      𝔞 (fact P) * l - 𝔞 x * eA' - 𝔞 x * 𝔞 (quo (fact P) k) * l
  · have s := natEq ((congrSg (Prf.hyp0 : ((k ≐ succ (pred k)) :: Γ) ⊢[PRAAx] k ≐ succ (pred k))).eqTrans (sg_succ (pred k)))
    have p := Prf.andE₂ (lam_pt (Lam wt k z) (x := x) (Prf.hyp0 : ((k ≐ succ (pred k)) :: Γ) ⊢[PRAAx] k ≐ succ (pred k)) (le_of_lt_succ hk).wk)
    have eW' := natEq (lq_at (Γ := ((k ≐ succ (pred k)) :: Γ)) k x D z)
    have eA' := natEq (AB_at (Γ := ((k ≐ succ (pred k)) :: Γ)) wt k P z)
    ipra_le sl p with 𝔞 x * eA' - 𝔞 (fact P) * eW' - 𝔞 (fact P) * 𝔞 (Lam wt k z) * 𝔞 (quo x k) * s

theorem hyp_succ {P : PTm n} :
    (lt (var 0) (Syn.shift (succ P)) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (succ (Syn.shift P)) := by
  have h0 : (lt (var 0) (Syn.shift (succ P)) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (Syn.shift (succ P)) := Prf.hyp0
  rw [shift_succ_x] at h0 ⊢; exact h0

/-- `P! Σ_{n≤P} Λ(n)⌊x/n⌋ ≤ x S_w(P)`. -/
theorem lam_sum_lo (x P D z : PTm n) :
    Γ ⊢[PRAAx] le (fact P * ap2 (sumF (gB lB)) (succ P) (pairT x (pairT D z))) (x * Sw wt P z) :=
  sum_le_lin1 (gB lB) (AB wt) (fact P) x (pairT x (pairT D z)) (pairT P z) (succ P) (.allI (.impI (by
    simp only [shift_pairT, shift_fact']
    exact lam_body_lo hyp_succ)))

/-- `x S_w(P) ≤ P! Σ_{n≤P} Λ(n)⌊x/n⌋ + P! ψ(P)`. -/
theorem lam_sum_hi (x P D z : PTm n) :
    Γ ⊢[PRAAx] le (x * Sw wt P z)
      (fact P * ap2 (sumF (gB lB)) (succ P) (pairT x (pairT D z)) + fact P * Psi wt P z) :=
  sum_le_lin (AB wt) (gB lB) (LamB wt) x (fact P) (fact P) (pairT P z) (pairT x (pairT D z)) z (succ P)
    (.allI (.impI (by
      simp only [shift_pairT, shift_fact']
      exact lam_body_hi hyp_succ)))

/-! ## The `F` part -/

theorem fq_at (k x D K L : PTm n) :
    Γ ⊢[PRAAx] inst2 (gB fB) k (pairT x (pairT D (pairT K (fact L)))) ≐ (sg k * fact L) * quo x k :=
  (gB_at _ _ _ _).eqTrans (congrMul (congrMul (.eqRefl _) (fB_at _ _ _ _)) (.eqRefl _))

/-- `Σ_{n≤P} F⌊x/n⌋ = Σ_{j<P} F⌊x/(j+1)⌋`. -/
theorem f_shift (x P D K L : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (gB fB)) (succ P) (pairT x (pairT D (pairT K (fact L)))) ≐
      ap2 (sumF (shiftBody (gB fB))) P (pairT x (pairT D (pairT K (fact L)))) := by
  refine (sum_shift _ _ _).eqTrans ((congrAdd ?_ (.eqRefl _)).eqTrans (zero_add _))
  exact (fq_at _ _ _ _ _).eqTrans (zero_mul_l (zero_mul_l sg_zero _) _)

theorem f_body {j x D K L P : PTm n} (hj : Γ ⊢[PRAAx] lt j P) (hPL : Γ ⊢[PRAAx] le P L) :
    Γ ⊢[PRAAx] le (one * inst2 (shiftBody (gB fB)) j (pairT x (pairT D (pairT K (fact L))))) (x * inst2 hB j (fact L)) ⋏
      le (x * inst2 hB j (fact L))
        (one * inst2 (shiftBody (gB fB)) j (pairT x (pairT D (pairT K (fact L)))) + fact L * inst2 (one : PTm 2) j zero) := by
  rw [inst2_shiftBody, inst2_h, show inst2 (one : PTm 2) j zero = one by simp [inst2]]
  have e := natEq (fq_at (Γ := Γ) (succ j) x D K L)
  have s := natEq (sg_succ (Γ := Γ) j)
  have hk : Γ ⊢[PRAAx] succ j ≐ succ (pred (succ j)) := congrSucc (pred_succ _).eqSymm
  have hf : Γ ⊢[PRAAx] fact L ≐ succ j * quo (fact L) (succ j) :=
    (fact_quo (le_trans hj hPL)).eqTrans (.eqRefl _)
  have fp := floor_pair (x := x) hk hf
  have a := Prf.andE₁ fp; have b := Prf.andE₂ fp
  refine .andI ?_ ?_
  · ipra_le sl a with e + 𝔞 (fact L) * 𝔞 (quo x (succ j)) * s
  · ipra_le sl b with e + 𝔞 (fact L) * 𝔞 (quo x (succ j)) * s

/-- `Σ_{n≤P} F⌊x/n⌋ ≤ x S(P, F) ≤ Σ_{n≤P} F⌊x/n⌋ + PF`, `P ≤ L`. -/
theorem f_sum {x P D K L : PTm n} (hPL : Γ ⊢[PRAAx] le P L) :
    Γ ⊢[PRAAx] le (ap2 (sumF (gB fB)) (succ P) (pairT x (pairT D (pairT K (fact L))))) (x * S P (fact L)) ⋏
      le (x * S P (fact L)) (ap2 (sumF (gB fB)) (succ P) (pairT x (pairT D (pairT K (fact L)))) + fact L * P) := by
  have hPL' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift P) (Syn.shift L) := by simpa [Fm.shift, Syn.shift] using hPL.shift
  have sh := natEq (f_shift (Γ := Γ) x P D K L)
  have lo := sum_le_lin1 (Γ := Γ) (shiftBody (gB fB)) hB one x (pairT x (pairT D (pairT K (fact L)))) (fact L) P
    (.allI (.impI (by
      simp only [shift_pairT, shift_fact', show Syn.shift (one : PTm n) = one by simp [Syn.shift]]
      exact Prf.andE₁ (f_body Prf.hyp0 hPL'.wk))))
  have hi := sum_le_lin (Γ := Γ) hB (shiftBody (gB fB)) (one : PTm 2) x one (fact L) (fact L)
    (pairT x (pairT D (pairT K (fact L)))) zero P
    (.allI (.impI (by
      simp only [shift_pairT, shift_fact', show Syn.shift (one : PTm n) = one by simp [Syn.shift],
        show Syn.shift (zero : PTm n) = zero by simp [Syn.shift]]
      exact Prf.andE₂ (f_body Prf.hyp0 hPL'.wk))))
  have o := natEq (sum_one (Γ := Γ) P zero)
  exact .andI (by ipra_le sl lo with sh) (by ipra_le sl hi with sh - 𝔞 (fact L) * o)

end LeanProofs.IPRA.AnalyticNumberTheory.BlockFloor
