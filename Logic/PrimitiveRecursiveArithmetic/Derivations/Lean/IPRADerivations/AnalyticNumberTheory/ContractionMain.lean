import IPRADerivations.AnalyticNumberTheory.HarmonicHalfSquare
import IPRADerivations.Core.LinearCombination

/-!
# The main term of the discrete contraction (`pnt_ipra_constructive_2026-11-14`, `con:one-step`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `contraction.tex`, proof of `con:one-step`:
"`∫_0^t (t − u)|r(u)| du ≤ a t²/2 + …`". In the discrete weighted inequality the bound `|R(y)| ≤ a F y` at
`y = ⌊x/n⌋` produces the main term `Σ_{n≤x} u_n F⌊x/n⌋`; here it is compared with `x u_x²/2`:

* `dl_ge`: `⌊F/m⌋ ≤ Δ_m` exactly, `F = L!`, `Km ≤ L` (`HarmonicLogSum.inc_lower`);
* `fq_le`: `F ⌊x/m⌋ ≤ x ⌊F/m⌋` exactly, since `m ∣ L!` for `m ≤ L`;
* `main_term`: `2 Σ_{2≤m≤M+1} u_m F⌊x/m⌋ ≤ x (u_{M+1}² + 2F²)` (`HarmonicHalfSquare.half_square`, `dd_le`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.ContractionMain

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (S_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertens (le_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogSquareSum (U)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogSum (inc_lower fact_quo)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicHalfSquare (dlB u2B udB ddB Dl dl_at u2_at half_square dd_le)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (pos_of_lt_zero)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorHarmonic (shift_fact')
open LeanProofs.IPRA.Probability.Lotus (cmB sum_const_mul)
open LeanProofs.IPRA.Probability.Independence (cm_pt)
open LeanProofs.IPRA.Analysis.Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `⌊F/(j+2)⌋ ≤ Δ_{j+2}`. -/
theorem dl_ge {j K L : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hL : Γ ⊢[PRAAx] le (K * succ (succ j)) L) :
    Γ ⊢[PRAAx] le (quo (fact L) (succ (succ j))) (Dl j K (fact L)) := by
  have il := inc_lower (N := succ j) (pos_of_lt_zero hK) hL
  have m : Γ ⊢[PRAAx] le (S (K * succ j) (fact L)) (S (K * succ (succ j)) (fact L)) :=
    S_mono (fact L) (le_of_eq_add (d := K) (by ipra_ring))
  have e := natEq (eq_add_of_le m)
  ipra_le sl il with e

/-- `F ⌊x/m⌋ ≤ x ⌊F/m⌋` for `1 ≤ m ≤ L`. -/
theorem fq_le {m x L : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hmL : Γ ⊢[PRAAx] le m L) :
    Γ ⊢[PRAAx] le (fact L * quo x m) (x * quo (fact L) m) := by
  have ef := natEq ((fact_quo (le_congr hm (.eqRefl _) hmL)).eqTrans
    (congrMul hm.eqSymm (congrAp2 quoF (.eqRefl _) hm.eqSymm)))
  have dm := div_mod_at (Γ := Γ) (x := x) hm
  have hdm : Γ ⊢[PRAAx] le (m * quo x m) x := le_of_eq_add (d := rem x m) (Prf.andE₁ dm)
  have q := le_scale (quo (fact L) m) hdm
  ipra_le sl q with 𝔞 (quo x m) * ef

/-- `u_{j+2} · F⌊x/(j+2)⌋` over `0 = j`, `1 = (x, (K, F))`. -/
def mtB : PTm 2 := Syn.subst ![var 0, sndT (var 1)] u2B * (sndT (sndT (var 1)) * quo (fstT (var 1)) (succ (succ (var 0))))

theorem inst2_mtB (j z : PTm n) :
    inst2 mtB j z = inst2 u2B j (sndT z) * (sndT (sndT z) * quo (fstT z) (succ (succ j))) := by
  have h : Syn.subst ![j, z] (Syn.subst ![var 0, sndT (var 1)] u2B) = inst2 u2B j (sndT z) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext i; fin_cases i <;> simp
  simp only [inst2, mtB, PTm.subst_mul, h]; simp

theorem mt_pt {j x K L : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hL : Γ ⊢[PRAAx] le (K * succ (succ j)) L) :
    Γ ⊢[PRAAx] le (inst2 mtB j (pairT x (pairT K (fact L)))) (inst2 (cmB udB) j (pairT x (pairT K (fact L)))) := by
  rw [inst2_mtB]
  have e1 : Γ ⊢[PRAAx] inst2 u2B j (sndT (pairT x (pairT K (fact L)))) ≐ U (succ (succ j)) K (fact L) :=
    (congrInst2 u2B (.eqRefl _) (snd_pair _ _)).eqTrans (u2_at _ _ _)
  have e2 : Γ ⊢[PRAAx] sndT (sndT (pairT x (pairT K (fact L)))) ≐ fact L :=
    (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)
  have e3 : Γ ⊢[PRAAx] quo (fstT (pairT x (pairT K (fact L)))) (succ (succ j)) ≐ quo x (succ (succ j)) :=
    congrAp2 quoF (fst_pair _ _) (.eqRefl _)
  have e4 : Γ ⊢[PRAAx] inst2 udB j (pairT K (fact L)) ≐ U (succ (succ j)) K (fact L) * Dl j K (fact L) := by
    rw [show inst2 udB j (pairT K (fact L)) = inst2 u2B j (pairT K (fact L)) * inst2 dlB j (pairT K (fact L)) by
      simp [inst2]]
    exact congrMul (u2_at _ _ _) (dl_at _ _ _)
  refine le_congr (congrMul e1 (congrMul e2 e3)).eqSymm ((cm_pt _ _ _ _).eqTrans (congrMul (.eqRefl _) e4)).eqSymm ?_
  have hsj : Γ ⊢[PRAAx] succ (succ j) ≐ succ (pred (succ (succ j))) := congrSucc (pred_succ _).eqSymm
  have hjL : Γ ⊢[PRAAx] le (succ (succ j)) L := by
    have h1 : Γ ⊢[PRAAx] le (succ (succ j)) (K * succ (succ j)) :=
      le_of_eq_add (d := pred K * succ (succ j)) (by
        ipra_lc (𝔞 j + 2) * natEq (pos_of_lt_zero hK))
    exact le_trans h1 hL
  have f := fq_le (x := x) hsj hjL
  have d := le_scale x (dl_ge hK hL)
  have p := le_scale (U (succ (succ j)) K (fact L)) (le_trans f d)
  ipra_le sl p

/-- `2 Σ_{2≤m≤M+1} u_m F⌊x/m⌋ ≤ x (u_{M+1}² + 2F²)` for `K ≥ 1`, `K(M+1) ≤ L`. -/
theorem main_term {M x K L : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hL : Γ ⊢[PRAAx] le (K * succ M) L) :
    Γ ⊢[PRAAx] le (two * ap2 (sumF mtB) M (pairT x (pairT K (fact L))))
      (x * (U (succ M) K (fact L) * U (succ M) K (fact L) + two * (fact L * fact L))) := by
  have hK' : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift K) := by simpa [Fm.shift, Syn.shift] using hK.shift
  have hL' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift K * succ (Syn.shift M)) (Syn.shift L) := by
    simpa [Fm.shift, Syn.shift] using hL.shift
  have p := sum_le_params (Γ := Γ) mtB (cmB udB) (pairT x (pairT K (fact L))) (pairT x (pairT K (fact L))) M
    (.allI (.impI (by
      simp only [shift_pairT, shift_fact']
      have hv : (lt (var 0) (Syn.shift M) :: Γ.map Fm.shift) ⊢[PRAAx] le (succ (succ (var 0))) (succ (Syn.shift M)) :=
        (succ_monus_succ _ _).eqTrans Prf.hyp0
      exact mt_pt hK'.wk (le_trans (le_scale _ hv) hL'.wk))))
  have c := natEq (sum_const_mul (Γ := Γ) udB M x (pairT K (fact L)))
  have h := natEq (half_square (Γ := Γ) M K (fact L))
  have d := dd_le (Γ := Γ) M (fact L) hK
  ipra_le 2 * sl p + 𝔞 x * sl d with 2 * c + 𝔞 x * h

end LeanProofs.IPRA.AnalyticNumberTheory.ContractionMain
