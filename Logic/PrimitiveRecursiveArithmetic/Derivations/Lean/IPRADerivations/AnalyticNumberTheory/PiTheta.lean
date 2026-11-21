import IPRADerivations.AnalyticNumberTheory.PsiModulus
import IPRADerivations.AnalyticNumberTheory.PrimePowerMangoldt
import IPRADerivations.AnalyticNumberTheory.SumPhi

/-!
# Primes against prime powers (`pnt_ipra_constructive_2026-11-14`, §"From the Chebyshev estimate to prime counting")

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `pnt_ipra.tex`, Lemma `lem:pi-conversion`: "it
uses only finite sums and the global bound `θ(u) ≤ ψ(u) ≤ 4u`." With the harmonic weight `u_d = S(Kd) − S(K)` at
mesh `K` over `F` (`HarmonicChebyshev.wt`, read at `z = (K, F)`):

* `Theta x z = Σ_{d ≤ x} [d prime] u_d` and `Pi x z = Σ_{d ≤ x} [d prime]`;
* `theta_le_psi`: `θ(x) ≤ ψ_w(x)` (a prime is its own base, `PrimePowerMangoldt.lam_pw'`);
* `theta_le_pi`: `θ(x) ≤ π(x) u_x` (`u` is monotone);
* `pi_upper`: `π(x) u_x ≤ θ(x) + (u_x − u_Y) π(x) + (Y + 1) u_x` for `Y ≤ x`, splitting the primes at `Y`
  (`Core/SumSplit.sum_split`): the summation by parts of the packet, reduced to one cut;
* `pi_cheb`: `π(x) u_Y ≤ θ(x) + (Y + 1) u_Y`, the Chebyshev bound `π(x) ≤ Y + 1 + θ(x)/u_Y`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.PiTheta

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (wt inst2_wt S_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertens (le_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogSquareSum (U)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockChain (u_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedMangoldt (lamB Lam)
open LeanProofs.IPRA.AnalyticNumberTheory.PrimePowerMangoldt (lam_pw')
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (isP isP_01 prime_of_isP)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (Psi LamB inst2_LamB)
open LeanProofs.IPRA.AnalyticNumberTheory.SumPhi (sum_ones)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBlock (sum_le_lin sum_le_lin1)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.Analysis.Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The sums -/

/-- `[d prime]`. -/
def piB : PTm 2 := isP (var 0)
/-- `[d prime] u_d`. -/
def thB : PTm 2 := isP (var 0) * wt

theorem inst2_piB (d z : PTm n) : inst2 piB d z = isP d := by simp [inst2, piB]
theorem inst2_thB (d z : PTm n) : inst2 thB d z = isP d * inst2 wt d z := by simp [inst2, thB]

/-- `π(x) = Σ_{d ≤ x} [d prime]`. -/
abbrev Pi (x z : PTm n) : PTm n := ap2 (sumF piB) (succ x) z
/-- `θ(x) = Σ_{d ≤ x} [d prime] u_d`. -/
abbrev Theta (x z : PTm n) : PTm n := ap2 (sumF thB) (succ x) z

theorem wt_at (d K F : PTm n) : Γ ⊢[PRAAx] inst2 wt d (pairT K F) ≐ U d K F := by
  rw [inst2_wt]
  exact congrMonus (congrAp2 (sumF hB) (congrMul (fst_pair _ _) (.eqRefl _)) (snd_pair _ _))
    (congrAp2 (sumF hB) (fst_pair _ _) (snd_pair _ _))

/-! ## Pointwise comparisons -/

theorem th_pt (d y : PTm n) : Γ ⊢[PRAAx] le (isP d * inst2 wt d y) (Lam wt d y) := by
  refine .orE (isP_01 d) ?_ ?_
  · have e := natEq (Prf.hyp0 : ((isP d ≐ zero) :: Γ) ⊢[PRAAx] isP d ≐ zero)
    ipra_le 𝔞 (Lam wt d y) with 𝔞 (inst2 wt d y) * e
  · have h1 : ((isP d ≐ one) :: Γ) ⊢[PRAAx] isP d ≐ one := Prf.hyp0
    have hp := prime_of_isP h1
    have e1 : ((isP d ≐ one) :: Γ) ⊢[PRAAx] pw d one ≐ d := pw_one d
    have L := lam_pw' wt hp (pos_of_one_le (le_refl one)) y
    have L' : ((isP d ≐ one) :: Γ) ⊢[PRAAx] Lam wt d y ≐ inst2 wt d y :=
      (congrAp2 (sumF (lamB wt)) (congrSucc e1.eqSymm) (congrPairT e1.eqSymm (.eqRefl y))).eqTrans L
    have e := natEq h1
    have l := natEq L'
    ipra_le 0 with l - 𝔞 (inst2 wt d y) * e

/-- `u_Y ≤ u_d` gives `[d prime] u_x ≤ [d prime] u_d + (u_x − u_Y)[d prime]`. -/
theorem tl_pt {d Y x K F : PTm n} (hYd : Γ ⊢[PRAAx] le Y d) (hYx : Γ ⊢[PRAAx] le Y x) :
    Γ ⊢[PRAAx] le (U x K F * isP d) (one * (isP d * U d K F) + monus (U x K F) (U Y K F) * isP d) := by
  have h1 := u_mono K F hYd
  have hux := u_mono K F hYx
  refine .orE (isP_01 d) ?_ ?_
  · have e := natEq (Prf.hyp0 : ((isP d ≐ zero) :: Γ) ⊢[PRAAx] isP d ≐ zero)
    ipra_le 0 with (𝔞 (U d K F) + 𝔞 (monus (U x K F) (U Y K F)) - 𝔞 (U x K F)) * e
  · have e := natEq (Prf.hyp0 : ((isP d ≐ one) :: Γ) ⊢[PRAAx] isP d ≐ one)
    have h1' := h1.wk (ψ := isP d ≐ one)
    have e1 := natEq (eq_add_of_le (hux.wk (ψ := isP d ≐ one)))
    ipra_le sl h1' with (𝔞 (U d K F) + 𝔞 (monus (U x K F) (U Y K F)) - 𝔞 (U x K F)) * e - e1

/-! ## Comparisons of the sums -/

theorem theta_le_psi (x y : PTm n) : Γ ⊢[PRAAx] le (Theta x y) (Psi wt x y) := by
  refine sum_le_params _ _ _ _ _ (.allI (.impI ?_))
  rw [inst2_thB, inst2_LamB]
  exact th_pt _ _

/-- `[d prime] u_d ≤ u_x [d prime]` for `d ≤ x`. -/
theorem tp_pt {d x K F : PTm n} (hdx : Γ ⊢[PRAAx] le d x) :
    Γ ⊢[PRAAx] le (one * (isP d * U d K F)) (U x K F * isP d) := by
  have h1 := u_mono K F hdx
  refine .orE (isP_01 d) ?_ ?_
  · have e := natEq (Prf.hyp0 : ((isP d ≐ zero) :: Γ) ⊢[PRAAx] isP d ≐ zero)
    ipra_le 0 with (𝔞 (U x K F) - 𝔞 (U d K F)) * e
  · have e := natEq (Prf.hyp0 : ((isP d ≐ one) :: Γ) ⊢[PRAAx] isP d ≐ one)
    have h1' := h1.wk (ψ := isP d ≐ one)
    ipra_le sl h1' with (𝔞 (U x K F) - 𝔞 (U d K F)) * e

/-- `u_Y [d prime] ≤ [d prime] u_d` for `Y ≤ d`. -/
theorem tc_pt {d Y K F : PTm n} (hYd : Γ ⊢[PRAAx] le Y d) :
    Γ ⊢[PRAAx] le (U Y K F * isP d) (one * (isP d * U d K F)) := by
  have h1 := u_mono K F hYd
  refine .orE (isP_01 d) ?_ ?_
  · have e := natEq (Prf.hyp0 : ((isP d ≐ zero) :: Γ) ⊢[PRAAx] isP d ≐ zero)
    ipra_le 0 with (𝔞 (U d K F) - 𝔞 (U Y K F)) * e
  · have e := natEq (Prf.hyp0 : ((isP d ≐ one) :: Γ) ⊢[PRAAx] isP d ≐ one)
    have h1' := h1.wk (ψ := isP d ≐ one)
    ipra_le sl h1' with (𝔞 (U d K F) - 𝔞 (U Y K F)) * e

/-- `θ(x) ≤ π(x) u_x`. -/
theorem theta_le_pi (x K F : PTm n) :
    Γ ⊢[PRAAx] le (Theta x (pairT K F)) (U x K F * Pi x (pairT K F)) := by
  have h := sum_le_lin1 (Γ := Γ) thB piB one (U x K F) (pairT K F) (pairT K F) (succ x) (.allI (.impI (by
    simp only [inst2_thB, inst2_piB, shift_pairT]
    rw [show Syn.shift (one : PTm n) = one by simp [Syn.shift],
      show Syn.shift (U x K F) = U (Syn.shift x) (Syn.shift K) (Syn.shift F) by simp [Syn.shift]]
    have hdx : (lt (var 0) (Syn.shift (succ x)) :: Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift x) := by
      have a0 : (lt (var 0) (Syn.shift (succ x)) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (Syn.shift (succ x)) := Prf.hyp0
      rw [show Syn.shift (succ x) = succ (Syn.shift x) by simp [Syn.shift]] at a0
      exact (succ_monus_succ _ _).eqSymm.eqTrans a0
    exact le_congr (congrMul (.eqRefl _) (congrMul (.eqRefl _) (wt_at _ _ _))).eqSymm (.eqRefl _) (tp_pt hdx))))
  ipra_le sl h

/-- The tail `Y < d ≤ x` of a prime sum, as a sum from `Y + 1`. -/
theorem split_at {g : PTm 2} {x Y : PTm n} (z : PTm n) (hYx : Γ ⊢[PRAAx] le Y x) :
    Γ ⊢[PRAAx] ap2 (sumF g) (succ x) z ≐ ap2 (sumF g) (succ Y) z + ap2 (sumF (offB g)) (monus x Y) (pairT (succ Y) z) := by
  have a := natEq (eq_add_of_le hYx)
  have ex : Γ ⊢[PRAAx] succ x ≐ succ Y + monus x Y := by apply deriveNat; ipra_simps; linear_combination a
  exact (congrAp2 (sumF g) ex (.eqRefl _)).eqTrans (sum_split g (succ Y) (monus x Y) z)

/-- `π(Y) ≤ Y + 1`. -/
theorem pi_le (Y z : PTm n) : Γ ⊢[PRAAx] le (Pi Y z) (succ Y) := by
  refine le_congr (.eqRefl _) (sum_ones (succ Y) z) (sum_le_params _ _ _ _ _ (.allI (.impI ?_)))
  rw [inst2_piB, show inst2 (one : PTm 2) (var 0) (Syn.shift z) = one by simp [inst2]]
  refine .orE (isP_01 (var 0)) ?_ ?_
  · exact le_congr (Prf.hyp0 : ((isP (var 0) ≐ zero) :: _) ⊢[PRAAx] isP (var 0) ≐ zero).eqSymm (.eqRefl _) (zero_le _)
  · exact le_congr (Prf.hyp0 : ((isP (var 0) ≐ one) :: _) ⊢[PRAAx] isP (var 0) ≐ one).eqSymm (.eqRefl _) (le_refl _)

section Tails

variable {x Y K F : PTm n}

/-- The tail point `d = Y + 1 + i`, read through the pair parameter. -/
theorem tail_pt (i : PTm n) :
    Γ ⊢[PRAAx] isP (fstT (pairT (succ Y) (pairT K F)) + i) ≐ isP (succ Y + i) ⋏
      inst2 wt (fstT (pairT (succ Y) (pairT K F)) + i) (sndT (pairT (succ Y) (pairT K F))) ≐ U (succ Y + i) K F := by
  have ed : Γ ⊢[PRAAx] fstT (pairT (succ Y) (pairT K F)) + i ≐ succ Y + i := congrAdd (fst_pair _ _) (.eqRefl _)
  refine .andI ?_ ((congrInst2 wt ed (snd_pair _ _)).eqTrans (wt_at _ _ _))
  have c := congrInst2 piB ed (.eqRefl (zero : PTm n))
  rw [inst2_piB, inst2_piB] at c
  exact c

/-- `π(x) u_x ≤ θ(x) + (u_x − u_Y) π(x) + (Y + 1) u_x` for `Y ≤ x`. -/
theorem pi_upper (hYx : Γ ⊢[PRAAx] le Y x) :
    Γ ⊢[PRAAx] le (U x K F * Pi x (pairT K F))
      (Theta x (pairT K F) + monus (U x K F) (U Y K F) * Pi x (pairT K F) + succ Y * U x K F) := by
  have hYx' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift Y) (Syn.shift x) := by simpa [Fm.shift, Syn.shift] using hYx.shift
  have ep := natEq (split_at (g := piB) (pairT K F) hYx)
  have et := natEq (split_at (g := thB) (pairT K F) hYx)
  have hPY := pi_le (Γ := Γ) Y (pairT K F)
  have tl := sum_le_lin (Γ := Γ) (offB piB) (offB thB) (offB piB) (U x K F) one (monus (U x K F) (U Y K F))
    (pairT (succ Y) (pairT K F)) (pairT (succ Y) (pairT K F)) (pairT (succ Y) (pairT K F)) (monus x Y)
    (.allI (.impI (by
      simp only [inst2_offB, inst2_piB, inst2_thB, shift_pairT]
      rw [show Syn.shift (one : PTm n) = one by simp [Syn.shift],
        show Syn.shift (U x K F) = U (Syn.shift x) (Syn.shift K) (Syn.shift F) by simp [Syn.shift],
        show Syn.shift (monus (U x K F) (U Y K F)) =
          monus (U (Syn.shift x) (Syn.shift K) (Syn.shift F)) (U (Syn.shift Y) (Syn.shift K) (Syn.shift F)) by
          simp [Syn.shift],
        show Syn.shift (succ Y) = succ (Syn.shift Y) by simp [Syn.shift]]
      have tp := tail_pt (Γ := lt (var 0) (Syn.shift (monus x Y)) :: Γ.map Fm.shift) (Y := Syn.shift Y)
        (K := Syn.shift K) (F := Syn.shift F) (var 0)
      have b := tl_pt (Γ := lt (var 0) (Syn.shift (monus x Y)) :: Γ.map Fm.shift) (K := Syn.shift K) (F := Syn.shift F)
        (d := succ (Syn.shift Y) + var 0) (by ipra_le 𝔞 (var 0) + 1) hYx'.wk
      exact le_congr (congrMul (.eqRefl _) (Prf.andE₁ tp)).eqSymm
        (congrAdd (congrMul (.eqRefl _) (congrMul (Prf.andE₁ tp) (Prf.andE₂ tp))) (congrMul (.eqRefl _) (Prf.andE₁ tp))).eqSymm b)))
  ipra_le sl tl + 𝔞 (U x K F) * sl hPY + 𝔞 (Theta Y (pairT K F)) +
      𝔞 (monus (U x K F) (U Y K F)) * 𝔞 (Pi Y (pairT K F)) with
    et + (𝔞 (monus (U x K F) (U Y K F)) - 𝔞 (U x K F)) * ep

/-- `π(x) u_Y ≤ θ(x) + (Y + 1) u_Y` for `Y ≤ x`. -/
theorem pi_cheb (hYx : Γ ⊢[PRAAx] le Y x) :
    Γ ⊢[PRAAx] le (U Y K F * Pi x (pairT K F)) (Theta x (pairT K F) + succ Y * U Y K F) := by
  have ep := natEq (split_at (g := piB) (pairT K F) hYx)
  have et := natEq (split_at (g := thB) (pairT K F) hYx)
  have hPY := pi_le (Γ := Γ) Y (pairT K F)
  have tl := sum_le_lin1 (Γ := Γ) (offB piB) (offB thB) (U Y K F) one
    (pairT (succ Y) (pairT K F)) (pairT (succ Y) (pairT K F)) (monus x Y)
    (.allI (.impI (by
      simp only [inst2_offB, inst2_piB, inst2_thB, shift_pairT]
      rw [show Syn.shift (one : PTm n) = one by simp [Syn.shift],
        show Syn.shift (U Y K F) = U (Syn.shift Y) (Syn.shift K) (Syn.shift F) by simp [Syn.shift],
        show Syn.shift (succ Y) = succ (Syn.shift Y) by simp [Syn.shift]]
      have tp := tail_pt (Γ := lt (var 0) (Syn.shift (monus x Y)) :: Γ.map Fm.shift) (Y := Syn.shift Y)
        (K := Syn.shift K) (F := Syn.shift F) (var 0)
      have b := tc_pt (Γ := lt (var 0) (Syn.shift (monus x Y)) :: Γ.map Fm.shift) (K := Syn.shift K) (F := Syn.shift F)
        (d := succ (Syn.shift Y) + var 0) (Y := Syn.shift Y) (by ipra_le 𝔞 (var 0) + 1)
      exact le_congr (congrMul (.eqRefl _) (Prf.andE₁ tp)).eqSymm
        (congrMul (.eqRefl _) (congrMul (Prf.andE₁ tp) (Prf.andE₂ tp))).eqSymm b)))
  ipra_le sl tl + 𝔞 (U Y K F) * sl hPY + 𝔞 (Theta Y (pairT K F)) with et - 𝔞 (U Y K F) * ep

end Tails

end LeanProofs.IPRA.AnalyticNumberTheory.PiTheta
