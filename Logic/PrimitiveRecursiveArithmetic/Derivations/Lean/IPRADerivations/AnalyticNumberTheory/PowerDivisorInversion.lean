import IPRADerivations.AnalyticNumberTheory.PowerAbstractInversion
import IPRADerivations.AnalyticNumberTheory.MobiusBounds
import IPRADerivations.AnalyticNumberTheory.EulerProduct
import IPRADerivations.Core.Header

/-!
# Möbius inversion along perfect powers (`riemann_ipra_prime_criteria_2026-11-20`, `thm:powerdivisor`)

Packet: `analytic-number-theory/riemann_ipra_prime_criteria_2026-11-20`, `new-growth.tex`, proof of Theorem
`thm:powerdivisor`: "`A(N) = Σ_{d=1}^N μ(d) B_h(⌊N/d^h⌋)`. For the second identity, substitute the first into the
right side, use `⌊⌊N/d^h⌋/e^h⌋ = ⌊N/(de)^h⌋`, and group pairs by `s = de`. The coefficient of `A(⌊N/s^h⌋)` is
`Σ_{d∣s} μ(d) = [s = 1]` … Terms with `s^h > N` vanish. This proves finite inversion."

With `μ = μ⁺ − μ⁻` (`AnalyticNumberTheory/Mobius`, prime bound `N + 1`) and `G(m) = A(⌊N/m^h⌋)`:

* for a weight body `w(d)`, `R_w(N) = Σ_{d<N+1} sg(d) w(d) B_h(⌊N/d^h⌋)` (`RS`);
* `inversion`: `R_{μ⁺}(N) = R_{μ⁻}(N) + A(N)`, i.e. `A(N) = Σ_{d≤N} μ(d) B_h(⌊N/d^h⌋)`. It is the abstract inversion
  `PowerAbstractInversion.inversion_g` for the row values `B_h(⌊N/d^h⌋)` (`bR`): the row identity is
  `PowerDivisorRow.row_identity`, and the delta term is `G(1) = A(N)`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.PowerDivisorInversion

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PowerDivisorPrefix
open LeanProofs.IPRA.AnalyticNumberTheory.PowerDivisorRow
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds (GP GN G_at cancel_gen congrMu)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (muP muN congrEqb' congrSg)
open LeanProofs.IPRA.AnalyticNumberTheory.EulerProduct (eqb_comm')
open LeanProofs.IPRA.AnalyticNumberTheory.LogRefinement (quo_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.Order (pw_one_base)
open LeanProofs.IPRA.Probability.Lotus (cmB inst2_cmB sum_const_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda (sum_add2)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

variable (a w : PTm 2)

/-! ## The weighted sums -/

/-- The row value `B_h(⌊N/d^h⌋)` over `0 = d`, `1 = ⟨⟨N, h⟩, y⟩`. -/
def bR : PTm 2 :=
  ap2 (sumF (bpB a)) (quo (fstT (fstT (var 1))) (pw (var 0) (sndT (fstT (var 1))))) (pairT (sndT (fstT (var 1))) (sndT (var 1)))

/-- `sg(d) w(d) B_h(⌊N/d^h⌋)` over `0 = d`, `1 = ⟨⟨N, h⟩, y⟩`. -/
def rB : PTm 2 := sg (var 0) * w * bR a

/-- `R_w(N) = Σ_{d<N+1} sg(d) w(d) B_h(⌊N/d^h⌋)`. -/
abbrev RS (N h y : PTm n) : PTm n := ap2 (sumF (rB a w)) (succ N) (Zp N h y)

theorem inst2_bR (d P : PTm n) : inst2 (bR a) d P =
    ap2 (sumF (bpB a)) (quo (fstT (fstT P)) (pw d (sndT (fstT P)))) (pairT (sndT (fstT P)) (sndT P)) := by
  simp [inst2, bR]

theorem inst2_rB (d P : PTm n) : inst2 (rB a w) d P = sg d * inst2 w d P *
    ap2 (sumF (bpB a)) (quo (fstT (fstT P)) (pw d (sndT (fstT P)))) (pairT (sndT (fstT P)) (sndT P)) := by
  simp [inst2, rB, bR]

/-- The row value `B_h(⌊N/d^h⌋)` read at the packed parameter. -/
theorem row_arg (d N h y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (bpB a)) (quo (fstT (fstT (Zp N h y))) (pw d (sndT (fstT (Zp N h y)))))
        (pairT (sndT (fstT (Zp N h y))) (sndT (Zp N h y))) ≐ Bpre a (quo N (pw d h)) h y := by
  have e1 : Γ ⊢[PRAAx] fstT (fstT (pairT (pairT N h) y)) ≐ N := (congrFst (fst_pair _ _)).eqTrans (fst_pair _ _)
  have e2 : Γ ⊢[PRAAx] sndT (fstT (pairT (pairT N h) y)) ≐ h := (congrSnd (fst_pair _ _)).eqTrans (snd_pair _ _)
  exact congrAp2 _ (congrAp2 quoF e1 (congrAp2 powF e2 (.eqRefl _))) (congrPairT e2 (snd_pair _ _))

theorem bR_at (d N h y : PTm n) : Γ ⊢[PRAAx] inst2 (bR a) d (Zp N h y) ≐ Bpre a (quo N (pw d h)) h y := by
  rw [inst2_bR]
  exact row_arg a d N h y

theorem rB_at (d N h y : PTm n) :
    Γ ⊢[PRAAx] inst2 (rB a w) d (Zp N h y) ≐ sg d * inst2 w d (Zp N h y) * Bpre a (quo N (pw d h)) h y := by
  rw [inst2_rB]
  exact congrMul (.eqRefl _) (row_arg a d N h y)

/-! ## The inversion -/

/-- `thm:powerdivisor`, finite inversion: `Σ_{d≤N} μ⁺(d) B_h(⌊N/d^h⌋) = Σ_{d≤N} μ⁻(d) B_h(⌊N/d^h⌋) + A(N)`,
i.e. `A(N) = Σ_{d=1}^N μ(d) B_h(⌊N/d^h⌋)`, for every coefficient body `a` and `h ≥ 1`. -/
theorem inversion {h : PTm n} (hh : Γ ⊢[PRAAx] le one h) (N y : PTm n) :
    Γ ⊢[PRAAx] RS a wP N h y ≐ RS a wN N h y + Apre a N y := by
  have hh' : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift h) := by simpa [Fm.shift, Syn.shift] using hh.shift
  have h1 : Γ ⊢[PRAAx] (one : PTm n) ≐ succ (pred one) := pos_of_one_le (le_refl _)
  refine PowerAbstractInversion.inversion_g (GB a) (bR a) (N := N) (h := h) (y := y) (T := Apre a N y)
    (fun Δ d s hd => (bR_at a d _ _ _).eqTrans (row_identity a hd (hh'.weaken s) _ _)) ?_ ?_
  · exact (GB_at a _ _ _ _).eqTrans (congrAp2 _
      ((congrAp2 quoF (.eqRefl _) (pw_one_base h)).eqTrans (quo_mul h1 (one_mul N).eqSymm)) (.eqRefl _))
  · exact (congrAp2 _ ((monus_zero N).eqSymm.eqTrans Prf.hyp0) (.eqRefl _)).eqTrans (sum_zero _ _)

end LeanProofs.IPRA.AnalyticNumberTheory.PowerDivisorInversion
