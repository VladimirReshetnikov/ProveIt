import IPRADerivations.DiophantineNumberTheory.DirichletReal

/-!
# Unbounded denominators by padding

Packet: `diophantine-number-theory/dirichlet_kronecker_ipra`, Theorem `thm:padding` ("Unbounded integer
denominators without irrationality"): for every named real `α` and `B ≥ 0` there are `B < q ≤ (B+1)³` and `p`
with `|α − p/q| < 1/q²`. "Set `N = (B+1)³` and obtain `(p₀, q₀)` from `thm:dir-real`. Set `v = ⌊B/q₀⌋ + 1`,
`q = v q₀`, `p = v p₀`."

With `q₀ = q₀' + 1 ≤ N` and `v = ⌊B/q₀⌋ + 1`:

* `q_gt`: `B < v q₀`;
* `v_sq_le`: `v² q₀ ≤ (B+1)³` (if `q₀ > B` then `v = 1`; otherwise `v ≤ B + 1` and `v q₀ ≤ B + q₀ ≤ 2B`);
* `q_le`: `v q₀ ≤ (B+1)³`;
* `padding_bound`: from the output of `DirichletReal.real_step` at `N = (B+1)³`
  (`AbsLe (q₀A − p₀D) b`, `2N(N+1) b ≤ (2N+1) D`) and `D ≥ 1`: `AbsLe (qA − pD) (v b)` and `q (v b) < D`,
  i.e. `q |q a − p| < 1`, which is `|a − p/q| < 1/q²` at every precision of the name.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.DirichletPadding

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.PolynomialRemainder (AbsLe abs_mul abs_congr)
open LeanProofs.IPRA.DiophantineNumberTheory.DirichletReal (abs_nat)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The padding factor `v = ⌊B/q₀⌋ + 1`. -/
abbrev vF (B q₀' : PTm k) : PTm k := succ (quo B (succ q₀'))

/-- `(B+1)³`. -/
abbrev cube (B : PTm k) : PTm k := succ B * succ B * succ B

theorem q_gt (B q₀' : PTm k) : Γ ⊢[PRAAx] lt B (vF B q₀' * succ q₀') := by
  have d := div_mod (Γ := Γ) B q₀'
  have eB := natEq (Prf.andE₁ d)
  have hR : Γ ⊢[PRAAx] le (succ (rem B (succ q₀'))) (succ q₀') := Prf.andE₂ d
  show Γ ⊢[PRAAx] le (succ B) (vF B q₀' * succ q₀')
  ipra_le sl hR using linear_combination -eB

theorem v_sq_le {B q₀' : PTm k} (hN : Γ ⊢[PRAAx] le (succ q₀') (cube B)) :
    Γ ⊢[PRAAx] le (vF B q₀' * vF B q₀' * succ q₀') (cube B) := by
  have d := div_mod (Γ := Γ) B q₀'
  refine .orE (lt_or_le B (succ q₀')) ?_ ?_
  · have hlt : (lt B (succ q₀') :: Γ) ⊢[PRAAx] lt B (succ q₀') := Prf.hyp0
    have u := div_mod_unique (Γ := lt B (succ q₀') :: Γ) (z := B) (q := zero) (r := B) (K' := q₀')
      (by ipra_ring) hlt
    have eQ := natEq (Prf.andE₁ u)
    have hN' : (lt B (succ q₀') :: Γ) ⊢[PRAAx] le (succ q₀') (cube B) := hN.wk
    ipra_le sl hN' using
      linear_combination (-(𝔞 q₀' + 1) * (𝔞 (quo B (succ q₀')) + 2)) * eQ
  · have hle : (le (succ q₀') B :: Γ) ⊢[PRAAx] le (succ q₀') B := Prf.hyp0
    have eB := natEq ((Prf.andE₁ d).wk (ψ := le (succ q₀') B))
    have h1 : (le (succ q₀') B :: Γ) ⊢[PRAAx] le (vF B q₀') (succ B) := by
      ipra_le 𝔞 (rem B (succ q₀')) + 𝔞 (quo B (succ q₀')) * 𝔞 q₀' using linear_combination eB
    have h2 : (le (succ q₀') B :: Γ) ⊢[PRAAx] le (vF B q₀' * succ q₀') (B + succ q₀') := by
      ipra_le 𝔞 (rem B (succ q₀')) using linear_combination eB
    have c := le_mul_mono h1 h2
    ipra_le sl c + (𝔞 B + 1) * (sl hle + 𝔞 B * 𝔞 B + 1)

theorem q_le {B q₀' : PTm k} (hN : Γ ⊢[PRAAx] le (succ q₀') (cube B)) :
    Γ ⊢[PRAAx] le (vF B q₀' * succ q₀') (cube B) := by
  have h := v_sq_le hN
  ipra_le sl h + 𝔞 (quo B (succ q₀')) * (𝔞 (quo B (succ q₀')) + 1) * (𝔞 q₀' + 1)

/-- `thm:padding`, the transfer: with `q = v q₀`, `p = v p₀`, `AbsLe (qA − pD) (v b)` and `q (v b) < D`. -/
theorem padding_bound {B q₀' b D : PTm k} {A p₀ : ZT k} (hN : Γ ⊢[PRAAx] le (succ q₀') (cube B))
    (hr : Γ ⊢[PRAAx] AbsLe (ZT.ofNat (succ q₀') * A + -(p₀ * ZT.ofNat D)) b)
    (hb : Γ ⊢[PRAAx] le (two * cube B * succ (cube B) * b) ((two * cube B + one) * D))
    (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] AbsLe (ZT.ofNat (vF B q₀' * succ q₀') * A + -((ZT.ofNat (vF B q₀') * p₀) * ZT.ofNat D))
        (vF B q₀' * b) ⋏
      lt (vF B q₀' * succ q₀' * (vF B q₀' * b)) D := by
  refine .andI ?_ ?_
  · refine abs_congr (ZT.derive ?_) (abs_mul (abs_nat (vF B q₀')) hr)
    simp only [ZT.toZ_add, ZT.toZ_neg, ZT.toZ_mul, ZT.toZ_ofNat, Q.mk_mul, map_mul]
    ring
  · have hv := v_sq_le hN
    refine .orE (lt_or_le (vF B q₀' * succ q₀' * (vF B q₀' * b)) D) Prf.hyp0 ?_
    have hge : (le D (vF B q₀' * succ q₀' * (vF B q₀' * b)) :: Γ) ⊢[PRAAx]
        le D (vF B q₀' * succ q₀' * (vF B q₀' * b)) := Prf.hyp0
    have hb' := hb.wk (ψ := le D (vF B q₀' * succ q₀' * (vF B q₀' * b)))
    have hv' := hv.wk (ψ := le D (vF B q₀' * succ q₀' * (vF B q₀' * b)))
    have hD' := hD.wk (ψ := le D (vF B q₀' * succ q₀' * (vF B q₀' * b)))
    have c1 := le_mul_mono hv' (le_refl (two * cube B * succ (cube B) * b))
    have c : (le D (vF B q₀' * succ q₀' * (vF B q₀' * b)) :: Γ) ⊢[PRAAx] le (succ zero) zero := by
      ipra_le 2 * ((𝔞 B + 1) * (𝔞 B + 1) * (𝔞 B + 1)) * ((𝔞 B + 1) * (𝔞 B + 1) * (𝔞 B + 1) + 1) * sl hge +
        sl c1 + (𝔞 B + 1) * (𝔞 B + 1) * (𝔞 B + 1) * sl hb' + (𝔞 B + 1) * (𝔞 B + 1) * (𝔞 B + 1) * sl hD' +
        (𝔞 B * 𝔞 B * 𝔞 B + 3 * 𝔞 B * 𝔞 B + 3 * 𝔞 B)
    exact not_succ_le_self zero _ c

end LeanProofs.IPRA.DiophantineNumberTheory.DirichletPadding
