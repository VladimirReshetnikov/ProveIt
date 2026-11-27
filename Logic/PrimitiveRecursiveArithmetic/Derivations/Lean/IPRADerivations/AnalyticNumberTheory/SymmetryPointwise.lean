import IPRADerivations.AnalyticNumberTheory.SymmetryInstances
import IPRADerivations.AnalyticNumberTheory.WeightBridge

/-!
# The comparison at one inner endpoint (`pnt_ipra_constructive_2026-11-14`, `sb:symmetry`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `selberg.tex`, proof of Lemma `sb:symmetry`:
"For each `d ≤ x`, apply (`sb:comparison-error`) at `y = x/d`". Everything is scaled by `F = L!`; the outer
endpoint `x` fixes the finite constant `C = F c` (`TauLogAbel.CT K x F`). For one inner endpoint `m = k + 1 ≤ x`
this module compares the square sum of the additive logarithm `B(m) = Σ_{j≤m} L_w(j)²` with the summed comparison
function written through the three inversion bodies of `SymmetryInstances`,

  `Φ(m) = F Σ_{j≤m} τ(j) L_w(j) + 4C² m`,  `Ψ(m) = 2CF D(m)`,

and proves the two-sided bound (`point_upper`, `point_lower`)

  `Φ(m) ≤ B(m) + Ψ(m) + E(m)`,  `B(m) + Ψ(m) ≤ Φ(m) + E(m)`,  `E(m) = 146 F² (⌊m^{1/4}⌋ + 1)³ + 2F²`,

under `(x + 1)⁴ ≤ K` and `K (x + 1)⁴ ≤ L`. It chains the Abel identity (`TauAbelIdentity.abel_tau`), the two
halves of the comparison error (`SelbergComparison`), their fourth-root envelope (`ComparisonEnvelope`), and the
two logarithm bridges: `WeightBridge` for the squares, and `tw_le_tu`/`tu_le_tw` here for `Σ τ L_w` against
`Σ τ u` (`L_w(j) ≤ u_j ≤ L_w(j) + j ⌊F/K⌋`). The choice `K ≥ (x+1)⁴` makes every `⌊F/K⌋` error at most `F`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.SymmetryPointwise

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (S_mono wt)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogSquareSum (U Qs)
open LeanProofs.IPRA.AnalyticNumberTheory.TauLogAbel (As CT)
open LeanProofs.IPRA.AnalyticNumberTheory.TauAbelIdentity (tuB tuB_at abel_tau)
open LeanProofs.IPRA.AnalyticNumberTheory.SelbergComparison (c16 c19 c22 comparison_upper comparison_lower)
open LeanProofs.IPRA.AnalyticNumberTheory.ComparisonEnvelope (le_mul2 lam_succ env_upper env_lower)
open LeanProofs.IPRA.AnalyticNumberTheory.FourthRootSum (qr Q4 isqrt_le_self)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightBridge (lw_le_u u_le_lw bridge_lo bridge_hi sum_le_add_const)
open LeanProofs.IPRA.AnalyticNumberTheory.SymmetrySum (bL)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvSummatory (bS inst2_bS Bs)
open LeanProofs.IPRA.AnalyticNumberTheory.SymmetryInstances (bs_shift conv_zero twB inst2_twB)
open LeanProofs.IPRA.AnalyticNumberTheory.DirichletLeibniz (cvB conv inst2_cvB)
open LeanProofs.IPRA.AnalyticNumberTheory.EulerDomination (sg_le_one)
open LeanProofs.IPRA.Analysis.Products (fact)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Elementary bounds -/

/-- `⌊x/q⌋ q ≤ x`. -/
theorem quo_mul_le {x q : PTm n} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q)) : Γ ⊢[PRAAx] le (quo x q * q) x :=
  Division.quo_mul_le hq

/-- `τ(N) ≤ N + 1`. -/
theorem tau_le (N y : PTm n) : Γ ⊢[PRAAx] le (conv one one N y) (succ N) := by
  have s := sum_le_const (Γ := Γ) (cvB one one) (N := succ N) (L := one) (x := pairT N y) (.allI (.impI (by
    rw [inst2_cvB, one_inst, one_inst, show Syn.shift (one : PTm n) = one by simp [Syn.shift]]
    have p := le_mul2 (sg_le_one (Γ := (lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift)) (var 0))
      (eqb_le_one (rem (fstT (Syn.shift (pairT N y))) (var 0)) zero)
    ipra_le sl p)))
  ipra_le sl s

/-- `x ≤ (x + 1)⁴`. -/
theorem le_Q4 (x : PTm n) : Γ ⊢[PRAAx] le x (Q4 x) := by
  ipra_le 𝔞 x * 𝔞 x * 𝔞 x * 𝔞 x + 4 * (𝔞 x * 𝔞 x * 𝔞 x) + 6 * (𝔞 x * 𝔞 x) + 3 * 𝔞 x + 1

/-- `(x + 1)³ ≤ (x + 1)⁴`. -/
theorem cube_le_Q4 (x : PTm n) : Γ ⊢[PRAAx] le (succ x * (succ x * succ x)) (Q4 x) := by
  ipra_le 𝔞 x * 𝔞 x * 𝔞 x * 𝔞 x + 3 * (𝔞 x * 𝔞 x * 𝔞 x) + 3 * (𝔞 x * 𝔞 x) + 𝔞 x

alias le_succ' := Common.succ_le_succ

theorem Q4_mono {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx] le (Q4 a) (Q4 b) :=
  have s := le_succ' h
  have p := le_mul2 s s
  le_mul2 p p

/-- `u_{k+1} ≤ k F`. -/
theorem u_le_kF {K : PTm n} (k F : PTm n) (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx] le (U (succ k) K F) (k * F) := by
  have l := lam_succ (Γ := Γ) k F (pos_of_lt_zero hK)
  have m1 : Γ ⊢[PRAAx] le (S K F) (S (K * succ k) F) :=
    S_mono F (le_of_eq_add (d := K * k) (by ipra_ring))
  have Eu := natEq (eq_add_of_le m1)
  ipra_le sl l with Eu

/-! ## `Σ τ L_w` against `Σ τ u` -/

/-- `Σ_{j≤m} τ(j) L_w(j) ≤ Σ_{j≤m} τ(j) u_j` for `K ≥ 1`, `Km ≤ L`. -/
theorem tw_le_tu {m K L : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hmL : Γ ⊢[PRAAx] le (K * m) L) :
    Γ ⊢[PRAAx] le (ap2 (sumF twB) m (pairT K (fact L))) (ap2 (sumF tuB) (succ m) (pairT K (fact L))) := by
  have hK' : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift K) := by simpa [Fm.shift, Syn.shift] using hK.shift
  have hmL' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift K * Syn.shift m) (Syn.shift L) := by
    simpa [Fm.shift, Syn.shift] using hmL.shift
  have s := sum_le_params (Γ := Γ) twB (bS tuB) (pairT K (fact L)) (pairT K (fact L)) m (.allI (.impI (by
    rw [shift_pairT, shift_fact', inst2_twB, inst2_bS]
    exact le_congr (.eqRefl _) (tuB_at _ _ _).eqSymm (le_scale _ (lw_le_u hK'.wk
      (le_trans (le_scale _ (Prf.hyp0 : (lt (var 0) (Syn.shift m) :: Γ.map Fm.shift) ⊢[PRAAx] _)) hmL'.wk))))))
  have b := natEq (bs_shift (Γ := Γ) tuB m (pairT K (fact L)))
  have t0 := natEq ((tuB_at (Γ := Γ) zero K (fact L)).eqTrans (zero_mul_l (conv_zero one one _) _))
  ipra_le sl s with b + t0

/-- `Σ_{j≤m} τ(j) u_j ≤ Σ_{j≤m} τ(j) L_w(j) + m (m + 1) m ⌊F/K⌋` for `K ≥ 1`, `Km ≤ L`. -/
theorem tu_le_tw {m K L : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hmL : Γ ⊢[PRAAx] le (K * m) L) :
    Γ ⊢[PRAAx] le (ap2 (sumF tuB) (succ m) (pairT K (fact L)))
      (ap2 (sumF twB) m (pairT K (fact L)) + m * (succ m * (m * quo (fact L) K))) := by
  have hK' : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift K) := by simpa [Fm.shift, Syn.shift] using hK.shift
  have hmL' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift K * Syn.shift m) (Syn.shift L) := by
    simpa [Fm.shift, Syn.shift] using hmL.shift
  have s := sum_le_add_const (Γ := Γ) (bS tuB) twB (x := pairT K (fact L)) (y := pairT K (fact L))
    (c := succ m * (m * quo (fact L) K)) (N := m) (.allI (.impI (by
      rw [shift_pairT, shift_fact', inst2_twB, inst2_bS,
        show Syn.shift (succ m * (m * quo (fact L) K)) =
          succ (Syn.shift m) * (Syn.shift m * quo (fact (Syn.shift L)) (Syn.shift K)) by simp [Syn.shift]]
      let C := (lt (var 0) (Syn.shift m) :: Γ.map Fm.shift)
      have hv : C ⊢[PRAAx] le (succ (var 0)) (Syn.shift m) := Prf.hyp0
      have ul := u_le_lw hK'.wk (le_trans (le_scale _ hv) hmL'.wk)
      have tl := le_trans (tau_le (Γ := C) (succ (var 0)) (pairT (Syn.shift K) (fact (Syn.shift L)))) (le_succ' hv)
      have p1 := le_scale (conv one one (succ (var 0)) (pairT (Syn.shift K) (fact (Syn.shift L)))) ul
      have p2 := le_mul2 tl (mul_le_mul_right (quo (fact (Syn.shift L)) (Syn.shift K)) hv)
      refine le_congr (tuB_at _ _ _).eqSymm (.eqRefl _) ?_
      ipra_le sl p1 + sl p2)))
  have b := natEq (bs_shift (Γ := Γ) tuB m (pairT K (fact L)))
  have t0 := natEq ((tuB_at (Γ := Γ) zero K (fact L)).eqTrans (zero_mul_l (conv_zero one one _) _))
  ipra_le sl s with b + t0

/-! ## The pointwise comparison -/

/-- The hypotheses: `m = k + 1 ≤ x`, `K ≥ 1`, `(x + 1)⁴ ≤ K`, `K (x + 1)⁴ ≤ L`. -/
structure Hyp (k K L x : PTm n) (Γ : List (Fm PTm n)) : Prop where
  hK : Γ ⊢[PRAAx] le one K
  hkx : Γ ⊢[PRAAx] le (succ k) x
  hx4 : Γ ⊢[PRAAx] le (Q4 x) K
  hL : Γ ⊢[PRAAx] le (K * Q4 x) L

section
variable {k K L x : PTm n} (h : Hyp k K L x Γ)
include h

theorem Hyp.hKx : Γ ⊢[PRAAx] le (K * x) L := le_trans (le_scale K (le_Q4 x)) h.hL
theorem Hyp.hkK : Γ ⊢[PRAAx] le (succ k) K := le_trans h.hkx (le_trans (le_Q4 x) h.hx4)
theorem Hyp.hKk : Γ ⊢[PRAAx] le (K * succ k) L := le_trans (le_scale K h.hkx) h.hKx
theorem Hyp.hx : Γ ⊢[PRAAx] le one x := le_trans (le_succ' (zero_le k)) h.hkx
theorem Hyp.hL4 : Γ ⊢[PRAAx] le (K * Q4 (qr (succ k))) L :=
  le_trans (le_scale K (Q4_mono (le_trans (isqrt_le_self _) (le_trans (isqrt_le_self _) h.hkx)))) h.hL

/-- `(m + 1) m m ⌊F/K⌋ ≤ F` for `m = k + 1`. -/
theorem Hyp.cubic : Γ ⊢[PRAAx] le (succ k * (succ (succ k) * (succ k * quo (fact L) K))) (fact L) := by
  have s1 : Γ ⊢[PRAAx] le (succ k) (succ x) := le_trans h.hkx (le_of_eq_add (d := one) (by ipra_ring))
  have c := le_trans (le_mul2 (le_succ' h.hkx) (le_mul2 s1 s1)) (le_trans (cube_le_Q4 x) h.hx4)
  have q := mul_le_mul_right (quo (fact L) K) c
  have r := quo_mul_le (Γ := Γ) (x := fact L) (pos_of_lt_zero h.hK)
  ipra_le sl q + sl r

end

/-- `W(m) = (⌊m^{1/4}⌋ + 1)³`. -/
abbrev W (m : PTm n) : PTm n := succ (qr m) * succ (qr m) * succ (qr m)

/-- `E(m) = 146 F² W(m) + 2 F²`. -/
abbrev E (m F : PTm n) : PTm n := num 146 * (F * F * W m) + two * (F * F)

/-- `Φ(m) ≤ B(m) + Ψ(m) + E(m)`: `F Σ τ L_w + 4C² m ≤ Σ L_w² + 2CF D(m) + E(m)`. -/
theorem point_upper {k K L x : PTm n} (h : Hyp k K L x Γ) :
    Γ ⊢[PRAAx] le (fact L * ap2 (sumF twB) (succ k) (pairT K (fact L)) +
        two * (two * (CT K x (fact L) * (CT K x (fact L) * succ k))))
      (Bs (bL wt) (succ k) (pairT K (fact L)) + two * (CT K x (fact L) * (fact L * S (succ k) (succ k))) +
        E (succ k) (fact L)) := by
  have tw := le_scale (fact L) (tw_le_tu h.hK h.hKk)
  have ab := natEq (abel_tau (Γ := Γ) (succ k) K (fact L))
  have cu := comparison_upper h.hK h.hKx h.hkx h.hkK
  have ev := env_upper h.hK (le_succ' (zero_le k)) h.hx h.hKx h.hL4
  have bh := bridge_hi h.hK h.hKk
  -- the bridge error `m · 2m ⌊F/K⌋ u_m ≤ 2F²`
  have uk := u_le_kF (Γ := Γ) k (fact L) h.hK
  have e1 := le_scale (succ k * (two * (succ k * quo (fact L) K))) uk
  have kc : Γ ⊢[PRAAx] le (succ k * (succ k * (k * quo (fact L) K))) (fact L) := by
    have c := h.cubic
    ipra_le sl c + 2 * ((𝔞 k + 1) * (𝔞 k + 1) * 𝔞 (quo (fact L) K))
  have e2 := le_scale (two * fact L) kc
  ipra_le sl tw + sl cu + sl ev + sl bh + sl e1 + sl e2 + 4 * (𝔞 (fact L) * 𝔞 (fact L) * 𝔞 (W (succ k))) with
    𝔞 (fact L) * ab

/-- `B(m) + Ψ(m) ≤ Φ(m) + E(m)`: `Σ L_w² + 2CF D(m) ≤ F Σ τ L_w + 4C² m + E(m)`. -/
theorem point_lower {k K L x : PTm n} (h : Hyp k K L x Γ) :
    Γ ⊢[PRAAx] le (Bs (bL wt) (succ k) (pairT K (fact L)) + two * (CT K x (fact L) * (fact L * S (succ k) (succ k))))
      (fact L * ap2 (sumF twB) (succ k) (pairT K (fact L)) +
        two * (two * (CT K x (fact L) * (CT K x (fact L) * succ k))) + E (succ k) (fact L)) := by
  have bl := bridge_lo h.hK h.hKk
  have ab := natEq (abel_tau (Γ := Γ) (succ k) K (fact L))
  have cl := comparison_lower h.hK h.hKx h.hkx h.hkK
  have ev := env_lower h.hK (le_succ' (zero_le k)) h.hx h.hKx h.hL4
  have tu := le_scale (fact L) (tu_le_tw h.hK h.hKk)
  have cb := le_scale (fact L) h.cubic
  ipra_le sl bl + sl cl + sl ev + sl tu + sl cb + 𝔞 (fact L) * 𝔞 (fact L) with -(𝔞 (fact L) * ab)

end LeanProofs.IPRA.AnalyticNumberTheory.SymmetryPointwise

export_ipra AnalyticNumberTheory.SymmetryPointwise (le_Q4 quo_mul_le)
