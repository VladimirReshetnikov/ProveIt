import IPRADerivations.Core.BoundedSums
import IPRADerivations.Core.OrderCertificates

/-!
# The geometric tail of a half-contraction

Packet: `analysis/ipra_certified_continuation_2026-11-19`, `lean/FeedbackReference.lean` (an ambient Lean
reference model over rationals; its object-theory port is listed as open there): `increment_bound` (successive
increments of the orbit of a half-contraction are at most `D 2^{−n}`), `finite_segment` and `finite_tail`
("The exact finite geometric tail, before any interpretation by real numbers": the orbit moves at most
`2D 2^{−n}` after stage `n`).

Object-level derivations for the scalar increments: for a body `d(i, x)` (the size of the `i`-th increment of a
primitive recursive orbit), with the half-contraction `2 d_{i+1} ≤ d_i` as one object premise over all `i`:

* `halving`: `2^i d_i ≤ d_0` (quantifier-free induction);
* `antitone_le`: a body with `u_{k+1} ≤ u_k` for all `k` satisfies `u_k ≤ u_m` whenever `m ≤ k`;
* `tail`: `2^n ∑_{i<n+j} d_i ≤ 2^n ∑_{i<n} d_i + 2 d_0`, i.e. the increments after stage `n` add up to at most
  `2 d_0 2^{−n}`, for every `j` (the potential `U_k = ∑_{i<k} d_i + 2 d_k` is non-increasing).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.HalfContractionTail

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The half-contraction premise `2 d_{i+1} ≤ d_i` for all `i`. -/
abbrev halfPrem (d : PTm 2) (x : PTm n) : Fm PTm n :=
  Fm.all (le (two * inst2 d (succ (var 0)) (Syn.shift x)) (inst2 d (var 0) (Syn.shift x)))

/-- `2^i d_i ≤ d_0`. -/
theorem halving (d : PTm 2) {x : PTm n} (hs : Γ ⊢[PRAAx] halfPrem d x) (i : PTm n) :
    Γ ⊢[PRAAx] le (pw two i * inst2 d i x) (inst2 d zero x) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (pw two (var 0) * inst2 d (var 0) (Syn.shift x)) (inst2 d zero (Syn.shift x))) := by
    ipra_qfind (le_QF _ _) [subst_le, subst_ap2, subst_inst2]
    · have p0 := natEq (pw_zero (Γ := Γ) two)
      ipra_le 0 using
        rw [p0]; ring
    · let x' := Syn.shift x
      let Δ := le (pw two (var 0) * inst2 d (var 0) x') (inst2 d zero x') :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] le (pw two (var 0) * inst2 d (var 0) x') (inst2 d zero x') := Prf.hyp0
      have hk : Δ ⊢[PRAAx] le (two * inst2 d (succ (var 0)) x') (inst2 d (var 0) x') := hs.allOpen.wk
      have f := natEq (pw_succ (Γ := Δ) two (var 0))
      show Δ ⊢[PRAAx] le (pw two (succ (var 0)) * inst2 d (succ (var 0)) x') (inst2 d zero x')
      ipra_le 𝔟 (pw two (var 0) : PTm (n + 1)) * sl hk + sl ih with
        𝔟 (inst2 d (succ (var 0)) x') * f
  have h := Prf.allE i hall
  simpa only [subst_le, PTm.subst_mul, subst_ap2, subst_inst2, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] using h

/-- A non-increasing body: `m ≤ k` gives `u_k ≤ u_m`. -/
theorem antitone_le (u : PTm 2) {x m k : PTm n}
    (hs : Γ ⊢[PRAAx] Fm.all (le (inst2 u (succ (var 0)) (Syn.shift x)) (inst2 u (var 0) (Syn.shift x))))
    (hmk : Γ ⊢[PRAAx] le m k) : Γ ⊢[PRAAx] le (inst2 u k x) (inst2 u m x) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (Syn.shift m) (var 0) ⟶
      le (inst2 u (var 0) (Syn.shift x)) (inst2 u (Syn.shift m) (Syn.shift x))) := by
    ipra_qfind (⟨le_QF _ _, le_QF _ _⟩) [subst_le, subst_inst2]
    · refine .impI ?_
      have e : (le m zero :: Γ) ⊢[PRAAx] m ≐ zero := le_antisymm Prf.hyp0 (zero_le _)
      exact le_congr (.eqRefl _) (congrInst2 u e.eqSymm (.eqRefl _)) (le_refl _)
    · refine .impI ?_
      let m' := Syn.shift m
      let x' := Syn.shift x
      let IH : Fm PTm (n + 1) := le m' (var 0) ⟶ le (inst2 u (var 0) x') (inst2 u m' x')
      let Δ := le m' (succ (var 0)) :: IH :: Γ.map Fm.shift
      have hab : Δ ⊢[PRAAx] le m' (succ (var 0)) := Prf.hyp0
      refine .orE (lt_or_eq_of_le hab) ?_ ?_
      · have prior : (lt m' (succ (var 0)) :: Δ) ⊢[PRAAx] le m' (var 0) :=
          (succ_monus_succ m' (var 0)).eqSymm.eqTrans Prf.hyp0
        have ih : (lt m' (succ (var 0)) :: Δ) ⊢[PRAAx] IH := Prf.hyp1.wk
        have hk : (lt m' (succ (var 0)) :: Δ) ⊢[PRAAx]
            le (inst2 u (succ (var 0)) x') (inst2 u (var 0) x') := hs.allOpen.wk.wk.wk
        exact le_trans hk (Prf.impE ih prior)
      · exact le_congr (.eqRefl _) (congrInst2 u Prf.hyp0.eqSymm (.eqRefl _)) (le_refl _)
  have h := Prf.allE k hall
  simp only [Fm.subst_imp, subst_le, subst_inst2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at h
  exact Prf.impE h hmk

/-- The potential `U_k = ∑_{i<k} d_i + 2 d_k`. -/
abbrev uB (d : PTm 2) : PTm 2 := ap2 (sumF d) (var 0) (var 1) + two * d

theorem inst2_uB (d : PTm 2) (k x : PTm n) :
    inst2 (uB d) k x = ap2 (sumF d) k x + two * inst2 d k x := by
  simp [inst2, uB, subst_ap2]

/-- `2^n ∑_{i<n+j} d_i ≤ 2^n ∑_{i<n} d_i + 2 d_0`. -/
theorem tail (d : PTm 2) {x : PTm n} (hs : Γ ⊢[PRAAx] halfPrem d x) (m j : PTm n) :
    Γ ⊢[PRAAx] le (pw two m * ap2 (sumF d) (m + j) x) (pw two m * ap2 (sumF d) m x + two * inst2 d zero x) := by
  have hU : Γ ⊢[PRAAx] Fm.all (le (inst2 (uB d) (succ (var 0)) (Syn.shift x)) (inst2 (uB d) (var 0) (Syn.shift x))) := by
    refine Prf.allI ?_
    rw [inst2_uB, inst2_uB]
    have hk : Γ.map Fm.shift ⊢[PRAAx] le (two * inst2 d (succ (var 0)) (Syn.shift x)) (inst2 d (var 0) (Syn.shift x)) :=
      hs.allOpen
    have es := natEq (sum_succ' (Γ := Γ.map Fm.shift) d (var 0) (Syn.shift x))
    ipra_le sl hk with es
  have hmono := antitone_le (uB d) hU (show Γ ⊢[PRAAx] le m (m + j) by ipra_le 𝔟 j)
  rw [inst2_uB, inst2_uB] at hmono
  have hh := halving d hs m
  ipra_le 𝔟 (pw two m) * sl hmono + 2 * 𝔟 (pw two m) * 𝔟 (inst2 d (m + j) x) + 2 * sl hh

end LeanProofs.IPRA.Analysis.HalfContractionTail
