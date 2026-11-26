import IPRADerivations.Foundations.BoundedReflection
import IPRADerivations.Combinatorics.CoefficientLogConcave

/-!
# The rational volume cut

Packet: `geometry/isoperimetric_ipra_constructive_2026-11-15`, `report/euclidean.tex`,
`lem:rational-cut`: "A rational `t` can be computed such that the pieces `Y⁻ = Y ∩ {x_i ≤ t}` and
`Y⁺ = Y ∩ {x_i ≥ t}` have volumes `λ V(Y)` and `(1 − λ) V(Y)`." Proof: "Sort the finitely many
endpoints in coordinate `i`. Between two consecutive endpoints `u < v`, the cross-sectional
`(n − 1)`-volume is a constant rational `A ≥ 0` ... Scan these intervals, adding `A (v − u)`,
until the target `λ V(Y)` is reached or crossed. ... Otherwise the target lies strictly inside
an interval with `A > 0`; if the volume accumulated at its left endpoint is `F`, choose
`t = u + (λ V(Y) − F)/A`."

The slabs between consecutive endpoints are indexed by `j < n`, with cross-section `A_j` and
width `ℓ_j` given by arbitrary bodies (cleared of a common denominator), prefix volumes
`F(k) = Σ_{j<k} A_j ℓ_j`, and a target `τ` (`λ V(Y)` cleared) with `τ < F(n) = V(Y)`:

* `cB`, `idx`: the scan, the least `k` with `τ < F(k + 1)`, as a bounded search;
* `cross`: `k < n`, `F(k) ≤ τ < F(k + 1)`;
* `cut`: in the slab `k`: `A_k ≥ 1`, the numerator `c = τ − F(k)` of the offset `(τ − F(k))/A_k`
  satisfies `c < A_k ℓ_k` (the cut lies in the slab, `t = u_k + c/A_k < u_k + ℓ_k`), and
  `F(k) + c = τ` (the left piece has volume `τ`; the right piece has `V(Y) − τ`).

The scan stops at the first slab where the target is strictly crossed; when the target is
reached exactly at an endpoint (`c = 0`) the same formula gives that endpoint. Not derived: the
sorting of the endpoints, the clipping of the boxes and the count of pieces.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.RationalCut

open_ipra
open LeanProofs.IPRA.Combinatorics.CoefficientLogConcave (inst2_mul inst2_monus inst2_ap2)
open LeanProofs.IPRA.Foundations.BoundedReflection (exB wit ex_intro ex_elim ex_least)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (eq_succ_pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem lt_of_monus_ne {a b : PTm n} (h : Γ ⊢[PRAAx] neg (monus a b ≐ zero)) :
    Γ ⊢[PRAAx] lt b a :=
  .orE (lt_or_le b a) Prf.hyp0 (.botE _ (.impE h.wk Prf.hyp0))

theorem monus_ne_of_lt {a b : PTm n} (h : Γ ⊢[PRAAx] lt b a) :
    Γ ⊢[PRAAx] neg (monus a b ≐ zero) :=
  .impI (le_lt_absurd _ (Prf.hyp0 (Γ := Γ) (φ := le a b)) h.wk)

section Scan

variable (w : PTm 2)

/-- `F(j + 1) ∸ τ`, nonzero exactly when `τ < F(j + 1)`; over `0 = j`, `1 = ⟨τ, x⟩`. -/
def cB : PTm 2 := monus (ap2 (sumF w) (succ (var 0)) (sndT (var 1))) (fstT (var 1))

theorem c_at (j τ x : PTm n) :
    Γ ⊢[PRAAx] inst2 (cB w) j (pairT τ x) ≐ monus (ap2 (sumF w) (succ j) x) τ := by
  have h : inst2 (cB w) j (pairT τ x) =
      monus (ap2 (sumF w) (succ j) (sndT (pairT τ x))) (fstT (pairT τ x)) := by
    simp only [cB, inst2_monus, inst2_ap2]; simp [inst2]
  rw [h]
  exact congrMonus (congrAp2 _ (.eqRefl _) (snd_pair _ _)) (fst_pair _ _)

/-- The first slab in which the target is crossed. -/
abbrev idx (τ N x : PTm n) : PTm n := wit (cB w) N (pairT τ x)

/-- `lem:rational-cut`, the scan: for `τ < F(N)` the index `k = idx` satisfies `k < N` and
`F(k) ≤ τ < F(k + 1)`. -/
theorem cross {τ N x : PTm n} (h : Γ ⊢[PRAAx] lt τ (ap2 (sumF w) N x)) :
    Γ ⊢[PRAAx] lt (idx w τ N x) N ⋏
      (le (ap2 (sumF w) (idx w τ N x) x) τ ⋏ lt τ (ap2 (sumF w) (succ (idx w τ N x)) x)) := by
  -- `N ≥ 1`
  have hN : Γ ⊢[PRAAx] N ≐ succ (pred N) := by
    refine .orE (zero_or_succ N) ?_ Prf.hyp0
    exact lt_zero_absurd _ (lt_congr (.eqRefl _)
      ((congrAp2 _ Prf.hyp0 (.eqRefl _)).eqTrans (sum_zero w x)) h.wk)
  have hw : Γ ⊢[PRAAx] neg (inst2 (cB w) (pred N) (pairT τ x) ≐ zero) := by
    refine .impI (.impE (monus_ne_of_lt (lt_congr (.eqRefl _)
      (congrAp2 _ hN (.eqRefl _)) h)).wk ((c_at w _ _ _).eqSymm.eqTrans Prf.hyp0))
  have hlt : Γ ⊢[PRAAx] lt (pred N) N := le_congr (.eqRefl _) hN.eqSymm (le_refl _)
  have el := ex_elim (cB w) (ex_intro (cB w) hw hlt)
  have upper : Γ ⊢[PRAAx] lt τ (ap2 (sumF w) (succ (idx w τ N x)) x) :=
    lt_of_monus_ne (.impI (.impE (Prf.andE₂ el).wk ((c_at w _ _ _).eqTrans Prf.hyp0)))
  have lower : Γ ⊢[PRAAx] le (ap2 (sumF w) (idx w τ N x) x) τ := by
    refine .orE (zero_or_succ (idx w τ N x)) ?_ ?_
    · exact le_congr ((congrAp2 _ Prf.hyp0 (.eqRefl _)).eqTrans (sum_zero w x)).eqSymm
        (.eqRefl _) (zero_le τ)
    · have e : ((idx w τ N x ≐ succ (pred (idx w τ N x))) :: Γ) ⊢[PRAAx]
          idx w τ N x ≐ succ (pred (idx w τ N x)) := Prf.hyp0
      have z := ex_least (cB w) (N := N) (x := pairT τ x) (j := pred (idx w τ N x))
        (le_congr (.eqRefl _) e.eqSymm (le_refl _))
      have z' : ((idx w τ N x ≐ succ (pred (idx w τ N x))) :: Γ) ⊢[PRAAx]
          monus (ap2 (sumF w) (succ (pred (idx w τ N x))) x) τ ≐ zero :=
        (c_at w _ _ _).eqSymm.eqTrans z
      exact (congrMonus (congrAp2 _ e (.eqRefl _)) (.eqRefl _)).eqTrans z'
  exact .andI (Prf.andE₁ el) (.andI lower upper)

end Scan

section Cut

variable (A L : PTm 2)

/-- `lem:rational-cut`, the cut: in the crossing slab `k`, `A_k ≥ 1`, the numerator
`c = τ − F(k)` of the offset `c / A_k` is less than `A_k ℓ_k`, and `F(k) + c = τ`. -/
theorem cut {τ N x : PTm n} (h : Γ ⊢[PRAAx] lt τ (ap2 (sumF (A * L)) N x)) :
    Γ ⊢[PRAAx]
      (inst2 A (idx (A * L) τ N x) x ≐ succ (pred (inst2 A (idx (A * L) τ N x) x))) ⋏
      (lt (monus τ (ap2 (sumF (A * L)) (idx (A * L) τ N x) x))
          (inst2 A (idx (A * L) τ N x) x * inst2 L (idx (A * L) τ N x) x) ⋏
        (ap2 (sumF (A * L)) (idx (A * L) τ N x) x +
          monus τ (ap2 (sumF (A * L)) (idx (A * L) τ N x) x) ≐ τ)) := by
  have c := cross (A * L) h
  have lower := Prf.andE₁ (Prf.andE₂ c)
  have upper := Prf.andE₂ (Prf.andE₂ c)
  have s := sum_succ' (Γ := Γ) (A * L) (idx (A * L) τ N x) x
  rw [inst2_mul] at s
  -- `F(k) + c = τ`
  have left : Γ ⊢[PRAAx] ap2 (sumF (A * L)) (idx (A * L) τ N x) x +
      monus τ (ap2 (sumF (A * L)) (idx (A * L) τ N x) x) ≐ τ := (eq_add_of_le lower).eqSymm
  -- `c < A_k ℓ_k`
  have inside : Γ ⊢[PRAAx] lt (monus τ (ap2 (sumF (A * L)) (idx (A * L) τ N x) x))
      (inst2 A (idx (A * L) τ N x) x * inst2 L (idx (A * L) τ N x) x) := by
    refine le_of_eq_add (d := monus (ap2 (sumF (A * L)) (succ (idx (A * L) τ N x)) x) (succ τ)) ?_
    ipra_lc natEq (eq_add_of_le upper) - natEq s + natEq (eq_add_of_le lower)
  -- `A_k ≥ 1`
  have pos : Γ ⊢[PRAAx] inst2 A (idx (A * L) τ N x) x ≐
      succ (pred (inst2 A (idx (A * L) τ N x) x)) := by
    refine .orE (zero_or_succ (inst2 A (idx (A * L) τ N x) x)) ?_ Prf.hyp0
    refine lt_zero_absurd _ (lt_congr (.eqRefl _) ?_ inside.wk)
    exact (congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _)
  exact .andI pos (.andI inside left)

end Cut

end LeanProofs.IPRA.Geometry.RationalCut
