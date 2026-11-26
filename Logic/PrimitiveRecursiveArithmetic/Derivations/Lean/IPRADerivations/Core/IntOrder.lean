import IPRADerivations.Probability.Variance
import IPRADerivations.AnalyticNumberTheory.PhiLower

/-!
# Order on integer terms, and the triangle inequality without square roots

For integer terms `u = u⁺ − u⁻` (`ZT`), `zle u v` is the iPRA formula `u⁺ + v⁻ ≤ v⁺ + u⁻`, i.e.
`u ≤ v`. Inequalities are proved through natural-number witnesses: `zle u v` holds iff
`v = u + D` for a natural-number term `D`.

* `zle_of_toZ`, `zle_toZ`: the witness form;
* `sq_nat`: `x² = abs(x⁺ − x⁻)²` is a natural number;
* `nat_sqrt_mono`: `S² ≤ T² → S ≤ T` for natural numbers;
* `dot_le`: if `x₁² + y₁² ≤ a²` and `x₂² + y₂² ≤ b²` (with `a, b` natural), then
  `x₁x₂ + y₁y₂ ≤ ab`, from the Lagrange identity;
* `triangle`: under the same hypotheses `(x₁ + x₂)² + (y₁ + y₂)² ≤ (a + b)²`: the triangle
  inequality for the modulus of Gaussian integers, `|u| ≤ a`, `|v| ≤ b ⟹ |u + v| ≤ a + b`, without
  square roots.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA.Probability.Variance (ad ad_sq)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `u ≤ v` for integer terms. -/
def zle (u v : ZT n) : Fm PTm n := le (u.pos + v.neg) (v.pos + u.neg)

theorem toZ_def (u : ZT n) : ZT.toZ Γ u = Groth.ι (Q.mk Γ u.pos) - Groth.ι (Q.mk Γ u.neg) := rfl

/-- `u + D = v` with `D` natural gives `u ≤ v`. -/
theorem zle_of_toZ {u v : ZT n} (D : PTm n) (h : ZT.toZ Γ u + Groth.ι (Q.mk Γ D) = ZT.toZ Γ v) :
    Γ ⊢[PRAAx] zle u v := by
  refine le_of_eq_add (d := D) ?_
  rw [toZ_def, toZ_def] at h
  ipra_lc -h

/-- The witness of `u ≤ v`. -/
theorem zle_toZ {u v : ZT n} (h : Γ ⊢[PRAAx] zle u v) :
    ZT.toZ Γ u + Groth.ι (Q.mk Γ (monus (v.pos + u.neg) (u.pos + v.neg))) = ZT.toZ Γ v := by
  have e := natEq (eq_add_of_le h)
  rw [toZ_def, toZ_def]
  simp only [Q.mk_add, map_add] at e
  linear_combination -e

/-- `x² = abs(x⁺ − x⁻)²`. -/
theorem sq_nat (x : ZT n) :
    ZT.toZ Γ (ZT.sq x) = Groth.ι (Q.mk Γ (ad x.pos x.neg * ad x.pos x.neg)) := by
  have e := natEq (ad_sq (Γ := Γ) x.pos x.neg)
  rw [ZT.toZ_sq, toZ_def]
  simp only [Q.mk_add, Q.mk_mul, map_add, map_mul] at e ⊢
  linear_combination -e

/-- `S² ≤ T² → S ≤ T` for natural numbers. -/
alias nat_sqrt_mono := Common.le_of_sq_le

section Triangle

variable {a b : PTm n} {x₁ y₁ x₂ y₂ : ZT n}

/-- `x₁x₂ + y₁y₂ ≤ ab` from `x₁² + y₁² ≤ a²`, `x₂² + y₂² ≤ b²`. -/
theorem dot_le (h₁ : Γ ⊢[PRAAx] zle (ZT.sq x₁ + ZT.sq y₁) (ZT.ofNat (a * a)))
    (h₂ : Γ ⊢[PRAAx] zle (ZT.sq x₂ + ZT.sq y₂) (ZT.ofNat (b * b))) :
    Γ ⊢[PRAAx] zle (x₁ * x₂ + y₁ * y₂) (ZT.ofNat (a * b)) := by
  have w₁ := zle_toZ h₁; have w₂ := zle_toZ h₂
  generalize hs : x₁ * x₂ + y₁ * y₂ = s
  generalize hc : x₁ * y₂ - x₂ * y₁ = c
  have es : ZT.toZ Γ s = ZT.toZ Γ x₁ * ZT.toZ Γ x₂ + ZT.toZ Γ y₁ * ZT.toZ Γ y₂ := by rw [← hs]; simp
  have ec : ZT.toZ Γ c = ZT.toZ Γ x₁ * ZT.toZ Γ y₂ - ZT.toZ Γ x₂ * ZT.toZ Γ y₁ := by rw [← hc]; simp
  generalize hD₁ : monus ((ZT.ofNat (a * a)).pos + (ZT.sq x₁ + ZT.sq y₁).neg)
    ((ZT.sq x₁ + ZT.sq y₁).pos + (ZT.ofNat (a * a)).neg) = D₁ at w₁
  generalize hD₂ : monus ((ZT.ofNat (b * b)).pos + (ZT.sq x₂ + ZT.sq y₂).neg)
    ((ZT.sq x₂ + ZT.sq y₂).pos + (ZT.ofNat (b * b)).neg) = D₂ at w₂
  simp only [ZT.toZ_add, ZT.toZ_sq, ZT.toZ_ofNat, Q.mk_mul, map_mul] at w₁ w₂
  refine .orE (le_total s.pos s.neg) ?_ ?_
  · -- `s ≤ 0 ≤ ab`.
    have e := natEq (eq_add_of_le (Prf.hyp0 (Ax := PRAAx) (Γ := Γ) (φ := le s.pos s.neg)))
    refine zle_of_toZ (monus s.neg s.pos + a * b) ?_
    rw [toZ_def (u := s), ZT.toZ_ofNat]
    simp only [Q.mk_add, Q.mk_mul, map_add, map_mul] at e ⊢
    linear_combination -e
  · -- `s = σ ≥ 0` with `σ² ≤ (ab)²`.
    have e := natEq (eq_add_of_le (Prf.hyp0 (Ax := PRAAx) (Γ := Γ) (φ := le s.neg s.pos)))
    have tσ : ZT.toZ (le s.neg s.pos :: Γ) s = Groth.ι (Q.mk _ (monus s.pos s.neg)) := by
      rw [toZ_def]; simp only [Q.mk_add, map_add] at e; linear_combination e
    have px₁ := sq_nat (Γ := le s.neg s.pos :: Γ) x₁; have py₁ := sq_nat (Γ := le s.neg s.pos :: Γ) y₁
    have px₂ := sq_nat (Γ := le s.neg s.pos :: Γ) x₂; have py₂ := sq_nat (Γ := le s.neg s.pos :: Γ) y₂
    have pc := sq_nat (Γ := le s.neg s.pos :: Γ) c
    rw [ZT.toZ_sq] at px₁ py₁ px₂ py₂ pc
    have es' : ZT.toZ (le s.neg s.pos :: Γ) s = ZT.toZ _ x₁ * ZT.toZ _ x₂ + ZT.toZ _ y₁ * ZT.toZ _ y₂ := by
      rw [← hs]; simp
    have ec' : ZT.toZ (le s.neg s.pos :: Γ) c = ZT.toZ _ x₁ * ZT.toZ _ y₂ - ZT.toZ _ x₂ * ZT.toZ _ y₁ := by
      rw [← hc]; simp
    have w₁' : ZT.toZ (le s.neg s.pos :: Γ) x₁ ^ 2 + ZT.toZ _ y₁ ^ 2 + Groth.ι (Q.mk _ D₁) =
        Groth.ι (Q.mk _ a) * Groth.ι (Q.mk _ a) := by
      have := zle_toZ (h₁.wk (ψ := le s.neg s.pos)); rw [hD₁] at this
      simpa only [ZT.toZ_add, ZT.toZ_sq, ZT.toZ_ofNat, Q.mk_mul, map_mul] using this
    have w₂' : ZT.toZ (le s.neg s.pos :: Γ) x₂ ^ 2 + ZT.toZ _ y₂ ^ 2 + Groth.ι (Q.mk _ D₂) =
        Groth.ι (Q.mk _ b) * Groth.ι (Q.mk _ b) := by
      have := zle_toZ (h₂.wk (ψ := le s.neg s.pos)); rw [hD₂] at this
      simpa only [ZT.toZ_add, ZT.toZ_sq, ZT.toZ_ofNat, Q.mk_mul, map_mul] using this
    have sq : (le s.neg s.pos :: Γ) ⊢[PRAAx] le (monus s.pos s.neg * monus s.pos s.neg) ((a * b) * (a * b)) := by
      refine le_of_eq_add (d := (ad x₁.pos x₁.neg * ad x₁.pos x₁.neg + ad y₁.pos y₁.neg * ad y₁.pos y₁.neg) * D₂ +
        (ad x₂.pos x₂.neg * ad x₂.pos x₂.neg + ad y₂.pos y₂.neg * ad y₂.pos y₂.neg) * D₁ + D₁ * D₂ +
        ad c.pos c.neg * ad c.pos c.neg) ?_
      ipra_lc (-1 : Groth (Q (le s.neg s.pos :: Γ))) * ( (Groth.ι (Q.mk _ b) * Groth.ι (Q.mk _ b)) * w₁' + (ZT.toZ (le s.neg s.pos :: Γ) x₁ ^ 2 + ZT.toZ _ y₁ ^ 2 + Groth.ι (Q.mk _ D₁)) * w₂' - (Groth.ι (Q.mk _ (monus s.pos s.neg)) + ZT.toZ _ s) * tσ + (ZT.toZ _ s + ZT.toZ _ x₁ * ZT.toZ _ x₂ + ZT.toZ _ y₁ * ZT.toZ _ y₂) * es' + (ZT.toZ _ c + ZT.toZ _ x₁ * ZT.toZ _ y₂ - ZT.toZ _ x₂ * ZT.toZ _ y₁) * ec' - Groth.ι (Q.mk _ D₂) * (px₁ + py₁) - Groth.ι (Q.mk _ D₁) * (px₂ + py₂) - pc)
    have le' := nat_sqrt_mono sq
    have e₂ := natEq (eq_add_of_le le')
    refine zle_of_toZ (monus (a * b) (monus s.pos s.neg)) ?_
    rw [tσ, ZT.toZ_ofNat]
    simp only [Q.mk_add, Q.mk_mul, map_add, map_mul] at e₂ ⊢
    linear_combination -e₂

/-- The triangle inequality for Gaussian integers without square roots:
`x₁² + y₁² ≤ a²` and `x₂² + y₂² ≤ b²` give `(x₁ + x₂)² + (y₁ + y₂)² ≤ (a + b)²`. -/
theorem triangle (h₁ : Γ ⊢[PRAAx] zle (ZT.sq x₁ + ZT.sq y₁) (ZT.ofNat (a * a)))
    (h₂ : Γ ⊢[PRAAx] zle (ZT.sq x₂ + ZT.sq y₂) (ZT.ofNat (b * b))) :
    Γ ⊢[PRAAx] zle (ZT.sq (x₁ + x₂) + ZT.sq (y₁ + y₂)) (ZT.ofNat ((a + b) * (a + b))) := by
  obtain ⟨D₁, w₁⟩ : ∃ D : PTm n, ZT.toZ Γ (ZT.sq x₁ + ZT.sq y₁) + Groth.ι (Q.mk Γ D) =
      ZT.toZ Γ (ZT.ofNat (a * a)) := ⟨_, zle_toZ h₁⟩
  obtain ⟨D₂, w₂⟩ : ∃ D : PTm n, ZT.toZ Γ (ZT.sq x₂ + ZT.sq y₂) + Groth.ι (Q.mk Γ D) =
      ZT.toZ Γ (ZT.ofNat (b * b)) := ⟨_, zle_toZ h₂⟩
  obtain ⟨E, wd⟩ : ∃ D : PTm n, ZT.toZ Γ (x₁ * x₂ + y₁ * y₂) + Groth.ι (Q.mk Γ D) =
      ZT.toZ Γ (ZT.ofNat (a * b)) := ⟨_, zle_toZ (dot_le h₁ h₂)⟩
  refine zle_of_toZ (D₁ + D₂ + (E + E)) ?_
  simp only [ZT.toZ_add, ZT.toZ_sq, ZT.toZ_mul, ZT.toZ_ofNat, Q.mk_add, Q.mk_mul, map_add, map_mul] at w₁ w₂ wd ⊢
  linear_combination w₁ + w₂ + 2 * wd

end Triangle

end LeanProofs.IPRA
