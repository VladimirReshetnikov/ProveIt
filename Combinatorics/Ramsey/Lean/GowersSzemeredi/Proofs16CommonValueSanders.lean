import GowersSzemeredi.Proofs16CommonValueFreiman
import GowersSzemeredi.Proofs16SandersLinearPart

/-! The new map of Claim 9.4 with a low-rank linear part (J.5c Further
question 3).

`freiman_common_value` makes `Θ` a Freiman 8-homomorphism on a set `B` of
`a`'s carrying `κ(c/2)²N²` pairs. Each `a` carries at most `N` pairs, so
`|B| ≥ κ(c/2)²N`. `sanders_linear_part` at `p = log(1/(κ(c/2)²))` then gives
a linear part `ψ` that is Freiman-linear on a Bohr set of rank
`≤ 1 + C(p+1)⁴`, polylogarithmic in the density, with
`Θ a − Θ a′ = ψ(a − a′)` on `B`.
* `freiman_common_value_sanders` states this. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- The density of `freiman_common_value`'s set of values. -/
def commonValueDensity (c : Real) : Real :=
  (2 : Real) ^ (-(1882 : Real)) * ((c / 2) ^ 4) ^ 1164 * (c / 2) ^ 2

/-- **The common value with a Sanders-strength linear part.** -/
theorem freiman_common_value_sanders {N : Nat} [NeZero N] [Fact N.Prime]
    (Θ ψ₀ ψ₁ : ZMod N → ZMod N) (P : Finset (ZMod N × ZMod N))
    (hP : ∀ p ∈ P, Θ p.2 = ψ₀ (p.1 + p.2) - ψ₁ p.1)
    {c : Real} (hc : 0 < c) (hc1 : c ≤ 1) (hPc : c * (N : Real) ^ 2 ≤ P.card) :
    ∃ (B : Finset (ZMod N)) (Γ : Finset (ZMod N)) (ρ : Real) (ψ : ZMod N → ZMod N),
      FreimanHom 8 B Θ ∧
      commonValueDensity c * (N : Real) ^ 2 ≤ (P.filter fun p => p.2 ∈ B).card ∧
      (Γ.card : Real) ≤ 1 + OAI.Erdos3.CyclicCrootSisask.quarticBogolyubovConstant *
        (Real.log (1 / commonValueDensity c) + 1) ^ 4 ∧
      Real.exp (-(OAI.Erdos3.CyclicCrootSisask.quarticBogolyubovConstant *
        (Real.log (1 / commonValueDensity c) + 1))) / (2 * Real.pi) ≤ ρ ∧ 0 < ρ ∧
      IsFreimanLinearOn (bohr Γ ρ) ψ ∧ ψ 0 = 0 ∧
      ∀ a ∈ B, ∀ a' ∈ B, Θ a - Θ a' = ψ (a - a') := by
  have hN : (0 : Real) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨B, hF, hcnt⟩ := freiman_common_value Θ ψ₀ ψ₁ P hP hc hPc
  set δ := commonValueDensity c with hδ
  have hδpos : 0 < δ := by simp only [hδ, commonValueDensity]; positivity
  have hδ1 : δ ≤ 1 := by
    simp only [hδ, commonValueDensity]
    have h1 : (2 : Real) ^ (-(1882 : Real)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    have hc2 : c / 2 ≤ 1 := by linarith
    have h2 : ((c / 2) ^ 4) ^ 1164 ≤ 1 := pow_le_one₀ (by positivity) (pow_le_one₀ (by positivity) hc2)
    have h3 : (c / 2) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) hc2
    calc (2 : Real) ^ (-(1882 : Real)) * ((c / 2) ^ 4) ^ 1164 * (c / 2) ^ 2 ≤ 1 * 1 * 1 := by
          gcongr
      _ = 1 := by ring
  -- `|B| ≥ δN`: each value carries at most `N` pairs
  have hBcard : δ * (N : Real) ≤ B.card := by
    have h := Finset.card_le_mul_card_image (f := fun p : ZMod N × ZMod N => p.2)
      (P.filter fun p => p.2 ∈ B) N (by
        intro a _
        have : ((P.filter fun p => p.2 ∈ B).filter fun p => p.2 = a).card ≤
            (Finset.univ : Finset (ZMod N)).card := by
          refine Finset.card_le_card_of_injOn (fun p => p.1) (fun _ _ => by simp) ?_
          intro p hp p' hp' h
          exact Prod.ext h ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hp').2.symm)
        rwa [Finset.card_univ, ZMod.card] at this)
    have himg : ((P.filter fun p => p.2 ∈ B).image fun p => p.2) ⊆ B := by
      intro a ha
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
      exact (Finset.mem_filter.mp hp).2
    have h1 : (((P.filter fun p => p.2 ∈ B).card : Nat) : Real) ≤ (N : Real) * B.card := by
      exact_mod_cast h.trans (Nat.mul_le_mul_left _ (Finset.card_le_card himg))
    have hcnt' : δ * (N : Real) ^ 2 ≤ ((P.filter fun p => p.2 ∈ B).card : Real) := hcnt
    have h2 : δ * (N : Real) * N ≤ (B.card : Real) * N := by nlinarith
    exact le_of_mul_le_mul_right h2 hN
  set p := Real.log (1 / δ) with hp
  have hp0 : 0 ≤ p := Real.log_nonneg (by rw [le_div_iff₀ hδpos]; linarith)
  have hBdens : Real.exp (-p) * N ≤ (B.card : Real) := by
    rw [hp, Real.log_div one_ne_zero hδpos.ne', Real.log_one, zero_sub, neg_neg,
      Real.exp_log hδpos]
    exact hBcard
  obtain ⟨Γ, ρ, ψ, hΓ, hρ, hρpos, hψ, hψ0, hdiff⟩ := sanders_linear_part B Θ hF hp0 hBdens
  exact ⟨B, Γ, ρ, ψ, hF, hcnt, hΓ, hρ, hρpos, hψ, hψ0, hdiff⟩

end LeanProofs.GowersSzemeredi
