import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Tactic

/-!
# Two arithmetic exclusions for the remaining field offsets

These lemmas contain no native word, mask, tile or calibration premise.
The first excludes value510 on a finite permutation with a single fixed
exceptional doubling branch. It permits the actual511 self-loop. The
second is a local residue obstruction and requires no finiteness at all.
-/

namespace DiophantineConsistency.FiniteInvariant

set_option Elab.async false
set_option maxHeartbeats 2000000

private theorem predecessor_units {x₁ x₂ x₃ a b c : ℕ}
    (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1)
    (h₁ : 510 = (2*x₁+a)%512)
    (h₂ : x₁ = (2*x₂+b)%512)
    (h₃ : x₂ = (2*x₃+c)%512) : b = 1 ∧ c = 1 := by
  omega

/-- Three predecessors of510 force two consecutive uses of the exceptional
branch, and hence force its fixed source value to be511. -/
private theorem exception_eq_511 {A : Type*} (sigma : A ≃ A)
    (S epsilon : A → ℕ) (sstar : ℕ)
    (hS : ∀ i, S i < 512) (he : ∀ i, epsilon i ≤ 1)
    (hstep : ∀ i, S (sigma i) = (2*S i + epsilon i)%512)
    (hgate : ∀ i, epsilon i = 1 → S i = sstar)
    (i : A) (hi : S i = 510) : sstar = 511 := by
  let a := sigma.symm i
  let b := sigma.symm a
  let c := sigma.symm b
  have ha : S i = (2*S a + epsilon a)%512 := by
    simpa only [a, Equiv.apply_symm_apply] using hstep a
  have hb : S a = (2*S b + epsilon b)%512 := by
    simpa only [b, Equiv.apply_symm_apply] using hstep b
  have hc : S b = (2*S c + epsilon c)%512 := by
    simpa only [c, Equiv.apply_symm_apply] using hstep c
  have hu := predecessor_units (he a) (he b) (he c) (hi ▸ ha) hb hc
  have hsb := hgate b hu.1
  have hsc := hgate c hu.2
  have hbound := hS b
  rw [hsb, hsc, hu.2] at hc
  omega

private theorem successor_mod_four {A : Type*} (sigma : A → A)
    (S epsilon : A → ℕ)
    (he : ∀ i, epsilon i ≤ 1)
    (hstep : ∀ i, S (sigma i) = (2*S i + epsilon i)%512)
    (hgate : ∀ i, epsilon i = 1 → S i = 511)
    (i : A) (hi : S i % 2 = 0) : S (sigma i) % 4 = 0 := by
  have hz : epsilon i = 0 := by
    have hb := he i
    by_contra hn
    have h1 : epsilon i = 1 := by omega
    have hs := hgate i h1
    omega
  have hs := hstep i
  rw [hz, add_zero] at hs
  omega

/-- Offset19 exclusion. The exceptional bit may occur only at a single
fixed source value, whose value is unrestricted in the hypotheses.
The conclusion excludes510, not every nonzero cycle. -/
theorem offset19_excludes_510 {A : Type*} [Finite A] (sigma : A ≃ A)
    (S epsilon : A → ℕ) (sstar : ℕ)
    (hS : ∀ i, S i < 512) (he : ∀ i, epsilon i ≤ 1)
    (hstep : ∀ i, S (sigma i) = (2*S i + epsilon i)%512)
    (hgate : ∀ i, epsilon i = 1 → S i = sstar) :
    ∀ i, S i ≠ 510 := by
  intro i hi
  have hstar := exception_eq_511 sigma S epsilon sstar hS he hstep hgate i hi
  have hgate' : ∀ j, epsilon j = 1 → S j = 511 := by
    intro j hj
    exact (hgate j hj).trans hstar
  have heven : ∀ j, S j % 2 = 0 → S (sigma j) % 2 = 0 := by
    intro j hj
    have hm := successor_mod_four sigma S epsilon he hstep hgate' j hj
    omega
  have hpre : S (sigma.symm i) % 2 = 0 :=
    Equiv.Perm.perm_symm_on_of_perm_on_finite heven (by omega)
  have hm := successor_mod_four sigma S epsilon he hstep hgate' _ hpre
  simp only [Equiv.apply_symm_apply, hi] at hm
  omega

/-- Offset20 exclusion. A two-bit prefix with value at most2 makes every
output0,1 or2 modulo4; an output510 would require a source3 modulo4.
No finite type, permutation, bound on S or terminal-color premise is used. -/
theorem offset20_excludes_510 {A : Type*} (theta : A → A)
    (S e : A → ℕ) (he : ∀ i, e i ≤ 2)
    (hstep : ∀ i, S i = (4*S (theta i))%512 + e i) :
    ∀ i, S i ≠ 510 := by
  intro i hi
  have h₁ := hstep i
  have h₂ := hstep (theta i)
  have he₁ := he i
  have he₂ := he (theta i)
  omega

#print axioms offset19_excludes_510
end DiophantineConsistency.FiniteInvariant
