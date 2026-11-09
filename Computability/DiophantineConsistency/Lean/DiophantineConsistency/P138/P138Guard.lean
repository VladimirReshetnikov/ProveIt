import DiophantineConsistency.P138.P138Canonical
import DiophantineConsistency.ZRows.ModelPellExistence

/-! # The guard Pell pair at the canonical data (stage C3)

At the canonical data (`P138Canonical.Canonical`), `PROOF.md` "Completeness with the new guard":

* `Budget > 64` (`P138Canonical.canonical_budget`), so `D = Budget − 4 > 0`;
* `Budget ≡ 0, 12 (mod 16)` (`P138Bootstrap.budget_mod`), so `D ≡ 12, 8 (mod 16)`, which no
  square is (`not_square_mod_sixteen`);
* hence `D τ²` is not a square either (`b² ∣ a² ⇒ b ∣ a`,
  `ZRowsCoprimeSquares.dvd_of_mul_self_dvd_mul_self`), and the classical Pell existence theorem
  (`ModelPellExistence.exists_pos`) gives `s, g > 0` with `g² = 1 + D τ² s²`.

Then, at every point `x` that takes the canonical values (`Matches`) and `x 10 = s`,
`P = Dt (1 + D Dt s²) = (τ g)²` and `BP = Dm P = (d τ g)²`, so `p0 = d τ g` (`guard`).

`D` depends only on the canonical coordinates: `reg_Budget` gives `Budget` in terms of the
record, and `canonX` is one matching point (the five non-canonical coordinates set to `0`). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.P138Guard
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing ZRowsCoprimeSquares P138Value P138Ports P138Bootstrap P138Canonical

attribute [local irreducible] Source34Ports.betaNat Source34Ports.lowNat Source34Ports.highNat
  Source34Kernel.paramKernel Mixed121Kernel.rho coneA coneB

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Squares modulo sixteen -/

theorem two_mul_ne_two_mul_add_one (a b : DiffRing V) : 2 * a ≠ 2 * b + 1 := by
  intro h
  exact odd_ne_zero' (b - a) (by linear_combination -h)

theorem cancel_const {k a b : DiffRing V} (hk : 0 < k) (h : k * a = k * b) : a = b :=
  mul_left_cancel₀ hk.ne' h

/-- No square is `8` or `12` modulo `16`. -/
theorem not_square_mod_sixteen (t m : DiffRing V) :
    t ^ 2 ≠ 16 * m + 8 ∧ t ^ 2 ≠ 16 * m + 12 := by
  obtain ⟨u, hu | hu⟩ := even_or_odd' t
  · obtain ⟨w, hw | hw⟩ := even_or_odd' u
    · constructor
      · intro h
        rw [hu, hw] at h
        exact two_mul_ne_two_mul_add_one (w ^ 2) m
          (cancel_const (by norm_num : (0 : DiffRing V) < 8) (by linear_combination h))
      · intro h
        rw [hu, hw] at h
        exact two_mul_ne_two_mul_add_one (2 * w ^ 2) (2 * m + 1)
          (cancel_const (by norm_num : (0 : DiffRing V) < 4) (by linear_combination h))
    · constructor
      · intro h
        rw [hu, hw] at h
        exact two_mul_ne_two_mul_add_one (2 * w ^ 2 + 2 * w) (2 * m)
          (cancel_const (by norm_num : (0 : DiffRing V) < 4) (by linear_combination h))
      · intro h
        rw [hu, hw] at h
        exact two_mul_ne_two_mul_add_one (w ^ 2 + w) m
          (cancel_const (by norm_num : (0 : DiffRing V) < 8) (by linear_combination h))
  · constructor
    · intro h
      exact two_mul_ne_two_mul_add_one (8 * m + 4) (2 * u ^ 2 + 2 * u)
        (by rw [hu] at h; linear_combination -h)
    · intro h
      exact two_mul_ne_two_mul_add_one (8 * m + 6) (2 * u ^ 2 + 2 * u)
        (by rw [hu] at h; linear_combination -h)

/-! ## The guard discriminant in record form -/

/-- `Budget` at the canonical point, in the record's terms. -/
def budget (Cn : Canonical V) : DiffRing V :=
  ι Cn.k ^ 2 * (ι Cn.q ^ 2 - ((portsR 4 * ι Cn.F - ι Cn.q) ^ 2 + (portsR 5 * ι Cn.C - ι Cn.q) ^ 2)) -
    4 * ι Cn.q ^ 2 * ι Cn.η ^ 2

theorem reg_Budget (Cn : Canonical V) {x : Fin 11 → DiffRing V} (hx : Matches Cn x) :
    (regs (portsR (V := V)) x).Budget = budget Cn := by
  unfold budget
  rw [Budget_eq, Derr_eq, reg_q Cn hx, reg_k Cn hx, reg_eta Cn hx, reg_F Cn hx, hx.x1]

/-- One point taking the canonical values. -/
def canonX (Cn : Canonical V) : Fin 11 → DiffRing V :=
  ![ι Cn.j, ι Cn.C, ι Cn.z, ι Cn.h, 0, ι Cn.v, ι Cn.w, 0, ι Cn.c, 0, 0]

theorem canonX_matches (Cn : Canonical V) : Matches Cn (canonX Cn) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The guard -/

/-- **C3.** The guard Pell pair: `D = Budget − 4 > 0` is the same at every matching point, and
there are `s, g > 0` with `g² = 1 + D τ² s²`; at a matching point with `x 10 = s`,
`P = (τ g)²` and `BP = (d τ g)²`. -/
theorem guard (Cn : Canonical V) :
    ∃ Dn s g : V, 0 < Dn ∧ 0 < s ∧ 0 < g ∧ g * g = 1 + Dn * Cn.τ * Cn.τ * s * s ∧
      (∀ x : Fin 11 → DiffRing V, Matches Cn x → (regs (portsR (V := V)) x).D4 = ι Dn) ∧
      ∀ x : Fin 11 → DiffRing V, Matches Cn x → x 10 = ι s →
        (regs (portsR (V := V)) x).P = (ι Cn.τ * ι g) ^ 2 ∧
        (regs (portsR (V := V)) x).BP = (ι Cn.d * ι Cn.τ * ι g) ^ 2 := by
  have hm0 := canonX_matches Cn
  obtain ⟨_, h64⟩ := canonical_budget Cn hm0
  obtain ⟨m, hm⟩ := budget_mod (portsR (V := V)) (canonX Cn) portFacts
  rw [reg_Budget Cn hm0] at h64 hm
  -- `D = budget − 4`, a natural number
  obtain ⟨Dn, hDn⟩ := nonneg_iff.mp (show (0 : DiffRing V) ≤ budget Cn - 4 by linarith)
  have hDpos : 0 < Dn := ι_lt_ι.mp (by rw [map_zero, ← hDn]; linarith)
  have hτpos : 0 < Cn.τ := by
    rcases (Arithmetic.zero_le Cn.τ).lt_or_eq with h | h
    · exact h
    · exfalso
      have hn := Cn.τ_norm
      rw [← h, zero_mul] at hn
      exact absurd hn.symm (ne_of_gt (lt_of_lt_of_le _root_.zero_lt_one le_self_add))
  -- `D τ²` is not a square
  have hns : ∀ t : V, t * t ≠ Dn * Cn.τ * Cn.τ := by
    intro t ht
    have hdvd : Cn.τ * Cn.τ ∣ t * t := ⟨Dn, by rw [ht]; ring⟩
    obtain ⟨t', rfl⟩ := dvd_of_mul_self_dvd_mul_self hdvd
    have hsq : t' * t' = Dn := by
      apply ArithmeticBinomLegendre.cancel_left (mul_pos hτpos hτpos)
      calc Cn.τ * Cn.τ * (t' * t') = Cn.τ * t' * (Cn.τ * t') := by ring
        _ = Dn * Cn.τ * Cn.τ := ht
        _ = Cn.τ * Cn.τ * Dn := by ring
    have hsqR : (ι t') ^ 2 = budget Cn - 4 := by rw [hDn, ← hsq, map_mul]; ring
    rcases hm with hm | hm
    · exact (not_square_mod_sixteen (ι t') (m - 1)).2 (by rw [hsqR, hm]; ring)
    · exact (not_square_mod_sixteen (ι t') m).1 (by rw [hsqR, hm]; ring)
  have hd0 : 0 < Dn * Cn.τ * Cn.τ := mul_pos (mul_pos hDpos hτpos) hτpos
  obtain ⟨g, s, hs, hg⟩ := ModelPellExistence.exists_pos (Dn * Cn.τ * Cn.τ) hd0 hns
  have hgpos : 0 < g := by
    rcases (Arithmetic.zero_le g).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, zero_mul] at hg
      exact absurd hg (ne_of_lt (lt_of_lt_of_le _root_.zero_lt_one le_add_self))
  have hD4 : ∀ x : Fin 11 → DiffRing V, Matches Cn x → (regs (portsR (V := V)) x).D4 = ι Dn := by
    intro x hx
    rw [D4_eq, reg_Budget Cn hx, hDn]
  refine ⟨Dn, s, g, hDpos, hs, hgpos, by rw [hg]; ring, hD4, ?_⟩
  intro x hx hs10
  have hP : (regs (portsR (V := V)) x).P = (ι Cn.τ * ι g) ^ 2 := by
    rw [P_eq, reg_Dt Cn hx, hD4 x hx, hs10]
    have hgR := congrArg (ι (V := V)) hg
    simp only [map_add, map_mul, map_one] at hgR
    linear_combination (-(ι Cn.τ * ι Cn.τ)) * hgR
  refine ⟨hP, ?_⟩
  rw [BP_eq, reg_Dm Cn hx, hP]
  ring

#print axioms cancel_const
#print axioms not_square_mod_sixteen
#print axioms reg_Budget
#print axioms canonX_matches
#print axioms guard

end DiophantineConsistency.P138Guard
