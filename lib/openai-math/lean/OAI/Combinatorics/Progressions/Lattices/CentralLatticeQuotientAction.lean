import Mathlib.Basic.Real.Basic
import Mathlib.GroupTheory.GroupAction.Quotient

namespace OAI

section

namespace Erdos3

variable {G : Type*} [Group G]

theorem central_lattice_smul_eq (Γ : Subgroup G) (z : G) (hz : z ∈ Γ)
    (hcentral : ∀ g, z * g = g * z) (x : G ⧸ Γ) : z • x = x := by
  induction x using Quotient.inductionOn' with
  | h g =>
    change (QuotientGroup.mk (z * g) : G ⧸ Γ) = QuotientGroup.mk g
    rw [hcentral g]
    exact QuotientGroup.mk_mul_of_mem g hz

theorem central_lattice_add_smul_eq (Γ : Subgroup G) (c : ℝ → G)
    (hadd : ∀ s t, c (s + t) = c s * c t) (t a : ℝ)
    (ha : c a ∈ Γ) (hcentral : ∀ g, c a * g = g * c a) (x : G ⧸ Γ) :
    c (t + a) • x = c t • x := by
  rw [hadd, mul_smul, central_lattice_smul_eq Γ (c a) ha hcentral]

theorem central_lattice_int_add_smul_eq (Γ : Subgroup G) (c : ℝ → G)
    (hadd : ∀ s t, c (s + t) = c s * c t)
    (hlattice : ∀ n : ℤ, c (n : ℝ) ∈ Γ)
    (hcentral : ∀ (n : ℤ) g, c (n : ℝ) * g = g * c (n : ℝ))
    (t : ℝ) (n : ℤ) (x : G ⧸ Γ) :
    c (t + n) • x = c t • x :=
  central_lattice_add_smul_eq Γ c hadd t n (hlattice n) (hcentral n) x

end Erdos3

end

end OAI
