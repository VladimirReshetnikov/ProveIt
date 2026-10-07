import OAI.Combinatorics.Progressions.Estimates.LocalMomentScale

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]

theorem exists_translated_local_average
    (S T : Finset G) (hS : S.Nonempty) (hT : T.Nonempty) (f : G → ℝ)
    {M eta : ℝ} (hM : 0 ≤ M) (hf : ∀ x, |f x| ≤ M)
    (hTV : ∀ t ∈ T, (∑ x, |realUniformMass S (x - t) - realUniformMass S x|) ≤ eta) :
    ∃ b ∈ S, (𝔼 a ∈ S, 𝔼 x ∈ S, f (a - x)) - M * eta ≤
      𝔼 a ∈ S, 𝔼 t ∈ T, f (a - (b + t)) := by
  have hsingle (a t : G) (ht : t ∈ T) :
      (𝔼 b ∈ S, f (a - b)) - M * eta ≤ 𝔼 b ∈ S, f (a - (b + t)) := by
    have h := (abs_expect_add_sub_le S (fun b => f (a - b)) t
      (fun b => hf (a - b))).trans (mul_le_mul_of_nonneg_left (hTV t ht) hM)
    have hlower := (abs_le.mp h).1
    linarith
  have hlocal (t : G) (ht : t ∈ T) :
      (𝔼 a ∈ S, 𝔼 b ∈ S, f (a - b)) - M * eta ≤
        𝔼 a ∈ S, 𝔼 b ∈ S, f (a - (b + t)) := by
    have h := Finset.expect_le_expect (fun a (_ : a ∈ S) => hsingle a t ht)
    simpa only [Finset.expect_sub_distrib, Finset.expect_const hS] using h
  have hglobal := Finset.expect_le_expect hlocal
  rw [Finset.expect_const hT] at hglobal
  have hreorder : (𝔼 t ∈ T, 𝔼 a ∈ S, 𝔼 b ∈ S, f (a - (b + t))) =
      𝔼 b ∈ S, 𝔼 a ∈ S, 𝔼 t ∈ T, f (a - (b + t)) := by
    calc
      _ = 𝔼 a ∈ S, 𝔼 b ∈ S, 𝔼 t ∈ T, f (a - (b + t)) := by
        rw [Finset.expect_comm T S]
        apply Finset.expect_congr rfl
        intro a _
        exact Finset.expect_comm T S _
      _ = _ := Finset.expect_comm S S _
  exact Finset.exists_le_of_le_expect hS (hglobal.trans_eq hreorder)

end Erdos3

end

end OAI
