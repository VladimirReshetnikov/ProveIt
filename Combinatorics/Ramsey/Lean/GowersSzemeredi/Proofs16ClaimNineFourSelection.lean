import GowersSzemeredi.Proofs16SelectionAveraging
import GowersSzemeredi.Proofs16IndependenceCount

/-! The selection step of Milićević's Claim 9.4 (arXiv:2601.01682, printed
p. 66), derandomized.

Milićević chooses, for each index `z` and each of four maps `ψ₁, …, ψ₄`, a
random combination `ψ_i(z) ∈ ⟨Γ_z⟩_R`. A prescribed decomposition
`(ξ₁, ξ₂, ξ₃, ξ₄)` of an escaping frequency is realized at `(x + a, x, y + a, y)`
with probability at least `(2R+1)^(−4d)`. The four maps are independent, so
the four points `(i, z)` are distinct even when `x + a, x, y + a, y` are not.
* `exists_good_selection_indexed`: `exists_good_selection` counted over an
  index family. Distinct indices may share a requirement.
* `claim_9_4_selection`: there are maps `ψ : Fin 4 → G → G` with
  `ψ i z ∈ spanBall (Γ z) R` that realize the prescribed decomposition at
  `(x + a, x, y + a, y)` for at least `(2R+1)^(−4d)` of the triples. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

section
variable {X Y : Type} [Fintype X] [DecidableEq X] [DecidableEq Y]

/-- **Selection averaging over an index family.** -/
theorem exists_good_selection_indexed (U : X → Finset Y) (hne : ∀ x, (U x).Nonempty) {K : Nat}
    (hK1 : 1 ≤ K) (hK : ∀ x, (U x).card ≤ K) {ι : Type*} (Tr : Finset ι)
    (req : ι → Finset X × (X → Y))
    (hT : ∀ t ∈ Tr, (req t).1.card ≤ 4 ∧ ∀ x ∈ (req t).1, (req t).2 x ∈ U x) :
    ∃ f ∈ Fintype.piFinset U, Tr.card ≤ K ^ 4 * (Tr.filter fun t => Meets f (req t)).card := by
  set F := Fintype.piFinset U
  have hFpos : 0 < F.card := by
    rw [Fintype.card_piFinset]
    exact Finset.prod_pos fun x _ => (hne x).card_pos
  have hreq : ∀ t ∈ Tr, F.card ≤ K ^ 4 * (F.filter fun f => Meets f (req t)).card := by
    intro t ht
    obtain ⟨hS, hv⟩ := hT t ht
    calc F.card ≤ K ^ (req t).1.card * (F.filter fun f => Meets f (req t)).card :=
          card_all_le_mul_meeting U hK (req t) hv
      _ ≤ K ^ 4 * (F.filter fun f => Meets f (req t)).card :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hK1 hS)
  have hdouble : ∑ f ∈ F, (Tr.filter fun t => Meets f (req t)).card =
      ∑ t ∈ Tr, (F.filter fun f => Meets f (req t)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  by_contra hcon
  push Not at hcon
  have hlt : K ^ 4 * ∑ f ∈ F, (Tr.filter fun t => Meets f (req t)).card < F.card * Tr.card := by
    rw [Finset.mul_sum]
    calc ∑ f ∈ F, K ^ 4 * (Tr.filter fun t => Meets f (req t)).card
        < ∑ _f ∈ F, Tr.card := Finset.sum_lt_sum_of_nonempty (Finset.card_pos.mp hFpos)
          fun f hf => hcon f hf
      _ = F.card * Tr.card := by rw [Finset.sum_const, smul_eq_mul]
  have hge : F.card * Tr.card ≤ K ^ 4 * ∑ t ∈ Tr, (F.filter fun f => Meets f (req t)).card := by
    rw [Finset.mul_sum]
    calc F.card * Tr.card = ∑ _t ∈ Tr, F.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ t ∈ Tr, K ^ 4 * (F.filter fun f => Meets f (req t)).card := Finset.sum_le_sum hreq
  rw [hdouble] at hlt
  omega

end

theorem zero_mem_spanBall {G : Type*} [AddCommGroup G] (Γ : Finset G) (R : Nat) :
    (0 : G) ∈ spanBall Γ R := by
  refine Finset.mem_image.mpr ⟨fun _ => 0, ?_, by simp⟩
  rw [Fintype.mem_piFinset]
  intro γ
  simp

/-- **The selection step of Claim 9.4.** -/
theorem claim_9_4_selection {N : Nat} [NeZero N] (Γ : ZMod N → Finset (ZMod N)) {d R : Nat}
    (hΓ : ∀ z, (Γ z).card ≤ d) (Tr : Finset (ZMod N × ZMod N × ZMod N))
    (ξ : ZMod N × ZMod N × ZMod N → Fin 4 → ZMod N)
    (hξ : ∀ t ∈ Tr, ξ t 0 ∈ spanBall (Γ (t.1 + t.2.2)) R ∧ ξ t 1 ∈ spanBall (Γ t.1) R ∧
      ξ t 2 ∈ spanBall (Γ (t.2.1 + t.2.2)) R ∧ ξ t 3 ∈ spanBall (Γ t.2.1) R) :
    ∃ ψ : Fin 4 → ZMod N → ZMod N, (∀ i z, ψ i z ∈ spanBall (Γ z) R) ∧
      Tr.card ≤ ((2 * R + 1) ^ d) ^ 4 * (Tr.filter fun t =>
        ψ 0 (t.1 + t.2.2) = ξ t 0 ∧ ψ 1 t.1 = ξ t 1 ∧
        ψ 2 (t.2.1 + t.2.2) = ξ t 2 ∧ ψ 3 t.2.1 = ξ t 3).card := by
  let U : Fin 4 × ZMod N → Finset (ZMod N) := fun p => spanBall (Γ p.2) R
  have hne : ∀ p, (U p).Nonempty := fun p => ⟨0, zero_mem_spanBall _ _⟩
  have hK : ∀ p, (U p).card ≤ (2 * R + 1) ^ d := fun p =>
    (spanBall_card_le _ _).trans (Nat.pow_le_pow_right (by omega) (hΓ p.2))
  let req : ZMod N × ZMod N × ZMod N → Finset (Fin 4 × ZMod N) × (Fin 4 × ZMod N → ZMod N) :=
    fun t => ({(0, t.1 + t.2.2), (1, t.1), (2, t.2.1 + t.2.2), (3, t.2.1)}, fun p => ξ t p.1)
  have hT : ∀ t ∈ Tr, (req t).1.card ≤ 4 ∧ ∀ p ∈ (req t).1, (req t).2 p ∈ U p := by
    intro t ht
    obtain ⟨h0, h1, h2, h3⟩ := hξ t ht
    refine ⟨?_, ?_⟩
    · calc (req t).1.card ≤ 1 + (({(1, t.1), (2, t.2.1 + t.2.2), (3, t.2.1)} :
            Finset (Fin 4 × ZMod N))).card := Finset.card_insert_le _ _
        _ ≤ 1 + (1 + (({(2, t.2.1 + t.2.2), (3, t.2.1)} : Finset (Fin 4 × ZMod N))).card) := by
            gcongr; exact Finset.card_insert_le _ _
        _ ≤ 4 := by
            have := Finset.card_le_two (a := ((2 : Fin 4), t.2.1 + t.2.2)) (b := ((3 : Fin 4), t.2.1))
            omega
    · intro p hp
      simp only [req, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
      · exact h3
  obtain ⟨f, hfmem, hf⟩ := exists_good_selection_indexed U hne (Nat.one_le_pow _ _ (by omega)) hK Tr req hT
  refine ⟨fun i z => f (i, z), fun i z => Fintype.mem_piFinset.mp hfmem (i, z), ?_⟩
  · refine hf.trans (Nat.mul_le_mul_left _ (Finset.card_le_card ?_))
    intro t ht
    obtain ⟨htT, hm⟩ := Finset.mem_filter.mp ht
    refine Finset.mem_filter.mpr ⟨htT, ?_, ?_, ?_, ?_⟩ <;>
      exact hm _ (by simp [req])

end LeanProofs.GowersSzemeredi
