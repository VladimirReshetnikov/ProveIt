import GowersSzemeredi.Proofs16GoodPartition
import GowersSzemeredi.Proofs16DeepAgreement

/-! Small oscillation makes cells good.

A variety `V(σ)` is cut out by the conditions `|γ x| ≤ σN` (`γ ∈ Γ`),
`|ψ y| ≤ σN` (`ψ ∈ Ψ`) and `|L_k(y) x| ≤ σN`. If every condition oscillates
by at most `εN` over a set `C` that meets `V(σ)`, then `C ⊆ V(σ + ε)`, by the
triangle inequality for centered values.

With `σ = ρ/2` and `ε = ρ/2`: a cell that meets `V(ρ/2)` and oscillates by
at most `ρN/2` is good for `(V(ρ/2), V(ρ))`. Cells that miss `V(ρ/2)` are
good with no condition. So `GoodPartitionsExist` reduces to
`OscillationPartitionsExist`: partitions whose cells either miss `V(ρ/2)`
or have small oscillation.

This is the (D)-type statement left on the variety route, and it is stated
as a hypothesis. Only cells meeting `V(ρ/2)` need control. On such a cell, every
`y` lies in `B(Ψ;ρ)` (oscillation `ρN/2` on top of `ρN/2`), which is where the
`L_k` are Freiman-linear. Two caveats remain:
* `Box` has one common difference for both axes, so a single step must make
  `L_k(y)·d`, `Δ_k(e)·x` and `γ d`, `ψ d` small at the same time;
* the graph obtained is `Φ`'s. `φ`'s agreement graph is its translate by
  `(s, t)`, and translating the partition is not done here.

* `mem_bilinearBohrVariety_iff`: the three conditions.
* `subset_variety_of_small_oscillation`.
* `cellGood_of_small_oscillation`, `goodPartitionsExist_of_oscillation`.
* `deep_structure_multiplyLinear`: deep agreement plus oscillation
  partitions give `MultiplyLinearWith` for `Φ`'s graph over the half-radius
  variety, with one map per cell. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- The three families of variety conditions. -/
theorem mem_bilinearBohrVariety_iff {N : Nat} [NeZero N] (Γ Ψ : Finset (ZMod N)) {r : Nat}
    (L : Fin r → ZMod N → ZMod N) (σ : Real) (p : ZMod N × ZMod N) :
    p ∈ bilinearBohrVariety Γ Ψ L σ ↔
      (∀ γ ∈ Γ, (centeredAbs (γ * p.1) : Real) ≤ σ * N) ∧
      (∀ ψ ∈ Ψ, (centeredAbs (ψ * p.2) : Real) ≤ σ * N) ∧
      ∀ k, (centeredAbs (L k p.2 * p.1) : Real) ≤ σ * N := by
  unfold bilinearBohrVariety bohr
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
    Finset.mem_image, forall_exists_index, forall_apply_eq_imp_iff]
  tauto

/-- Oscillation of the variety conditions over a set, at most `εN`. -/
def SmallOscillation {N : Nat} [NeZero N] (Γ Ψ : Finset (ZMod N)) {r : Nat}
    (L : Fin r → ZMod N → ZMod N) (ε : Real) (C : Finset (ZMod N × ZMod N)) : Prop :=
  ∀ p ∈ C, ∀ q ∈ C,
    (∀ γ ∈ Γ, (centeredAbs (γ * q.1 - γ * p.1) : Real) ≤ ε * N) ∧
    (∀ ψ ∈ Ψ, (centeredAbs (ψ * q.2 - ψ * p.2) : Real) ≤ ε * N) ∧
    ∀ k, (centeredAbs (L k q.2 * q.1 - L k p.2 * p.1) : Real) ≤ ε * N

/-- One step of the triangle inequality for centered values. -/
theorem centeredAbs_le_of_close {N : Nat} {u v : ZMod N} {a b : Real}
    (hu : (centeredAbs u : Real) ≤ a) (hvu : (centeredAbs (v - u) : Real) ≤ b) :
    (centeredAbs v : Real) ≤ a + b := by
  have h := centeredAbs_add_le u (v - u)
  rw [add_sub_cancel] at h
  have h' : (centeredAbs v : Real) ≤ centeredAbs u + centeredAbs (v - u) := by exact_mod_cast h
  linarith

/-- **A set of small oscillation meeting `V(σ)` lies in `V(σ + ε)`.** -/
theorem subset_variety_of_small_oscillation {N : Nat} [NeZero N] {Γ Ψ : Finset (ZMod N)} {r : Nat}
    {L : Fin r → ZMod N → ZMod N} {σ ε : Real} {C : Finset (ZMod N × ZMod N)}
    (hosc : SmallOscillation Γ Ψ L ε C) {p : ZMod N × ZMod N} (hpC : p ∈ C)
    (hpV : p ∈ bilinearBohrVariety Γ Ψ L σ) :
    ∀ q ∈ C, q ∈ bilinearBohrVariety Γ Ψ L (σ + ε) := by
  intro q hqC
  obtain ⟨hΓp, hΨp, hLp⟩ := (mem_bilinearBohrVariety_iff Γ Ψ L σ p).mp hpV
  obtain ⟨hΓo, hΨo, hLo⟩ := hosc p hpC q hqC
  rw [mem_bilinearBohrVariety_iff, add_mul]
  exact ⟨fun γ hγ => centeredAbs_le_of_close (hΓp γ hγ) (hΓo γ hγ),
    fun ψ hψ => centeredAbs_le_of_close (hΨp ψ hψ) (hΨo ψ hψ),
    fun k => centeredAbs_le_of_close (hLp k) (hLo k)⟩

/-- The cell's points as pairs. -/
def cellPairs {N : Nat} [NeZero N] (Q : Box N 2) : Finset (ZMod N × ZMod N) :=
  Q.carrier.image fun x => (x 0, x 1)

/-- **Small oscillation makes a cell good.** -/
theorem cellGood_of_small_oscillation {N : Nat} [NeZero N] {Γ Ψ : Finset (ZMod N)} {r : Nat}
    {L : Fin r → ZMod N → ZMod N} {ρ : Real} (Q : Box N 2)
    (h : (∀ x ∈ Q.carrier, (x 0, x 1) ∉ bilinearBohrVariety Γ Ψ L (ρ / 2)) ∨
      SmallOscillation Γ Ψ L (ρ / 2) (cellPairs Q)) :
    CellGood (bilinearBohrVariety Γ Ψ L (ρ / 2)) (bilinearBohrVariety Γ Ψ L ρ) Q := by
  rcases h with hmiss | hosc
  · exact Or.inl hmiss
  · by_cases hmeet : ∃ x ∈ Q.carrier, (x 0, x 1) ∈ bilinearBohrVariety Γ Ψ L (ρ / 2)
    · obtain ⟨x₀, hx₀, hx₀V⟩ := hmeet
      have hsub := subset_variety_of_small_oscillation hosc
        (Finset.mem_image_of_mem _ hx₀) hx₀V
      refine Or.inr fun x hx => ?_
      have := hsub (x 0, x 1) (Finset.mem_image_of_mem _ hx)
      rwa [add_halves] at this
    · simp only [not_exists, not_and] at hmeet
      exact Or.inl hmeet

/-- Partitions whose cells miss `V(ρ/2)` or oscillate by at most `ρN/2`.
The remaining (D)-type input of the variety route; not asserted. -/
def OscillationPartitionsExist {N : Nat} [NeZero N] (Eb : Real → Real)
    (Γ Ψ : Finset (ZMod N)) {r : Nat} (L : Fin r → ZMod N → ZMod N) (ρ : Real) : Prop :=
  ∀ theta : Real, 0 < theta → theta ≤ 1 → ∀ P : Box N 2, P.IsProper →
    ∃ M : Nat, ∃ Q : Fin M → Box N 2,
      IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
      (∀ j, (P.width : Real) ^ (Eb theta) ≤ (Q j).width) ∧
      ∀ j, (∀ x ∈ (Q j).carrier, (x 0, x 1) ∉ bilinearBohrVariety Γ Ψ L (ρ / 2)) ∨
        SmallOscillation Γ Ψ L (ρ / 2) (cellPairs (Q j))

theorem goodPartitionsExist_of_oscillation {N : Nat} [NeZero N] {Eb : Real → Real}
    {Γ Ψ : Finset (ZMod N)} {r : Nat} {L : Fin r → ZMod N → ZMod N} {ρ : Real}
    (h : OscillationPartitionsExist Eb Γ Ψ L ρ) :
    GoodPartitionsExist Eb (bilinearBohrVariety Γ Ψ L (ρ / 2)) (bilinearBohrVariety Γ Ψ L ρ) := by
  intro theta htheta htheta1 P hP
  obtain ⟨M, Q, hpart, hprop, hwid, hcell⟩ := h theta htheta htheta1 P hP
  exact ⟨M, Q, hpart, hprop, hwid, fun j => cellGood_of_small_oscillation (Q j) (hcell j)⟩

/-- **The variety route, assembled.** A Freiman bihomomorphism `Φ` on `V(ρ)`
whose variety admits oscillation partitions is multiply linear, with one map
per cell, on its graph over `V(ρ/2)`. The deep agreement points of
`MilicevicDeepVarietyStructure` lie in `V(ρ/2)`, so this graph contains
the agreement part of `φ`'s graph, up to the shift `(s, t)`. -/
theorem deep_structure_multiplyLinear {N : Nat} [NeZero N] [Fact N.Prime]
    {Γ Ψ : Finset (ZMod N)} {r : Nat} {L : Fin r → ZMod N → ZMod N} {ρ : Real}
    {Φ : ZMod N × ZMod N → ZMod N}
    (hΦ : IsEBihomomorphism (bilinearBohrVariety Γ Ψ L ρ) Φ {0})
    {Gamma : Finset (Point N 2 × ZMod N)}
    (hΓ : IsGraphOver Gamma (bilinearBohrVariety Γ Ψ L (ρ / 2)) Φ) (Qb Eb : Real → Real)
    (hQb : ∀ theta : Real, 0 < theta → theta ≤ 1 → 1 ≤ Qb theta)
    (hosc : OscillationPartitionsExist Eb Γ Ψ L ρ) :
    MultiplyLinearWith Qb Eb Gamma :=
  multiplyLinearWith_of_good_partitions hΦ hΓ Qb Eb hQb (goodPartitionsExist_of_oscillation hosc)

end LeanProofs.GowersSzemeredi
