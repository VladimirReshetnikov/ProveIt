import GowersSzemeredi.Proofs16CellOscillation
import GowersSzemeredi.Proofs16Translations

/-! Translating the variety route to `φ`'s own graph.

Milićević's structure ties the original map `φ` to the structured map `Φ`
only after a shift: `Φ p = φ (p + (s, t))`. `deep_structure_multiplyLinear`
covers `Φ`'s graph. This module transports everything along the shift, so
that the conclusion concerns `φ`'s graph over the (shifted) agreement set.

* `mem_translate_carrier`: membership in a translated box (the box and
  partition API is `Proofs16Translations`).
* `shiftPairs`, `IsEBihomomorphism.shift`: Freiman bihomomorphisms move too.
* `cellGood_translate`, `goodPartitionsExist_shift`: good partitions move.
* `deep_structure_multiplyLinear_phi`: if `Φ` is a Freiman bihomomorphism on
  `V(ρ)` admitting oscillation partitions, then `φ`'s graph over the shifted
  deep agreement set is multiply linear, with one map per cell. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- Membership in a translated box, in subtraction form. -/
theorem mem_translate_carrier {N k : Nat} [NeZero N] (Q : Box N k) (v x : Point N k) :
    x ∈ (Q.translate v).carrier ↔ x - v ∈ Q.carrier := by
  have h := Box.translate_mem_carrier Q v (x - v)
  rwa [sub_add_cancel] at h

/-- The shift of a set of pairs by `(s, t)`. -/
def shiftPairs {N : Nat} (S : Finset (ZMod N × ZMod N)) (s t : ZMod N) :
    Finset (ZMod N × ZMod N) :=
  S.image fun p => (p.1 + s, p.2 + t)

theorem mem_shiftPairs {N : Nat} (S : Finset (ZMod N × ZMod N)) (s t : ZMod N)
    (q : ZMod N × ZMod N) : q ∈ shiftPairs S s t ↔ (q.1 - s, q.2 - t) ∈ S := by
  unfold shiftPairs
  rw [Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    simpa using hp
  · intro h
    exact ⟨_, h, by simp⟩

/-- Freiman bihomomorphisms move along shifts. -/
theorem IsEBihomomorphism.shift {N : Nat} {V : Finset (ZMod N × ZMod N)}
    {Φ : ZMod N × ZMod N → ZMod N} (hΦ : IsEBihomomorphism V Φ {0}) (s t : ZMod N) :
    IsEBihomomorphism (shiftPairs V s t) (fun q => Φ (q.1 - s, q.2 - t)) {0} := by
  constructor
  · intro x₁ x₂ x₃ x₄ y hsum h1 h2 h3 h4
    rw [mem_shiftPairs] at h1 h2 h3 h4
    exact hΦ.1 (x₁ - s) (x₂ - s) (x₃ - s) (x₄ - s) (y - t)
      (by linear_combination hsum) h1 h2 h3 h4
  · intro x y₁ y₂ y₃ y₄ hsum h1 h2 h3 h4
    rw [mem_shiftPairs] at h1 h2 h3 h4
    exact hΦ.2 (x - s) (y₁ - t) (y₂ - t) (y₃ - t) (y₄ - t)
      (by linear_combination hsum) h1 h2 h3 h4

/-- Good cells move along shifts. -/
theorem cellGood_translate {N : Nat} [NeZero N] {S V : Finset (ZMod N × ZMod N)} {Q : Box N 2}
    (h : CellGood S V Q) (s t : ZMod N) :
    CellGood (shiftPairs S s t) (shiftPairs V s t) (Q.translate ![s, t]) := by
  have key : ∀ x : Point N 2, x ∈ (Q.translate ![s, t]).carrier →
      x - ![s, t] ∈ Q.carrier ∧
        ((x - ![s, t]) 0, (x - ![s, t]) 1) = (x 0 - s, x 1 - t) := by
    intro x hx
    exact ⟨(mem_translate_carrier Q _ x).mp hx, by simp⟩
  rcases h with hmiss | hin
  · refine Or.inl fun x hx hS => ?_
    obtain ⟨hxQ, he⟩ := key x hx
    rw [mem_shiftPairs] at hS
    exact hmiss _ hxQ (he ▸ hS)
  · refine Or.inr fun x hx => ?_
    obtain ⟨hxQ, he⟩ := key x hx
    rw [mem_shiftPairs]
    exact he ▸ hin _ hxQ

/-- Good partitions move along shifts. -/
theorem goodPartitionsExist_shift {N : Nat} [NeZero N] {Eb : Real → Real}
    {S V : Finset (ZMod N × ZMod N)} (h : GoodPartitionsExist Eb S V) (s t : ZMod N) :
    GoodPartitionsExist Eb (shiftPairs S s t) (shiftPairs V s t) := by
  intro theta htheta htheta1 P hP
  obtain ⟨M, Q, hpart, hprop, hwid, hgood⟩ :=
    h theta htheta htheta1 (P.translate (-![s, t])) (hP.translate _)
  refine ⟨M, fun j => (Q j).translate ![s, t], ?_, fun j => (hprop j).translate _,
    fun j => ?_, fun j => cellGood_translate (hgood j) s t⟩
  · have hP' := hpart.translate ![s, t]
    rwa [Box.translate_neg'] at hP'
  · simpa using hwid j

/-- **The variety route for `φ`'s own graph.** Let `Φ` be a Freiman
bihomomorphism on `V(ρ)` admitting oscillation partitions. Let `Γ_φ` be part
of `φ`'s graph whose points, shifted back by `(s, t)`, are deep agreement
points (`varietyAgreement` at radius `ρ/2`). Then `Γ_φ` is multiply linear
with one map per cell. The oscillation partitions are those of the unshifted
variety; `goodPartitionsExist_shift` moves them. -/
theorem deep_structure_multiplyLinear_phi {N : Nat} [NeZero N] [Fact N.Prime]
    {Γ Ψ : Finset (ZMod N)} {r : Nat} {L : Fin r → ZMod N → ZMod N} {ρ : Real}
    {A : Finset (ZMod N × ZMod N)} {φ Φ : ZMod N × ZMod N → ZMod N} {s t : ZMod N}
    (hΦ : IsEBihomomorphism (bilinearBohrVariety Γ Ψ L ρ) Φ {0})
    {Gamma : Finset (Point N 2 × ZMod N)}
    (hΓ : ∀ p ∈ Gamma, (p.1 0 - s, p.1 1 - t) ∈ varietyAgreement Γ Ψ L (ρ / 2) A φ Φ s t ∧
      p.2 = φ (p.1 0, p.1 1))
    (Qb Eb : Real → Real) (hQb : ∀ theta : Real, 0 < theta → theta ≤ 1 → 1 ≤ Qb theta)
    (hosc : OscillationPartitionsExist Eb Γ Ψ L ρ) :
    MultiplyLinearWith Qb Eb Gamma := by
  have hgraph : IsGraphOver Gamma (shiftPairs (bilinearBohrVariety Γ Ψ L (ρ / 2)) s t)
      (fun q => Φ (q.1 - s, q.2 - t)) := by
    intro p hp
    obtain ⟨hag, hval⟩ := hΓ p hp
    unfold varietyAgreement at hag
    obtain ⟨hV, _, hΦφ⟩ := Finset.mem_filter.mp hag
    refine ⟨(mem_shiftPairs _ s t _).mpr hV, ?_⟩
    simp only [sub_add_cancel] at hΦφ
    rw [hval]
    exact hΦφ.symm
  exact multiplyLinearWith_of_good_partitions (hΦ.shift s t) hgraph Qb Eb hQb
    (goodPartitionsExist_shift (goodPartitionsExist_of_oscillation hosc) s t)

end LeanProofs.GowersSzemeredi
