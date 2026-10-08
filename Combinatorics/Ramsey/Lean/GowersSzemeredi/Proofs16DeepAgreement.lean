import GowersSzemeredi.Proofs16VarietyRegularStep

/-! Agreement at depth: the form of Milićević's structure the packing uses.

`MilicevicVarietyStructure` (research notes J.2) places its agreement points
`Φ p = φ(p + (s,t))` somewhere in `V(ρ)`. The packing in J.2 covers only a
regular sub-variety `V(ρ_j)`, with `ρ/2 ≤ ρ_j ≤ ρ`
(`variety_exists_regular_step`). Agreement points near the boundary of
`V(ρ)` may miss `V(ρ_j)` entirely, and averaging cannot move them there.

Source check (arXiv:2601.01682). Proposition 11.1 and Section 13 never relate
the structured map pointwise to `φ`. Instead, *each* point `(x,y)` of the
structured domain satisfies an arrangement identity: a positive proportion
of `(d₁,…,d_k)`-arrangements of lengths `(x,y)`, all inside the variety, have
a signed sum of `φ`-values equal to the structured value. Pointwise agreement
`Φ(x,y) = φ(x+s,y+t)` then comes from averaging over `(x,y)`, plus Theorem
2.26. Because the identity holds at every point, the average can be taken
over any sub-domain of comparable size, for instance `V(ρ/2)`. The loss is the
size ratio `|V(ρ)|/|V(ρ/2)| ≤ M^dim` (`variety_card_lower`), which the
quasi-polynomial bound absorbs.

Caveat: Theorem 2.26 linearizes the remaining terms on a coset progression,
which can shrink the domain once more. The paper states the result only after
extension, on `B₁ × B₂`. So the deep form below is our reformulation, not a
quoted theorem; like the shallow form, it is a hypothesis.

The paper's varieties also transpose ours: `x` lies in a coset progression
`C`, and the `y`-conditions depend on `x`. Swapping coordinates matches them.

* `MilicevicDeepVarietyStructure D`: `Φ` is a Freiman bihomomorphism on
  `V(ρ)`, with agreement points counted in `V(ρ/2)`.
* `MilicevicDeepVarietyStructure.toShallow`: it implies the shallow form.
* `deep_agreement_in_intermediate`: agreement points lie in every `V(ρ')`
  with `ρ/2 ≤ ρ'`.
* `deep_regular_step`: a regular step `j` whose two radii both carry the
  agreement mass. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- The agreement set of `Φ` with the shifted `φ` inside a variety. -/
def varietyAgreement {N : Nat} [NeZero N] (Γ Ψ : Finset (ZMod N)) {r : Nat}
    (L : Fin r → ZMod N → ZMod N) (ρ : Real) (A : Finset (ZMod N × ZMod N))
    (φ Φ : ZMod N × ZMod N → ZMod N) (s t : ZMod N) : Finset (ZMod N × ZMod N) :=
  (bilinearBohrVariety Γ Ψ L ρ).filter fun p =>
    (p.1 + s, p.2 + t) ∈ A ∧ Φ p = φ (p.1 + s, p.2 + t)

/-- **Milićević's structure, deep-agreement form.** As
`MilicevicVarietyStructure`, except that the agreement points are counted in
the half-radius variety `V(ρ/2)`. Stated as a hypothesis; not asserted. -/
def MilicevicDeepVarietyStructure (D : Nat) : Prop :=
  ∀ (N : Nat) [NeZero N] (A : Finset (ZMod N × ZMod N))
    (φ : ZMod N × ZMod N → ZMod N) (c : Real),
    0 < c → c * (N : Real) ^ 2 ≤ A.card → IsEBihomomorphism A φ {0} →
    ∃ (Γ Ψ : Finset (ZMod N)) (r : Nat) (L : Fin r → ZMod N → ZMod N) (ρ : Real)
      (s t : ZMod N) (Φ : ZMod N × ZMod N → ZMod N),
      (Γ.card : Real) ≤ milicevicBound D c ∧ (Ψ.card : Real) ≤ milicevicBound D c ∧
      (r : Real) ≤ milicevicBound D c ∧ Real.exp (-milicevicBound D c) ≤ ρ ∧
      (∀ i, IsFreimanLinearOn (bohr Ψ ρ) (L i)) ∧
      IsEBihomomorphism (bilinearBohrVariety Γ Ψ L ρ) Φ {0} ∧
      Real.exp (-milicevicBound D c) * (N : Real) ^ 2 ≤
        ((varietyAgreement Γ Ψ L (ρ / 2) A φ Φ s t).card : Real)

/-- Agreement sets grow with the radius. -/
theorem varietyAgreement_mono {N : Nat} [NeZero N] (Γ Ψ : Finset (ZMod N)) {r : Nat}
    (L : Fin r → ZMod N → ZMod N) {ρ ρ' : Real} (h : ρ' ≤ ρ) (A : Finset (ZMod N × ZMod N))
    (φ Φ : ZMod N × ZMod N → ZMod N) (s t : ZMod N) :
    varietyAgreement Γ Ψ L ρ' A φ Φ s t ⊆ varietyAgreement Γ Ψ L ρ A φ Φ s t :=
  Finset.filter_subset_filter _ (bilinearBohrVariety_mono Γ Ψ L h)

/-- The deep form implies the shallow form. -/
theorem MilicevicDeepVarietyStructure.toShallow {D : Nat}
    (h : MilicevicDeepVarietyStructure D) : MilicevicVarietyStructure D := by
  intro N _ A φ c hc hA hφ
  obtain ⟨Γ, Ψ, r, L, ρ, s, t, Φ, hΓ, hΨ, hr, hρ, hL, hΦ, hagree⟩ := h N A φ c hc hA hφ
  have hρpos : 0 < ρ := (Real.exp_pos _).trans_le hρ
  refine ⟨Γ, Ψ, r, L, ρ, s, t, Φ, hΓ, hΨ, hr, hρ, hL, hΦ, hagree.trans ?_⟩
  exact_mod_cast Finset.card_le_card
    (varietyAgreement_mono Γ Ψ L (by linarith : ρ / 2 ≤ ρ) A φ Φ s t)

/-- Deep agreement points lie in every intermediate variety. -/
theorem deep_agreement_in_intermediate {N : Nat} [NeZero N] (Γ Ψ : Finset (ZMod N)) {r : Nat}
    (L : Fin r → ZMod N → ZMod N) {ρ ρ' : Real} (h : ρ / 2 ≤ ρ') (A : Finset (ZMod N × ZMod N))
    (φ Φ : ZMod N × ZMod N → ZMod N) (s t : ZMod N) {a : Real}
    (ha : a ≤ ((varietyAgreement Γ Ψ L (ρ / 2) A φ Φ s t).card : Real)) :
    a ≤ ((varietyAgreement Γ Ψ L ρ' A φ Φ s t).card : Real) :=
  ha.trans (by exact_mod_cast Finset.card_le_card (varietyAgreement_mono Γ Ψ L h A φ Φ s t))

/-- The regular-step radii stay above `ρ/2`. -/
theorem regular_radius_ge_half {ρ : Real} (hρ : 0 ≤ ρ) {m j : Nat} (hm : 0 < m) (hj : j ≤ m) :
    ρ / 2 ≤ ρ * (1 - (j : Real) / (2 * m)) := by
  have hmR : (0 : Real) < m := by exact_mod_cast hm
  have hjm : (j : Real) ≤ m := by exact_mod_cast hj
  have hfrac : (j : Real) / (2 * m) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  nlinarith

/-- **A regular step carrying the agreement mass.** Given deep agreement of
size `a`, some step `j < m` has a ratio bound `|V(ρ_j)| ≤ C |V(ρ_{j+1})|`,
and both `V(ρ_j)` and `V(ρ_{j+1})` contain at least `a` agreement points. -/
theorem deep_regular_step {N : Nat} [NeZero N] (Γ Ψ : Finset (ZMod N)) {r : Nat}
    (L : Fin r → ZMod N → ZMod N) {ρ : Real} (hρ : 0 < ρ) (M : Nat) [NeZero M]
    (hM : 1 ≤ ρ / 2 * M) (m : Nat) (hm : 0 < m) (A : Finset (ZMod N × ZMod N))
    (φ Φ : ZMod N × ZMod N → ZMod N) (s t : ZMod N) {a : Real}
    (ha : a ≤ ((varietyAgreement Γ Ψ L (ρ / 2) A φ Φ s t).card : Real)) :
    ∃ j, j < m ∧
      ((bilinearBohrVariety Γ Ψ L (ρ * (1 - j / (2 * m)))).card : Real) ≤
        ((M : Real) ^ (Ψ.card + (Γ.card + r))) ^ ((1 : Real) / m) *
          (bilinearBohrVariety Γ Ψ L (ρ * (1 - (j + 1 : Nat) / (2 * m)))).card ∧
      a ≤ ((varietyAgreement Γ Ψ L (ρ * (1 - j / (2 * m))) A φ Φ s t).card : Real) ∧
      a ≤ ((varietyAgreement Γ Ψ L (ρ * (1 - (j + 1 : Nat) / (2 * m))) A φ Φ s t).card : Real) := by
  obtain ⟨j, hj, hratio⟩ := variety_exists_regular_step Γ Ψ L hρ M hM m hm
  refine ⟨j, hj, hratio, ?_, ?_⟩
  · exact deep_agreement_in_intermediate Γ Ψ L
      (regular_radius_ge_half hρ.le hm hj.le) A φ Φ s t ha
  · exact deep_agreement_in_intermediate Γ Ψ L
      (regular_radius_ge_half hρ.le hm (Nat.succ_le_of_lt hj)) A φ Φ s t ha

end LeanProofs.GowersSzemeredi
