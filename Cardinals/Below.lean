/-
  A STRONGLY COMPACT CARDINAL BELOW `lam` (synthesis §6).

  * `separation` (Theorem 6.1): the small witness to non-stabilization of the
    `HCD` hierarchy, with its three refinements.
  * `P1 … P7` and `conditional_inconsistency` (Corollary 6.2), including the
    implications between the principles and the equivalence `P2 ↔ P3`-style
    remark (here: all size conventions are ambient, see `Basic.ShortCofinal`).
  * `no_CEx_above_extendible` (Corollary 6.3): the Blue–Goldberg exclusion,
    re-derived rather than admitted.

  The proofs use only the admitted published results of `Cardinals.Published`.
-/
import Cardinals.Barrier

universe u

namespace Cardinals

open ZFSet Ordinal Cardinal

/-- The range of an `ω`-sequence of ordinals, as a set. -/
noncomputable def seqSet (s : ℕ → Ordinal.{u}) : ZFSet.{u} :=
  ZFSet.range (fun n : ULift.{u} ℕ => ordZ (s n.down))

theorem mem_seqSet {s : ℕ → Ordinal.{u}} {x : ZFSet.{u}} :
    x ∈ seqSet s ↔ ∃ n, ordZ (s n) = x := by
  unfold seqSet
  rw [ZFSet.mem_range]
  exact ⟨fun ⟨n, hn⟩ => ⟨n.down, hn⟩, fun ⟨n, hn⟩ => ⟨⟨n⟩, hn⟩⟩

theorem card_seqSet_le (s : ℕ → Ordinal.{u}) : ZFSet.card (seqSet s) ≤ ℵ₀ := by
  have h := ZFSet.lift_card_range_le (f := fun n : ULift.{u} ℕ => ordZ (s n.down))
  simpa [seqSet] using h

theorem cofinalIn_seqSet {s : ℕ → Ordinal.{u}} {lam : Ordinal.{u}}
    (hlt : ∀ n, s n < lam) (hcof : ∀ ξ < lam, ∃ n, ξ ≤ s n) : CofinalIn (seqSet s) lam := by
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨n, rfl⟩ := mem_seqSet.mp hx
    exact ⟨s n, hlt n, rfl⟩
  · intro ξ hξ
    obtain ⟨n, hn⟩ := hcof ξ hξ
    exact ⟨s n, hn, hlt n, mem_seqSet.mpr ⟨n, rfl⟩⟩

/-- Under cover exactingness there is a countable cofinal subset of `lam` in `V`. -/
theorem exists_countable_cofinal (c γ : Cardinal.{u}) (hc : ℵ₀ ≤ c) (h : CEx γ c.ord) :
    ∃ a : ZFSet.{u}, CofinalIn a c.ord ∧ ZFSet.card a ≤ ℵ₀ := by
  obtain ⟨s, -, hlt, hcof⟩ := cof_omega c γ hc h
  exact ⟨seqSet s, cofinalIn_seqSet hlt hcof, card_seqSet_le s⟩

/-- **Small-witness separation (synthesis Theorem 6.1).**  Suppose `δ < c ≤ γ`,
`δ` is strongly compact and `c.ord` is `γ`-cover exacting.  Then there is a cofinal
`a ⊆ c.ord` with `a ∈ HCD(δ)`, `|a| < δ`, and `a ∉ CD(η)` for every `η > γ`. -/
theorem separation (δ c γ : Cardinal.{u}) (hc : ℵ₀ ≤ c) (hδ : SC δ) (hδc : δ < c)
    (h : CEx γ c.ord) :
    ∃ a : ZFSet.{u}, HCD δ a ∧ CofinalIn a c.ord ∧ ZFSet.card a < δ ∧
      ∀ η, γ < η → ¬ CD η a := by
  obtain ⟨a₀, ha₀, ha₀card⟩ := exists_countable_cofinal c γ hc h
  have hδinf : ℵ₀ ≤ δ := hδ.1.le
  obtain ⟨b, hbN, hab, hbcard⟩ :=
    Published.HCD_cover δ hδ c.ord a₀ ha₀.1 (lt_of_le_of_lt ha₀card hδ.1)
  have hN := Published.HCD_isInnerModelZF δ hδinf
  refine ⟨b ∩ ordZ c.ord, hN.inter_ord hbN c.ord, ⟨?_, ?_⟩, ?_, ?_⟩
  · exact subOrd_iff_subset.mpr (fun x hx => (mem_inter.mp hx).2)
  · intro ξ hξ
    obtain ⟨η, hξη, hη, hmem⟩ := ha₀.2 ξ hξ
    exact ⟨η, hξη, hη, mem_inter.mpr ⟨hab hmem, Ordinal.toZFSet_mem_toZFSet_iff.mpr hη⟩⟩
  · exact lt_of_le_of_lt (card_mono (fun x hx => (mem_inter.mp hx).1)) hbcard
  · intro η hη hcd
    have hshort : ShortCofinal (b ∩ ordZ c.ord) c.ord := by
      refine ⟨⟨subOrd_iff_subset.mpr (fun x hx => (mem_inter.mp hx).2), ?_⟩, ?_⟩
      · intro ξ hξ
        obtain ⟨ζ, hξζ, hζ, hmem⟩ := ha₀.2 ξ hξ
        exact ⟨ζ, hξζ, hζ, mem_inter.mpr ⟨hab hmem, Ordinal.toZFSet_mem_toZFSet_iff.mpr hζ⟩⟩
      · rw [card_ord]
        exact lt_trans
          (lt_of_le_of_lt (card_mono (fun x hx => (mem_inter.mp hx).1)) hbcard) hδc
    exact barrier_above c γ η hc h hη _ hshort hcd

/-- Cofinality gap: `lam` is singular (with a witness of size `< δ`) in `HCD(δ)`
and regular in every `HCD(η)`, `η > γ`. -/
theorem cofinality_gap (δ c γ η : Cardinal.{u}) (hc : ℵ₀ ≤ c) (hδ : SC δ) (hδc : δ < c)
    (h : CEx γ c.ord) (hη : γ < η) :
    (∃ a, HCD δ a ∧ CofinalIn a c.ord ∧ ZFSet.card a < δ) ∧ RegularIn (HCD η) c.ord := by
  obtain ⟨a, ha, hcof, hcard, -⟩ := separation δ c γ hc hδ hδc h
  exact ⟨⟨a, ha, hcof, hcard⟩, regular_in_HCD c γ η hc h hη⟩

/-- Refinement (1) of Theorem 6.1 (report R2): the witness has no cover of size
below `c` in `CD(η)`. -/
theorem separation_no_small_cover (δ c γ : Cardinal.{u}) (hc : ℵ₀ ≤ c) (hδ : SC δ)
    (hδc : δ < c) (h : CEx γ c.ord) :
    ∃ a : ZFSet.{u}, HCD δ a ∧ CofinalIn a c.ord ∧ ZFSet.card a < δ ∧
      ∀ η, γ < η → ∀ b, CD η b → SubOrd b c.ord → a ⊆ b → c ≤ ZFSet.card b := by
  obtain ⟨a, ha, hcof, hcard, -⟩ := separation δ c γ hc hδ hδc h
  refine ⟨a, ha, hcof, hcard, fun η hη b hb hbsub hab => ?_⟩
  refine cover_gap c γ η hc h hη b hb ⟨hbsub, fun ξ hξ => ?_⟩
  obtain ⟨ζ, hξζ, hζ, hmem⟩ := hcof.2 ξ hξ
  exact ⟨ζ, hξζ, hζ, hab hmem⟩

/-- Refinement (2) of Theorem 6.1 (report R6): no cofinal subset of the witness
lies in `CD(η)`. -/
theorem separation_no_refinement (δ c γ : Cardinal.{u}) (hc : ℵ₀ ≤ c) (hδ : SC δ)
    (hδc : δ < c) (h : CEx γ c.ord) :
    ∃ a : ZFSet.{u}, HCD δ a ∧ CofinalIn a c.ord ∧ ZFSet.card a < δ ∧
      ∀ η, γ < η → ∀ b, b ⊆ a → CofinalIn b c.ord → ¬ CD η b := by
  obtain ⟨a, ha, hcof, hcard, -⟩ := separation δ c γ hc hδ hδc h
  refine ⟨a, ha, hcof, hcard, fun η hη b hba hbcof hb => ?_⟩
  refine barrier_above c γ η hc h hη b ⟨hbcof, ?_⟩ hb
  rw [card_ord]
  exact lt_trans (lt_of_le_of_lt (card_mono hba) hcard) hδc

/-- Refinement (3) of Theorem 6.1 (report R4): some `δ`-complete ultrafilter on an
ordinal is not in `CD(η)`. -/
theorem separation_ultrafilter (δ c γ η : Cardinal.{u}) (hc : ℵ₀ ≤ c) (hδ : SC δ)
    (hδc : δ < c) (h : CEx γ c.ord) (hη : γ < η) :
    ∃ U, IsCompleteUF δ U ∧ ¬ CD η U := by
  obtain ⟨a, ha, -, -, hnot⟩ := separation δ c γ hc hδ hδc h
  by_contra hcon
  push Not at hcon
  exact hnot η hη (Published.ODfrom_trans _ _ a ha.cd hcon)

/-! ### The conditional inconsistency in its reported forms (Corollary 6.2) -/

section Principles

variable (δ η : Cardinal.{u}) (lam : Ordinal.{u})

/-- `P₁` local stabilization on `𝒫(lam)`. -/
def P1 : Prop := ∀ a, SubOrd a lam → HCD δ a → HCD η a

/-- `P₂` local promotion of small subsets of `lam` (sizes ambient). -/
def P2 : Prop := ∀ a, SubOrd a lam → ZFSet.card a < δ → HCD δ a → HCD η a

/-- `P₄` weak covering: small `HCD(δ)`-subsets of `lam` are covered by
`HCD(η)`-subsets of `lam` of size below `|lam|`. -/
def P4 : Prop := ∀ a, SubOrd a lam → ZFSet.card a < δ → HCD δ a →
  ∃ b, HCD η b ∧ SubOrd b lam ∧ a ⊆ b ∧ ZFSet.card b < lam.card

/-- `P₅` cofinal refinement. -/
def P5 : Prop := ∀ a, CofinalIn a lam → ZFSet.card a < δ → HCD δ a →
  ∃ b, HCD η b ∧ b ⊆ a ∧ CofinalIn b lam

/-- `P₆` ultrafilter-code promotion. -/
def P6 : Prop := ∀ U, IsCompleteUF δ U → CD η U

/-- `P₇` some short cofinal subset of `lam` lies in `CD(η)`. -/
def P7 : Prop := ∃ a, ShortCofinal a lam ∧ CD η a

theorem P1.toP2 (h : P1 δ η lam) : P2 δ η lam := fun a ha _ hN => h a ha hN

theorem P2.toP4 (hδ : δ ≤ lam.card) (h : P2 δ η lam) : P4 δ η lam :=
  fun a ha hcard hN => ⟨a, h a ha hcard hN, ha, fun _ hx => hx, lt_of_lt_of_le hcard hδ⟩

theorem P2.toP5 (h : P2 δ η lam) : P5 δ η lam :=
  fun a ha hcard hN => ⟨a, h a ha.1 hcard hN, fun _ hx => hx, ha⟩

theorem P6.toP1 (h : P6 δ η) : P1 δ η lam := fun a ha hN =>
  HCD_of_CD_of_subOrd ha (Published.ODfrom_trans _ _ a hN.cd h)

end Principles

/-- `P₇` alone contradicts cover exactingness (no strongly compact needed). -/
theorem not_P7 (c γ η : Cardinal.{u}) (hc : ℵ₀ ≤ c) (h : CEx γ c.ord) (hη : γ < η) :
    ¬ P7 η c.ord :=
  fun ⟨a, ha, hcd⟩ => barrier_above c γ η hc h hη a ha hcd

/-- `P₄` yields `P₇` in the presence of the separation witness. -/
theorem not_P4 (δ c γ η : Cardinal.{u}) (hc : ℵ₀ ≤ c) (hδ : SC δ) (hδc : δ < c)
    (h : CEx γ c.ord) (hη : γ < η) : ¬ P4 δ η c.ord := by
  intro hP
  obtain ⟨a, ha, hcof, hcard, -⟩ := separation δ c γ hc hδ hδc h
  obtain ⟨b, hbN, hbsub, hab, hbcard⟩ := hP a hcof.1 hcard ha
  refine not_P7 c γ η hc h hη ⟨b, ⟨⟨hbsub, fun ξ hξ => ?_⟩, hbcard⟩, hbN.cd⟩
  obtain ⟨ζ, hξζ, hζ, hmem⟩ := hcof.2 ξ hξ
  exact ⟨ζ, hξζ, hζ, hab hmem⟩

/-- `P₅` yields `P₇` in the presence of the separation witness. -/
theorem not_P5 (δ c γ η : Cardinal.{u}) (hc : ℵ₀ ≤ c) (hδ : SC δ) (hδc : δ < c)
    (h : CEx γ c.ord) (hη : γ < η) : ¬ P5 δ η c.ord := by
  intro hP
  obtain ⟨a, ha, hcof, hcard, -⟩ := separation δ c γ hc hδ hδc h
  obtain ⟨b, hbN, hba, hbcof⟩ := hP a hcof hcard ha
  refine not_P7 c γ η hc h hη ⟨b, ⟨hbcof, ?_⟩, hbN.cd⟩
  rw [card_ord]
  exact lt_trans (lt_of_le_of_lt (card_mono hba) hcard) hδc

/-- **Conditional inconsistency below `lam` (synthesis Corollary 6.2).**
A strongly compact `δ < c`, `γ`-cover exactingness of `c.ord`, and any one of the
principles `P₁, P₂, P₄, P₅, P₆` between the levels `δ` and `η > γ` are jointly
contradictory. -/
theorem conditional_inconsistency (δ c γ η : Cardinal.{u}) (hc : ℵ₀ ≤ c) (hδ : SC δ)
    (hδc : δ < c) (h : CEx γ c.ord) (hη : γ < η) :
    ¬ P1 δ η c.ord ∧ ¬ P2 δ η c.ord ∧ ¬ P4 δ η c.ord ∧ ¬ P5 δ η c.ord ∧ ¬ P6 δ η := by
  have h5 := not_P5 δ c γ η hc hδ hδc h hη
  have h4 := not_P4 δ c γ η hc hδ hδc h hη
  have h2 : ¬ P2 δ η c.ord := fun hP => h5 hP.toP5
  have h1 : ¬ P1 δ η c.ord := fun hP => h2 hP.toP2
  exact ⟨h1, h2, h4, h5, fun hP => h1 (hP.toP1 δ η c.ord)⟩

/-- **The extendible boundary recovered (synthesis Corollary 6.3; Blue–Goldberg's
Theorem 3.6).**  No cover-exacting cardinal lies above an extendible cardinal. -/
theorem no_CEx_above_extendible (δ c γ : Cardinal.{u}) (hc : ℵ₀ ≤ c)
    (hext : Extendible δ.ord) (hδc : δ < c) : ¬ CEx γ c.ord := by
  intro h
  have hδ : SC δ := Published.SC_of_extendible δ hext
  have hP1 : P1 δ (Order.succ γ) c.ord :=
    fun a _ hN => Published.HCD_stabilizes δ hext a hN _
  exact (conditional_inconsistency δ c γ (Order.succ γ) hc hδ hδc h (Order.lt_succ γ)).1 hP1

/-- Monotonicity of the cofinality profile (synthesis Theorem 6.4, first part). -/
theorem RegularIn_HCD_mono {η ξ : Cardinal.{u}} (hηξ : η ≤ ξ) {lam : Ordinal.{u}}
    (h : RegularIn (HCD η) lam) : RegularIn (HCD ξ) lam :=
  fun a haN => h a (haN.mono hηξ)

/-- Below a strongly compact `δ < c` the profile has not yet regularized
(synthesis Theorem 6.4, lower bound `r(lam) > δ`). -/
theorem not_RegularIn_HCD_of_le (δ c γ ρ : Cardinal.{u}) (hc : ℵ₀ ≤ c) (hδ : SC δ)
    (hδc : δ < c) (h : CEx γ c.ord) (hρ : ρ ≤ δ) : ¬ RegularIn (HCD ρ) c.ord := by
  intro hreg
  obtain ⟨a, ha, hcof, hcard, -⟩ := separation δ c γ hc hδ hδc h
  refine hreg a (ha.mono hρ) ⟨hcof, ?_⟩
  rw [card_ord]
  exact lt_trans hcard hδc

end Cardinals
