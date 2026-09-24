/-
  NO STRONGLY COMPACT SANDWICH (synthesis §7.4, report R24).

  * `IsOmegaClub`, `clubFilterTrace`, `OmegaClubAmenable`: Goldberg's `ω`-club amenable
    inner models; `IsMeasureIn`, `MeasurableIn`: measurability computed in a class;
    `CountableCover`: the `(ω₁, δ)`-cover property.
  * two admitted published inputs: Goldberg's dichotomy for amenable models, and the
    textbook fact that a ground does not make all large regular cardinals measurable;
  * `countableCover_contra`: a class with the `(ω₁, δ)`-cover property in which `lam > δ`
    is regular omits no countable cofinal subset of `lam` -- so there is none;
  * `amenable_ground_cover` (Theorem 7.11), `no_sandwich` (Theorem 7.12), `no_SC_above` and the
    inconsistency of the hypotheses of `two_strongly_compacts` (Corollary 7.5).

  The amenability of `HCD(η)` (synthesis Lemma 7.10: ordinal-definable subsets of
  `HCD(η)` belong to it) needs the definability of the class `HCD(η)` by reflection and is
  *not* formalized; it appears as the hypothesis `OmegaClubAmenable (HCD η)`.
-/
import Cardinals.Above

universe u

namespace Cardinals

open ZFSet Ordinal Cardinal

/-! ### `ω`-club amenability -/

/-- `C` is an `ω`-closed unbounded subset of `α`: unbounded in `α`, and closed under
suprema below `α` of strictly increasing `ω`-sequences. -/
def IsOmegaClub (α : Ordinal.{u}) (C : Set Ordinal.{u}) : Prop :=
  (∀ ξ ∈ C, ξ < α) ∧ (∀ β < α, ∃ ξ ∈ C, β ≤ ξ) ∧
    ∀ s : ℕ → Ordinal.{u}, StrictMono s → (∀ n, s n ∈ C) →
      ∀ β < α, IsLUB (Set.range s) β → β ∈ C

/-- The trace on the class `N` of the *ambient* `ω`-club filter on `α`. -/
def clubFilterTrace (N : ZFSet.{u} → Prop) (α : Ordinal.{u}) : Set ZFSet.{u} :=
  {A | N A ∧ A ⊆ ordZ α ∧ ∃ C, IsOmegaClub α C ∧ ∀ ξ ∈ C, ordZ ξ ∈ A}

/-- `N` is `ω`-club amenable: for every `α` of uncountable cofinality, the trace on `N`
of the ambient `ω`-club filter on `α` is a member of `N`. -/
def OmegaClubAmenable (N : ZFSet.{u} → Prop) : Prop :=
  ∀ α : Ordinal.{u}, ℵ₀ < α.cof → ∃ F, N F ∧ ∀ A, A ∈ F ↔ A ∈ clubFilterTrace N α

/-- `U ∈ N` is, in the sense of `N`, a nonprincipal `θ`-complete ultrafilter on `θ`. -/
structure IsMeasureIn (N : ZFSet.{u} → Prop) (θ : Ordinal.{u}) (U : ZFSet.{u}) : Prop where
  mem : N U
  sub : ∀ A ∈ U, A ⊆ ordZ θ
  proper : ∅ ∉ U
  upward : ∀ A ∈ U, ∀ B, N B → A ⊆ B → B ⊆ ordZ θ → B ∈ U
  ultra : ∀ A, N A → A ⊆ ordZ θ → A ∈ U ∨ (ordZ θ \ A) ∈ U
  nonprincipal : ∀ ξ < θ, ({ordZ ξ} : ZFSet.{u}) ∉ U
  complete : ∀ β < θ, ∀ f, N f → IsFunc (ordZ β) U f →
    ZFSet.sep (fun x => ∀ i A, pair i A ∈ f → x ∈ A) (ordZ θ) ∈ U

/-- `θ` is measurable in `N`. -/
def MeasurableIn (N : ZFSet.{u} → Prop) (θ : Ordinal.{u}) : Prop := ∃ U, IsMeasureIn N θ U

/-- The `(ω₁, δ)`-cover property: every countable subset of `N` is covered by a member
of `N` of `N`-cardinality below `δ`. -/
def CountableCover (N : ZFSet.{u} → Prop) (δ : Cardinal.{u}) : Prop :=
  ∀ σ : ZFSet.{u}, (∀ x ∈ σ, N x) → ZFSet.card σ ≤ ℵ₀ →
    ∃ τ, N τ ∧ σ ⊆ τ ∧ ∃ β < δ.ord, ∃ f, N f ∧ IsInjFunc τ (ordZ β) f

/-! ### Admitted published inputs -/

namespace Published

/-- Goldberg's dichotomy for `ω`-club amenable models: if `N` is `ω`-club amenable and
`δ` is strongly compact, then all sufficiently large regular cardinals are measurable
in `N`, or `N` has the `(ω₁, δ)`-cover property.

Reference: G. Goldberg, "Strongly compact cardinals and ordinal definability", J. Math.
Log. 24(1) (2024) 2250010, arXiv:2107.00513v1, Lemma 2.7: "Suppose `N` is `ω`-club
amenable and `δ` is `ω₁`-strongly compact. Then one of the following holds: (1) All
sufficiently large regular cardinals are measurable in `N`. (2) `N` has the
`(ω₁, δ)`-cover property."  The definitions of `ω`-club amenable and of the
`(λ, δ)`-cover property are in §2.2 there; a strongly compact cardinal is
`ω₁`-strongly compact.  (Statement checked against the arXiv text.) -/
theorem amenable_dichotomy (N : ZFSet.{u} → Prop) (hN : IsInnerModelZFC N)
    (ham : OmegaClubAmenable N) (δ : Cardinal.{u}) (hδ : SC δ) :
    (∃ θ₀ : Cardinal.{u}, ∀ θ : Cardinal.{u}, θ₀ ≤ θ → θ.IsRegular → MeasurableIn N θ.ord) ∨
      CountableCover N δ := by
  admit

/-- Over a set-forcing ground `W`, arbitrarily large regular cardinals of `V` are not
measurable in `W`: if `V = W[G]` with `G ⊆ P ∈ W` and `μ ≥ |P|`, then `θ = (μ⁺)^W` is
still a cardinal in `V`, hence a successor cardinal and regular in `V`, while a
successor cardinal of `W` is not measurable in `W`.

Reference: T. Jech, "Set Theory", 3rd millennium ed., Springer 2003, Theorem 15.3 (a
forcing with the `κ`-chain condition preserves cardinals `≥ κ`; a poset of size `μ` is
`μ⁺`-cc) together with Lemma 10.4 (every measurable cardinal is inaccessible), applied
inside `W`.  This is the two-line combination of the two textbook statements used in
R24, §6. -/
theorem ground_not_eventually_measurable (W : ZFSet.{u} → Prop) (hW : IsGround W)
    (θ₀ : Cardinal.{u}) : ∃ θ : Cardinal.{u}, θ₀ ≤ θ ∧ θ.IsRegular ∧ ¬ MeasurableIn W θ.ord := by
  admit

end Published

/-! ### From covering to a contradiction -/

/-- A class `N` with the `(ω₁, δ)`-cover property in which `c.ord` is regular, `δ < c`,
leaves no room for a countable cofinal subset of `c.ord`. -/
theorem countableCover_contra (N : ZFSet.{u} → Prop) (hN : IsInnerModelZF N)
    (δ c : Cardinal.{u}) (hδc : δ < c) (hcov : CountableCover N δ)
    (hreg : RegularIn N c.ord) (a : ZFSet.{u}) (ha : CofinalIn a c.ord)
    (hcard : ZFSet.card a ≤ ℵ₀) : False := by
  have haN : ∀ x ∈ a, N x := fun x hx => by
    obtain ⟨ξ, -, rfl⟩ := ha.1 x hx
    exact hN.ords ξ
  obtain ⟨τ, hτN, hsub, β, hβ, f, -, hf⟩ := hcov a haN hcard
  have hτcard : ZFSet.card τ < δ := by
    refine lt_of_le_of_lt (card_le_of_isInjFunc hf) ?_
    rw [card_toZFSet]
    exact Cardinal.lt_ord.mp hβ
  have hbN : N (τ ∩ ordZ c.ord) := hN.inter_ord hτN c.ord
  have hcof : CofinalIn (τ ∩ ordZ c.ord) c.ord := by
    refine ⟨subOrd_iff_subset.mpr (fun x hx => (mem_inter.mp hx).2), fun ξ hξ => ?_⟩
    obtain ⟨η, h1, h2, h3⟩ := ha.2 ξ hξ
    exact ⟨η, h1, h2, mem_inter.mpr ⟨hsub h3, Ordinal.toZFSet_mem_toZFSet_iff.mpr h2⟩⟩
  refine hreg _ hbN ⟨hcof, ?_⟩
  rw [card_ord]
  exact lt_of_le_of_lt (card_mono (fun x hx => (mem_inter.mp hx).1)) (hτcard.trans hδc)

/-- **Covering by an amenable ground (synthesis Theorem 7.11, via Goldberg's lemma).** -/
theorem amenable_ground_cover (W : ZFSet.{u} → Prop) (hW : IsGround W)
    (ham : OmegaClubAmenable W) (δ : Cardinal.{u}) (hδ : SC δ) : CountableCover W δ := by
  rcases Published.amenable_dichotomy W hW.1 ham δ hδ with ⟨θ₀, h⟩ | h
  · obtain ⟨θ, hθ, hreg, hnot⟩ := Published.ground_not_eventually_measurable W hW θ₀
    exact absurd (h θ hθ hreg) hnot
  · exact h

/-- A cardinal above a strongly compact `δ` that is regular in an amenable ground has
no countable cofinal subset. -/
theorem amenable_ground_cof (W : ZFSet.{u} → Prop) (hW : IsGround W)
    (ham : OmegaClubAmenable W) (δ c : Cardinal.{u}) (hδ : SC δ) (hδc : δ < c)
    (hreg : RegularIn W c.ord) (a : ZFSet.{u}) (ha : CofinalIn a c.ord) :
    ¬ ZFSet.card a ≤ ℵ₀ := fun hcard =>
  countableCover_contra W hW.1.toIsInnerModelZF δ c hδc
    (amenable_ground_cover W hW ham δ hδ) hreg a ha hcard

/-- **No strongly compact sandwich (synthesis Theorem 7.12).**  If `δ < c ≤ γ < η`, `δ`
is strongly compact and `c.ord` is `γ`-cover exacting, then an `ω`-club amenable
`HCD(η)` is not a ground of `V`. -/
theorem no_sandwich (δ c γ η : Cardinal.{u}) (hc : ℵ₀ ≤ c) (hδ : SC δ) (hδc : δ < c)
    (h : CEx γ c.ord) (hη : γ < η) (ham : OmegaClubAmenable (HCD η)) :
    ¬ IsGround (HCD η) := fun hgr => by
  obtain ⟨a, ha, hcard⟩ := exists_countable_cofinal c γ hc h
  exact amenable_ground_cof (HCD η) hgr ham δ c hδ hδc (regular_in_HCD c γ η hc h hη) a ha hcard

/-- No strongly compact cardinal lies above the cover bound of a cover-exacting
cardinal that lies above a strongly compact cardinal (given the amenability of
`HCD(κ)`, synthesis Lemma 7.10).  In particular the hypotheses of
`two_strongly_compacts` are inconsistent. -/
theorem no_SC_above (δ c γ κ : Cardinal.{u}) (hc : ℵ₀ ≤ c) (hδ : SC δ) (hδc : δ < c)
    (h : CEx γ c.ord) (hκ : SC κ) (hγκ : γ < κ) (ham : OmegaClubAmenable (HCD κ)) : False :=
  no_sandwich δ c γ κ hc hδ hδc h hγκ ham (Published.HCD_isGround κ hκ)

end Cardinals
