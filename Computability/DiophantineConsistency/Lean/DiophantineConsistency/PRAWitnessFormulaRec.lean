import DiophantineConsistency.PRAWitnessFormulas
/-! # Witness bounds for formula recursions over `ℒₛₑₜ`

A `UformulaRec1.Blueprint` recursion is the fixpoint of triples
`⟪param, p, y⟫`. Its core has bounded witnesses once its clauses do
(`ClauseBounds`), the parameter changes at quantifiers being bounded by the
parameter. Its `fixpointDef` has an unbounded stage; `recRank`
`⟪param, p, y⟫ ↦ ⟪param, p, y + p⟫` decreases along the recursion when the
parameter does not grow and children's results are at most the result plus
one (`RecShape`), so the stage is polynomial in the triple
(`PRAWitnessFixpointGraph.stage_bound_of_rank`). Recursions whose parameter
grows (`substs`, through `qVec`) are not covered here. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAWitnessFormulaRec
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open StrictSigmaOneInduction PRAWitnessCalculus PRAWitnessArithmetic PRAWitnessVectors PRAWitnessSetTerms
  PRAWitnessTermRec PRAWitnessTermFunctions PRAWitnessFormulas

section sigma1
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The rank `⟪param, p, y⟫ ↦ ⟪param, p, y + p⟫`. -/
noncomputable def recRank (x : V) : V := ⟪π₁ x, π₁ (π₂ x), π₂ (π₂ x) + π₁ (π₂ x)⟫

instance recRank_definable : 𝚺₁-Function₁ (recRank : V → V) := by
  unfold recRank; definability

theorem le_recRank (x : V) : x ≤ recRank x := by
  have h : ⟪π₁ x, π₁ (π₂ x), π₂ (π₂ x)⟫ ≤ recRank x :=
    pair_le_pair_right _ (pair_le_pair_right _ le_self_add)
  simpa using h

@[simp] theorem recRank_pair₃ (a p y : V) : recRank ⟪a, p, y⟫ = ⟪a, p, y + p⟫ := by
  simp [recRank]

theorem child_lt {a a' p p₁ y y₁ : V} (ha : a' ≤ a) (hp : p₁ < p) (hy : y₁ ≤ y + 1) :
    ⟪a', p₁, y₁ + p₁⟫ < ⟪a, p, y + p⟫ := by
  have hyp : y₁ + p₁ ≤ y + p := by
    calc y₁ + p₁ ≤ (y + 1) + p₁ := add_le_add hy le_rfl
      _ = y + (p₁ + 1) := by rw [add_assoc, add_comm 1 p₁]
      _ ≤ y + p := add_le_add le_rfl (lt_iff_succ_le.mp hp)
  exact lt_of_le_of_lt (pair_le_pair_left ha _)
    (pair_lt_pair_right a (lt_of_lt_of_le (pair_lt_pair_left hp _) (pair_le_pair_right _ hyp)))

theorem pair₃_le_sq {a b c a' b' c' : V} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    ⟪a, b, c⟫ ≤ (a' + (b' + c' + 1) * (b' + c' + 1) + 1) * (a' + (b' + c' + 1) * (b' + c' + 1) + 1) :=
  pair_le_sq ha (pair_le_sq hb hc)

/-- The stage polynomial bounds the rank. -/
theorem recRank_succ_le (x : V) :
    recRank x + 1 ≤ (x + (x + (x + x) + 1) * (x + (x + x) + 1) + 1) *
      (x + (x + (x + x) + 1) * (x + (x + x) + 1) + 1) + 1 :=
  add_le_add (pair₃_le_sq (pi₁_le_self x) (le_trans (pi₁_le_self _) (pi₂_le_self x))
    (add_le_add (le_trans (pi₂_le_self _) (pi₂_le_self x)) (le_trans (pi₁_le_self _) (pi₂_le_self x))))
    le_rfl

variable {L : Language} [L.Encodable] [L.LORDefinable] {β : UformulaRec1.Blueprint}

/-- Growth conditions making `recRank` decrease along a recursion. -/
structure RecShape (c : UformulaRec1.Construction V β) : Prop where
  all_le : ∀ param, c.allChanges param ≤ param
  exs_le : ∀ param, c.exsChanges param ≤ param
  and_le : ∀ param p₁ p₂ y₁ y₂, y₁ ≤ c.and param p₁ p₂ y₁ y₂ + 1 ∧ y₂ ≤ c.and param p₁ p₂ y₁ y₂ + 1
  or_le : ∀ param p₁ p₂ y₁ y₂, y₁ ≤ c.or param p₁ p₂ y₁ y₂ + 1 ∧ y₂ ≤ c.or param p₁ p₂ y₁ y₂ + 1
  all_y : ∀ param p₁ y₁, y₁ ≤ c.all param p₁ y₁ + 1
  exs_y : ∀ param p₁ y₁, y₁ ≤ c.exs param p₁ y₁ + 1

theorem rankFinite (c : UformulaRec1.Construction V β) (h : RecShape c) :
    PRAFixpointRank.RankFinite (c.construction L) recRank := by
  rintro v C x ⟨param, p, y, rfl, hp, H⟩
  refine ⟨param, p, y, rfl, hp, ?_⟩
  rcases H with h1 | h1 | h1 | h1 | ⟨p₁, p₂, y₁, y₂, h₁, h₂, rfl, rfl⟩ |
    ⟨p₁, p₂, y₁, y₂, h₁, h₂, rfl, rfl⟩ | ⟨p₁, y₁, h₁, rfl, rfl⟩ | ⟨p₁, y₁, h₁, rfl, rfl⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h1))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p₁, p₂, y₁, y₂, ⟨h₁, ?_⟩, ⟨h₂, ?_⟩, rfl, rfl⟩))))
    · simpa using child_lt le_rfl (lt_K!_left p₁ p₂) (h.and_le param p₁ p₂ y₁ y₂).1
    · simpa using child_lt le_rfl (lt_K!_right p₁ p₂) (h.and_le param p₁ p₂ y₁ y₂).2
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p₁, p₂, y₁, y₂, ⟨h₁, ?_⟩, ⟨h₂, ?_⟩, rfl, rfl⟩)))))
    · simpa using child_lt le_rfl (lt_or_left p₁ p₂) (h.or_le param p₁ p₂ y₁ y₂).1
    · simpa using child_lt le_rfl (lt_or_right p₁ p₂) (h.or_le param p₁ p₂ y₁ y₂).2
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p₁, y₁, ⟨h₁, ?_⟩, rfl, rfl⟩))))))
    simpa using child_lt (h.all_le param) (lt_forall p₁) (h.all_y param p₁ y₁)
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p₁, y₁, ⟨h₁, ?_⟩, rfl, rfl⟩))))))
    simpa using child_lt (h.exs_le param) (lt_exists p₁) (h.exs_y param p₁ y₁)

end sigma1

section models
open PRAFiniteFunctionCodes PRALanguage PRATheory
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

variable (β : UformulaRec1.Blueprint)

/-- Witness bounds for the clause formulas of a formula recursion, and the
`𝗜𝚺₁` fact that its parameter changes do not increase the parameter. -/
structure ClauseBounds (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
    [M↓[language] ⊧* PRA] : Prop where
  rel : WB M β.rel.val
  nrel : WB M β.nrel.val
  verum : WB M β.verum.val
  falsum : WB M β.falsum.val
  and : WB M β.and.val
  or : WB M β.or.val
  all : WB M β.all.val
  exs : WB M β.exs.val
  allChanges : WB M β.allChanges.val
  exsChanges : WB M β.exsChanges.val
  rel_pi : WB M (∼β.rel.graphDelta.pi.val)
  nrel_pi : WB M (∼β.nrel.graphDelta.pi.val)
  verum_pi : WB M (∼β.verum.graphDelta.pi.val)
  falsum_pi : WB M (∼β.falsum.graphDelta.pi.val)
  and_pi : WB M (∼β.and.graphDelta.pi.val)
  or_pi : WB M (∼β.or.graphDelta.pi.val)
  all_pi : WB M (∼β.all.graphDelta.pi.val)
  exs_pi : WB M (∼β.exs.graphDelta.pi.val)
  allChanges_le : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (a b : V),
    β.allChanges.val.Evalb ![a, b] → a ≤ b
  exsChanges_le : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (a b : V),
    β.exsChanges.val.Evalb ![a, b] → a ≤ b

variable {β}

theorem wb_core_sigma (hβ : ClauseBounds β M) : WB M (β.blueprint ℒₛₑₜ).core.sigma.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := hβ.rel; have := hβ.nrel; have := hβ.verum; have := hβ.falsum; have := hβ.and
  have := hβ.or; have := hβ.all; have := hβ.exs; have := hβ.allChanges; have := hβ.exsChanges
  have := wb_isUFormula_sigma (M := M); have := wb_qqRelDef (M := M); have := wb_qqNRelDef (M := M)
  have := wb_qqVerumDef (M := M); have := wb_qqFalsumDef (M := M); have := wb_qqAndDef (M := M)
  have := wb_qqOrDef (M := M); have := wb_qqAllDef (M := M); have := wb_qqExsDef (M := M)
  have := wb_pair₃Def (M := M); have := wb_memRel₃ (M := M)
  have : WB M memRel₃Opr.sentence := wb_memRel₃ (M := M)
  simp only [UformulaRec1.Blueprint.blueprint, HierarchySymbol.Semiformula.sigma_mkDelta,
    HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto
  all_goals
    exact PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#6’
      (fun V _ _ e u h => ⟨u, by
        have h' := h; simp at h'
        simpa using le_of_lt (lt_of_le_of_lt (le_pair_left u _) (lt_of_mem h'.2)), h⟩) (by wb_auto)

theorem wb_core_neg_pi (hβ : ClauseBounds β M) : WB M (∼(β.blueprint ℒₛₑₜ).core.pi.val) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := hβ.rel_pi; have := hβ.nrel_pi; have := hβ.verum_pi; have := hβ.falsum_pi; have := hβ.and_pi
  have := hβ.or_pi; have := hβ.all_pi; have := hβ.exs_pi; have := hβ.allChanges; have := hβ.exsChanges
  have := wb_isUFormula_neg_pi (M := M); have := wb_qqRelDef (M := M); have := wb_qqNRelDef (M := M)
  have := wb_qqVerumDef (M := M); have := wb_qqFalsumDef (M := M); have := wb_qqAndDef (M := M)
  have := wb_qqOrDef (M := M); have := wb_qqAllDef (M := M); have := wb_qqExsDef (M := M)
  have := wb_pair₃Def (M := M); have := wb_memRel₃ (M := M); have := wb_neg_memRel₃ (M := M)
  have : WB M memRel₃Opr.sentence := wb_memRel₃ (M := M)
  have : WB M (∼memRel₃Opr.sentence) := wb_neg_memRel₃ (M := M)
  have := wb_neg_pair₃Def (M := M); have := wb_neg_qqRelDef (M := M); have := wb_neg_qqNRelDef (M := M)
  have := wb_neg_qqVerumDef (M := M); have := wb_neg_qqFalsumDef (M := M)
  have := wb_neg_qqAndDef (M := M); have := wb_neg_qqOrDef (M := M); have := wb_neg_qqAllDef (M := M)
  have := wb_neg_qqExsDef (M := M)
  simp only [UformulaRec1.Blueprint.blueprint, HierarchySymbol.Semiformula.pi_mkDelta,
    HierarchySymbol.Semiformula.val_mkPi]
  wb_auto
  · exact PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#4’
      (fun V _ _ e u h => ⟨u, by
        have h' := h; simp at h'
        simpa using hβ.allChanges_le V u (e 4) h'.1, h⟩) (by wb_auto)
  · exact PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#4’
      (fun V _ _ e u h => ⟨u, by
        have h' := h; simp at h'
        simpa using hβ.exsChanges_le V u (e 4) h'.1, h⟩) (by wb_auto)

/-- A construction of the blueprint in every `𝗜𝚺₁` model. -/
abbrev Constructions (β : UformulaRec1.Blueprint) :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁], UformulaRec1.Construction V β

theorem wb_fixpoint (c : Constructions β)
    (hc : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁], RecShape (c V)) (hβ : ClauseBounds β M) :
    WB M (β.blueprint ℒₛₑₜ).fixpointDef.val := by
  refine PRAWitnessFixpointGraph.wb_fixpointDef _ (wb_core_sigma hβ) (wb_core_neg_pi hβ)
    ‘(#0 + (#0 + (#0 + #0) + 1) * (#0 + (#0 + #0) + 1) + 1) *
      (#0 + (#0 + (#0 + #0) + 1) * (#0 + (#0 + #0) + 1) + 1) + 1’ ?_
  intro V _ _ e s L hL hx
  have h := PRAWitnessFixpointGraph.stage_bound_of_rank ((c V).construction ℒₛₑₜ) recRank
    le_recRank (rankFinite (c V) (hc V)) _ recRank_succ_le (fun i => e i.succ) (e 0) s L hL hx
  exact ⟨_, by simpa using h.1, h.2⟩

theorem wb_graph (c : Constructions β)
    (hc : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁], RecShape (c V)) (hβ : ClauseBounds β M) :
    WB M (β.graph ℒₛₑₜ).val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_fixpoint c hc hβ; have := wb_pair₃Def (M := M)
  simp only [UformulaRec1.Blueprint.graph, HierarchySymbol.Semiformula.val_mkSigma]
  exact PRAWitnessTransfer.wb_exs_poly _ (by simp)
    ‘(#0 + (#1 + #2 + 1) * (#1 + #2 + 1) + 1) * (#0 + (#1 + #2 + 1) * (#1 + #2 + 1) + 1)’
    (fun V _ _ e u h => ⟨u, by
      have h' := h; simp at h'
      rw [h'.1]
      simpa using pair₃_le_sq (le_refl (e 0)) (le_refl (e 1)) (le_refl (e 2)), h⟩) (by wb_auto)

theorem wb_result (c : Constructions β)
    (hc : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁], RecShape (c V)) (hβ : ClauseBounds β M) :
    WB M (β.result ℒₛₑₜ).val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_graph c hc hβ; have := wb_isUFormula_sigma (M := M); have := wb_isUFormula_neg_pi (M := M)
  simp only [UformulaRec1.Blueprint.result, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

end models
end DiophantineConsistency.PRAWitnessFormulaRec
