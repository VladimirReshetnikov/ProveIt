import ZFCinPA.LGlueT

set_option autoImplicit false
noncomputable section

/-!
# The glue templates for the formula induction

The induction linking `relativize` with `envForm` proves, for each formula
`q` with free variables below `j`,
`∀t (¬M_j t ∨ (q^L ↔ envForm 0 q (t)))`. In the templates, `G₀` is the
matching predicate, `G₁` the relativized side and `G₂` the environment side
(`gS 0 1 2`). The step templates over `GL`:

* `andG`, `orG`, `negG`, `topG`, `botG`: connectives, literally;
* `allG`, `exG`: a quantifier, from the freed premise read at
  `econs y t` (the successor clause of `M`) and functionality;
* `atomG false/true`: an atom `&a ∈ &b` (`&a = &b`), from the slot
  statements of `a` and `b`, their numerals, and uniqueness of the slot
  values; the environment side is literally `envForm`'s atom.
-/

namespace LeanProofs.ZFCinPA.LGlueT2

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.LTemplate
open LeanProofs.ZFCinPA.LInvariant LeanProofs.ZFCinPA.EnvTransform LeanProofs.ZFCinPA.LGlueT
open LeanProofs.ZFCinPA.ConstructibleInterpretation (domL)

local instance : Language.Mem GL := ⟨Sum.inl Language.Set.Rel.mem⟩

/-- `x = y`. -/
def eq2S : SetTheorySemisentence 2 := “x y. x = y”

/-- The glue statement for slots `i` (matching), `r` (relativized), `e` (environment). -/
def gS (i r e : Fin 8) : Sentence GL := ∀⁰ (∼G i ⋎ (G r 🡘 G e))

def andG : Sentence GL := (gS 0 1 2 ⋏ gS 0 3 4) 🡒 ∀⁰ (∼G 0 ⋎ (G 1 ⋏ G 3 🡘 G 2 ⋏ G 4))
def orG : Sentence GL := (gS 0 1 2 ⋏ gS 0 3 4) 🡒 ∀⁰ (∼G 0 ⋎ (G 1 ⋎ G 3 🡘 G 2 ⋎ G 4))
def negG : Sentence GL := gS 0 1 2 🡒 ∀⁰ (∼G 0 ⋎ (∼G 1 🡘 ∼G 2))
def topG : Sentence GL := ∀⁰ (∼G 0 ⋎ ((⊤ : Semisentence GL 1) 🡘 ⊤))
def botG : Sentence GL := ∀⁰ (∼G 0 ⋎ ((⊥ : Semisentence GL 1) 🡘 ⊥))

/-- The freed premise of a quantifier step: at level two, `t = #0`, `y = #1`,
`∃t₁ ∃z (z = y ∧ t = econs z t₁ ∧ G₀ t₁)`. -/
def mp2 : Semisentence GL 2 :=
  ∃⁰ ∃⁰ ((lift eq2S ⇜ ![#0, #3]) ⋏ ((lift econsS ⇜ ![#2, #0, #1]) ⋏ (G 0 ⇜ ![#1])))

/-- The premise of a quantifier step: `∀y ∀t (¬mp2(t, y) ∨ (G₁ y ↔ G₂ t))`. -/
def qHyp : Sentence GL := ∀⁰ ∀⁰ (∼mp2 ⋎ ((G 1 ⇜ ![#1]) 🡘 (G 2 ⇜ ![#0])))

/-- `relativize`'s universal clause over `G₁`. -/
def relAll : Semisentence GL 1 := ∀⁰ (∼(lift domL ⇜ ![#0]) ⋎ (G 1 ⇜ ![#0]))

/-- `relativize`'s existential clause over `G₁`. -/
def relEx : Semisentence GL 1 := ∃⁰ ((lift domL ⇜ ![#0]) ⋏ (G 1 ⇜ ![#0]))

/-- `envForm`'s universal clause over `G₂` (the shape of `LStepExT.allBody`). -/
def envAll : Semisentence GL 1 := ∀⁰ ∀⁰ (∼lift econsS ⋎ (∼lift domYS ⋎ (G 2 ⇜ ![#0])))

/-- `envForm`'s existential clause over `G₂` (the shape of `LStepExT.exBody`). -/
def envEx : Semisentence GL 1 := ∃⁰ ∃⁰ (lift econsS ⋏ (lift domYS ⋏ (G 2 ⇜ ![#0])))

def allG : Sentence GL := (funM 0 ⋏ qHyp) 🡒 ∀⁰ (∼G 0 ⋎ (relAll 🡘 envAll))
def exG : Sentence GL := (funM 0 ⋏ qHyp) 🡒 ∀⁰ (∼G 0 ⋎ (relEx 🡘 envEx))

/-- The numeral at slot `j` names exactly one natural number. -/
def numOKG (j : Fin 8) : Sentence GL :=
  “(∃ m, !(G j) m ∧ ∀ m', !(G j) m' → m' = m) ∧ ∀ m, !(G j) m → !(lift LStepAtom.natP) m”

/-- At most one element satisfies `G k`. -/
def uniqG (k : Fin 8) : Sentence GL := ∀⁰ ∀⁰ (∼(G k ⇜ ![#1]) ⋎ (∼(G k ⇜ ![#0]) ⋎ lift eq2S))

/-- `envForm`'s atom over the numerals at slots `3`, `5`. -/
def envAtom (isEq : Bool) : Semisentence GL 1 :=
  ∃⁰ ∃⁰ ((∃⁰ ((G 3 ⇜ ![#0]) ⋏ lift appXS)) ⋏
    ((∃⁰ ((G 5 ⇜ ![#0]) ⋏ lift appYS)) ⋏ lift (if isEq then eqXYS else memXYS)))

/-- `G₁` is the atom between the slot values `G₄`, `G₆`. -/
def atomDef (isEq : Bool) : Sentence GL :=
  ∀⁰ (G 1 🡘 ∃⁰ ∃⁰ ((G 4 ⇜ ![#1]) ⋏ ((G 6 ⇜ ![#0]) ⋏ lift (if isEq then eqXYS else memXYS))))

def atomG (isEq : Bool) : Sentence GL :=
  (slotS 0 3 4 ⋏ slotS 0 5 6 ⋏ numOKG 3 ⋏ numOKG 5 ⋏ funM 0 ⋏ uniqG 4 ⋏ uniqG 6 ⋏ atomDef isEq) 🡒
    ∀⁰ (∼G 0 ⋎ (G 1 🡘 envAtom isEq))

/-! ## Proofs in template models -/

section Proofs

local notation "PH" i:max x:max => Structure.rel (L := GL) (placeholderRel i) ![x]

theorem andG_provable : templTheory 8 arG ⊢ andG := by
  apply templ_provable
  intro M _ _ s _ _ _
  simp [andG, gS, G, models_iff]
  intro h₁ h₂ t
  rcases h₁ t with h | h
  · exact Or.inl h
  rcases h₂ t with h' | h'
  · exact Or.inl h'
  exact Or.inr (by rw [h, h'])

theorem orG_provable : templTheory 8 arG ⊢ orG := by
  apply templ_provable
  intro M _ _ s _ _ _
  simp [orG, gS, G, models_iff]
  intro h₁ h₂ t
  rcases h₁ t with h | h
  · exact Or.inl h
  rcases h₂ t with h' | h'
  · exact Or.inl h'
  exact Or.inr (by rw [h, h'])

theorem negG_provable : templTheory 8 arG ⊢ negG := by
  apply templ_provable
  intro M _ _ s _ _ _
  simp [negG, gS, G, models_iff]
  intro h₁ t
  rcases h₁ t with h | h
  · exact Or.inl h
  exact Or.inr (by rw [h])

theorem topG_provable : templTheory 8 arG ⊢ topG := by
  apply templ_provable
  intro M _ _ s _ _ _
  simp [topG, G, models_iff]

theorem botG_provable : templTheory 8 arG ⊢ botG := by
  apply templ_provable
  intro M _ _ s _ _ _
  simp [botG, G, models_iff]

theorem allG_provable : templTheory 8 arG ⊢ allG := by
  apply templ_provable
  intro M _ _ s _ _ _
  haveI : M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory) := pure_models (k := 8) (arities := arG)
  set H := ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)
  set hP := ConstructibleInterpretation.power_of_modelsZF (V := M)
  simp only [allG, Semantics.Imp.models_imply, Semantics.And.models_and]
  rintro ⟨hf, hq⟩
  rw [models_funM] at hf
  simp [models_iff, qHyp, mp2, G, eq2S, Semiformula.Operator.eq_def] at hq
  simp [models_iff, relAll, envAll, G, ConstructibleInterpretation.eval_domL H hP,
    LStepExT.eval_domYS]
  intro t
  by_cases h0 : Structure.rel (L := GL) (placeholderRel 0) ![t]
  swap
  · exact Or.inl h0
  right
  have ft := hf t h0
  have he : ∀ y t' : M, (econsS.Eval ![t', y, t] Empty.elim ↔
      t' = LeanProofs.BoundedZFCConsistency.econs H y t) :=
    fun y t' => LStepExT.eval_econsS t' y t ft
  have key : ∀ y, (Structure.rel (L := GL) (placeholderRel 1) ![y] ↔
      Structure.rel (L := GL) (placeholderRel 2) ![LeanProofs.BoundedZFCConsistency.econs H y t]) := by
    intro y
    rcases hq y (LeanProofs.BoundedZFCConsistency.econs H y t) with h | h
    · rcases h t y with h1 | h1 | h1
      · exact absurd rfl h1
      · exact absurd ((he y _).2 rfl) h1
      · exact absurd h0 h1
    · exact h
  constructor
  · intro hR y t'
    by_cases hE : econsS.Eval ![t', y, t] Empty.elim
    · by_cases hy : SetTheory.BusyBeaver.ZFC.Constructible.InL H hP y
      · right; right
        rw [(he y t').1 hE]
        exact (key y).1 ((hR y).resolve_left (not_not.2 hy))
      · right; left; exact hy
    · left; exact hE
  · intro hE y
    by_cases hy : SetTheory.BusyBeaver.ZFC.Constructible.InL H hP y
    · right
      exact (key y).2 (((hE y _).resolve_left (not_not.2 ((he y _).2 rfl))).resolve_left
        (not_not.2 hy))
    · left; exact hy

theorem atomG_provable (isEq : Bool) : templTheory 8 arG ⊢ atomG isEq := by
  apply templ_provable
  intro M _ _ s _ _ _
  haveI : M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory) := pure_models (k := 8) (arities := arG)
  set H := ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)
  simp only [atomG, Semantics.Imp.models_imply, Semantics.And.models_and]
  rintro ⟨hsa, hsb, hna, hnb, hf, hua, hub, hdef⟩
  rw [models_funM] at hf
  rw [models_slotS] at hsa hsb
  simp [models_iff, numOKG, G, LStepAtom.eval_natP H] at hna hnb
  simp [models_iff, uniqG, G, eq2S, Semiformula.Operator.eq_def] at hua hub
  simp [models_iff, atomDef, G] at hdef
  simp [models_iff, envAtom, G, LStepAtom.eval_appXS H, LStepAtom.eval_appYS H]
  intro t
  by_cases h0 : Structure.rel (L := GL) (placeholderRel 0) ![t]
  swap
  · exact Or.inl h0
  right
  have ft := hf t h0
  obtain ⟨⟨ma, hma, hmau⟩, -⟩ := hna
  obtain ⟨⟨mb, hmb, hmbu⟩, -⟩ := hnb
  obtain ⟨xa, hxa, hxat⟩ := hsa t h0 ma hma
  obtain ⟨xb, hxb, hxbt⟩ := hsb t h0 mb hmb
  have rdA : ∀ x, (∃ m, Structure.rel (L := GL) (placeholderRel 3) ![m] ∧
      _root_.SetTheory.kpair H m x ∈ t) ↔ Structure.rel (L := GL) (placeholderRel 4) ![x] := by
    intro x
    constructor
    · rintro ⟨m, hm, hmx⟩
      rw [hmau m hm] at hmx
      rw [ft ma x xa hmx hxat]
      exact hxa
    · intro hx
      refine ⟨ma, hma, ?_⟩
      rcases hua xa x with h | h | h
      · exact absurd hxa h
      · exact absurd hx h
      · rw [h]; exact hxat
  have rdB : ∀ y, (∃ m, Structure.rel (L := GL) (placeholderRel 5) ![m] ∧
      _root_.SetTheory.kpair H m y ∈ t) ↔ Structure.rel (L := GL) (placeholderRel 6) ![y] := by
    intro y
    constructor
    · rintro ⟨m, hm, hmy⟩
      rw [hmbu m hm] at hmy
      rw [ft mb y xb hmy hxbt]
      exact hxb
    · intro hy
      refine ⟨mb, hmb, ?_⟩
      rcases hub xb y with h | h | h
      · exact absurd hxb h
      · exact absurd hy h
      · rw [h]; exact hxbt
  rw [hdef t]
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩
    exact ⟨x, (rdA x).2 hx, y, (rdB y).2 hy, hxy⟩
  · rintro ⟨x, hx, y, hy, hxy⟩
    exact ⟨x, (rdA x).1 hx, y, (rdB y).1 hy, hxy⟩

theorem exG_provable : templTheory 8 arG ⊢ exG := by
  apply templ_provable
  intro M _ _ s _ _ _
  haveI : M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory) := pure_models (k := 8) (arities := arG)
  set H := ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)
  set hP := ConstructibleInterpretation.power_of_modelsZF (V := M)
  simp only [exG, Semantics.Imp.models_imply, Semantics.And.models_and]
  rintro ⟨hf, hq⟩
  rw [models_funM] at hf
  simp [models_iff, qHyp, mp2, G, eq2S, Semiformula.Operator.eq_def] at hq
  simp [models_iff, relEx, envEx, G, ConstructibleInterpretation.eval_domL H hP,
    LStepExT.eval_domYS]
  intro t
  by_cases h0 : Structure.rel (L := GL) (placeholderRel 0) ![t]
  swap
  · exact Or.inl h0
  right
  have ft := hf t h0
  have he : ∀ y t' : M, (econsS.Eval ![t', y, t] Empty.elim ↔
      t' = LeanProofs.BoundedZFCConsistency.econs H y t) :=
    fun y t' => LStepExT.eval_econsS t' y t ft
  have key : ∀ y, (Structure.rel (L := GL) (placeholderRel 1) ![y] ↔
      Structure.rel (L := GL) (placeholderRel 2) ![LeanProofs.BoundedZFCConsistency.econs H y t]) := by
    intro y
    rcases hq y (LeanProofs.BoundedZFCConsistency.econs H y t) with h | h
    · rcases h t y with h1 | h1 | h1
      · exact absurd rfl h1
      · exact absurd ((he y _).2 rfl) h1
      · exact absurd h0 h1
    · exact h
  constructor
  · rintro ⟨y, hy, hR⟩
    exact ⟨y, _, (he y _).2 rfl, hy, (key y).1 hR⟩
  · rintro ⟨y, t', hE, hy, hP2⟩
    rw [(he y t').1 hE] at hP2
    exact ⟨y, hy, (key y).2 hP2⟩

end Proofs

end LeanProofs.ZFCinPA.LGlueT2
