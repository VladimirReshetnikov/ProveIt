import ZFCinPA.LStepAnd

set_option autoImplicit false
noncomputable section

/-!
# Disjunction, negation and the constant steps of the reflection generator

* `orTemplate` (six placeholders, as `LStepAnd.andTemplate`): the
  disjunction step, by `satIn_or`;
* `negTemplate` (`P₀ F₁ P₂`, arities `1 2 1`): if `F₁` is a total reflection
  function for `P₀` and `P₂ = ¬P₀`, it is one for `P₂` (code `c → ⊥`), which
  serves the negated atoms of the environment transform;
* `topBase`, `botBase` (no placeholders): the successor function is a total
  reflection function for `⊤` (code `⊥ → ⊥`) and for `⊥` (code `⊥`).

The successor function `succP` is also the reflection function of atoms.
-/

namespace LeanProofs.ZFCinPA.LStepBasic

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.LTemplate
open LeanProofs.ZFCinPA.LPieces LeanProofs.ZFCinPA.LInvariant LeanProofs.ZFCinPA.LStepAnd

/-- `g = a ∪ {a}`. -/
def succP : SetTheorySemisentence 2 := piece 1 (SetTheory.BusyBeaver.ZFC.InternalRank.succF 1 0)

section Semantics

open SetTheory.BusyBeaver.ZFC.InternalOrd SetTheory.BusyBeaver.ZFC.Constructible
  SetTheory.BusyBeaver.ZFC.ConstructibleDef LeanProofs.BoundedZFCConsistency

variable {V : Type*} [SetStructure V] (H : _root_.SetTheory.ZFAxioms (memRel V))
  (hR : Regular (memRel V))
  (hP : ∀ a, ∃ p, ∀ x, memRel V x p ↔ _root_.SetTheory.Sub (memRel V) x a)

@[simp] theorem eval_succP (a g : V) (ε : Empty → V) :
    succP.Eval ![a, g] ε ↔ g = _root_.SetTheory.vsucc H a := by
  rw [succP, eval_piece, SetTheory.BusyBeaver.ZFC.InternalRank.nsat_succF H]
  rfl

/-- The successor function is total on ordinals and above its argument. -/
theorem tot_succ : Tot (fun a g : V => g = _root_.SetTheory.vsucc H a) := fun a ha =>
  ⟨_, ord_succ H ha, _root_.SetTheory.vsucc_self H a, rfl, fun _ h => h⟩

include hR in
/-- Every nonzero limit is closed under the successor. -/
theorem lim_closed_succ {b : V} (hb : IsLim (memRel V) b) :
    ∀ a, a ∈ b → ∀ g, g = _root_.SetTheory.vsucc H a → g ∈ b := by
  rintro a ha g rfl
  obtain ⟨γ, hγ, haγ⟩ := hb.2.2 a ha
  have hγo : Ord (memRel V) γ := ord_of_mem hb.1 hγ
  refine mem_of_sub_mem H hR hb.1 hγ (ord_succ H (ord_of_mem hb.1 ha)) fun z hz => ?_
  rcases (_root_.SetTheory.vsucc_spec H a z).1 hz with hz | rfl
  · exact hγo.1 a haγ z hz
  · exact haγ

include hR in
/-- **The disjunction step.** -/
theorem or_step {P₀ P₂ P₄ : V → Prop} {F₁ F₃ F₅ : V → V → Prop}
    (htot₁ : Tot F₁) (hrefl₁ : Refl H hP P₀ F₁) (htot₃ : Tot F₃) (hrefl₃ : Refl H hP P₂ F₃)
    (hdefP : ∀ t, P₄ t ↔ P₀ t ∨ P₂ t)
    (hdefF : ∀ a g, F₅ a g ↔ ∃ g₁ g₂, F₁ a g₁ ∧ F₃ a g₂ ∧ ∀ z, z ∈ g ↔ z ∈ g₁ ∨ z ∈ g₂) :
    Tot F₅ ∧ Refl H hP P₄ F₅ := by
  -- the conjunction step at the same functions supplies totality and closure
  obtain ⟨htot, c, -, hr⟩ := and_step H hR hP (P₄ := fun t => P₀ t ∧ P₂ t)
    htot₁ hrefl₁ htot₃ hrefl₃ (fun _ => Iff.rfl) hdefF
  refine ⟨htot, ?_⟩
  obtain ⟨c₁, hc₁, hr₁⟩ := hrefl₁
  obtain ⟨c₂, hc₂, hr₂⟩ := hrefl₃
  refine ⟨_, isFormCodeSem_or H hc₁ hc₂, fun b hb hcl S hS R hR' t ht hfin => ?_⟩
  -- closure under both components, as in the conjunction step
  have hcl₁ : ∀ a, a ∈ b → ∀ g, F₁ a g → g ∈ b := fun a ha g hg => by
    have hao := ord_of_mem hb.1 ha
    obtain ⟨g₁, ho₁, -, hF₁, u₁⟩ := htot₁ a hao
    obtain ⟨g₂, ho₂, -, hF₃, -⟩ := htot₃ a hao
    have hF₅ := (hdefF a _).2 ⟨g₁, g₂, hF₁, hF₃, fun z => _root_.SetTheory.vcup_spec H g₁ g₂ z⟩
    rw [u₁ g hg]
    exact mem_of_sub_mem H hR hb.1 (hcl a ha _ hF₅) ho₁
      fun z hz => (_root_.SetTheory.vcup_spec H _ _ z).2 (Or.inl hz)
  have hcl₃ : ∀ a, a ∈ b → ∀ g, F₃ a g → g ∈ b := fun a ha g hg => by
    have hao := ord_of_mem hb.1 ha
    obtain ⟨g₁, ho₁, -, hF₁, -⟩ := htot₁ a hao
    obtain ⟨g₂, ho₂, -, hF₃, u₃⟩ := htot₃ a hao
    have hF₅ := (hdefF a _).2 ⟨g₁, g₂, hF₁, hF₃, fun z => _root_.SetTheory.vcup_spec H g₁ g₂ z⟩
    rw [u₃ g hg]
    exact mem_of_sub_mem H hR hb.1 (hcl a ha _ hF₅) ho₂
      fun z hz => (_root_.SetTheory.vcup_spec H _ _ z).2 (Or.inr hz)
  rw [hdefP, hr₁ b hb hcl₁ S hS R hR' t ht hfin, hr₂ b hb hcl₃ S hS R hR' t ht hfin,
    satIn_or H (isSetStructure_stage H hR hP hb hS hR') hc₁ hc₂ ht]

include hR in
/-- **The negation step.** -/
theorem neg_step {P₀ P₂ : V → Prop} {F : V → V → Prop}
    (hrefl : Refl H hP P₀ F) (hdefP : ∀ t, P₂ t ↔ ¬ P₀ t) : Refl H hP P₂ F := by
  obtain ⟨c, hc, hr⟩ := hrefl
  refine ⟨_, isFormCodeSem_imp H hc (isFormCodeSem_bot H), fun b hb hcl S hS R hR' t ht hfin => ?_⟩
  rw [hdefP, hr b hb hcl S hS R hR' t ht hfin,
    satIn_imp H (isSetStructure_stage H hR hP hb hS hR') hc (isFormCodeSem_bot H) ht]
  exact ⟨fun h hs => absurd hs h, fun h hs => satIn_bot H (h hs)⟩

include hR in
/-- `⊤` is reflected (code `⊥ → ⊥`). -/
theorem top_refl {F : V → V → Prop} : Refl H hP (fun _ => True) F :=
  ⟨_, isFormCodeSem_imp H (isFormCodeSem_bot H) (isFormCodeSem_bot H),
    fun b hb _ S hS R hR' t ht _ => by
      rw [satIn_imp H (isSetStructure_stage H hR hP hb hS hR') (isFormCodeSem_bot H)
        (isFormCodeSem_bot H) ht]
      exact ⟨fun _ h => h, fun _ => trivial⟩⟩

/-- `⊥` is reflected (code `⊥`). -/
theorem bot_refl {F : V → V → Prop} : Refl H hP (fun _ => False) F :=
  ⟨_, isFormCodeSem_bot H, fun _ _ _ _ _ _ _ _ _ _ => ⟨False.elim, satIn_bot H⟩⟩

end Semantics

/-! ## The templates -/

local instance : Language.Mem L6 := ⟨Sum.inl Language.Set.Rel.mem⟩

/-- `P₄` is the disjunction of `P₀` and `P₂`. -/
def orDefP : Sentence L6 := “∀ t, !P₄ t ↔ !P₀ t ∨ !P₂ t”

/-- **The disjunction template.** -/
def orTemplate : Sentence L6 :=
  (totS F₁ ⋏ reflS P₀ F₁ ⋏ totS F₃ ⋏ reflS P₂ F₃ ⋏ orDefP ⋏ maxDefF) 🡒 (totS F₅ ⋏ reflS P₄ F₅)

theorem models_orDefP {M : Type} [Nonempty M] [Structure L6 M] :
    M↓[L6] ⊧ orDefP ↔ ∀ t : M, P₄.Eval ![t] Empty.elim ↔
      P₀.Eval ![t] Empty.elim ∨ P₂.Eval ![t] Empty.elim := by
  simp [models_iff, orDefP]

theorem orTemplate_provable : templTheory 6 ar6 ⊢ orTemplate := by
  apply templ_provable
  intro M _ _ s _ _ _
  haveI : M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory) := pure_models (k := 6) (arities := ar6)
  simp only [orTemplate, Semantics.Imp.models_imply, Semantics.And.models_and]
  rintro ⟨htot₁, hrefl₁, htot₃, hrefl₃, hdefP, hdefF⟩
  rw [models_totS] at htot₁ htot₃ ⊢
  rw [models_reflS] at hrefl₁ hrefl₃ ⊢
  rw [models_orDefP] at hdefP
  rw [models_maxDefF] at hdefF
  exact or_step (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M))
    (ConstructibleInterpretation.regular_of_modelsZF (V := M))
    (ConstructibleInterpretation.power_of_modelsZF (V := M))
    htot₁ hrefl₁ htot₃ hrefl₃ hdefP hdefF

/-- Placeholder arities of the negation step: `P₀ F₁ P₂`. -/
abbrev ar3 : Fin 3 → ℕ := ![1, 2, 1]

abbrev L3 := setTemplateLanguage 3 ar3

local instance : Language.Mem L3 := ⟨Sum.inl Language.Set.Rel.mem⟩

def nP₀ : Semisentence L3 1 := .rel (placeholderRel (0 : Fin 3)) ![#0]
def nF₁ : Semisentence L3 2 := .rel (placeholderRel (1 : Fin 3)) ![#0, #1]
def nP₂ : Semisentence L3 1 := .rel (placeholderRel (2 : Fin 3)) ![#0]

/-- `P₂` is the negation of `P₀`. -/
def negDefP : Sentence L3 := “∀ t, !nP₂ t ↔ ¬!nP₀ t”

/-- **The negation template.** -/
def negTemplate : Sentence L3 := (reflS nP₀ nF₁ ⋏ negDefP) 🡒 reflS nP₂ nF₁

theorem negTemplate_provable : templTheory 3 ar3 ⊢ negTemplate := by
  apply templ_provable
  intro M _ _ s _ _ _
  haveI : M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory) := pure_models (k := 3) (arities := ar3)
  simp only [negTemplate, Semantics.Imp.models_imply, Semantics.And.models_and]
  rintro ⟨hrefl, hdefP⟩
  rw [models_reflS] at hrefl ⊢
  have hdefP' : ∀ t : M, nP₂.Eval ![t] Empty.elim ↔ ¬ nP₀.Eval ![t] Empty.elim := by
    simpa [models_iff, negDefP] using hdefP
  exact neg_step (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M))
    (ConstructibleInterpretation.regular_of_modelsZF (V := M))
    (ConstructibleInterpretation.power_of_modelsZF (V := M)) hrefl hdefP'

/-- The template language without placeholders. -/
abbrev L0 := setTemplateLanguage 0 ![]

/-- The successor function, in the bare template language. -/
def succL : Semisentence L0 2 := lift succP

/-- **Base**: the successor is a total reflection function for `⊤`. -/
def topBase : Sentence L0 := totS succL ⋏ reflS ⊤ succL

/-- **Base**: the successor is a reflection function for `⊥`. -/
def botBase : Sentence L0 := reflS ⊥ succL

theorem topBase_provable : templTheory 0 ![] ⊢ topBase := by
  apply templ_provable
  intro M _ _ s _ _ _
  haveI : M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory) := pure_models (k := 0) (arities := ![])
  simp only [topBase, Semantics.And.models_and]
  refine ⟨?_, ?_⟩
  · rw [models_totS]
    simpa [Tot, succL, eval_succP (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M))] using
      tot_succ (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M))
  · rw [models_reflS]
    simpa [Refl] using top_refl (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M))
      (ConstructibleInterpretation.regular_of_modelsZF (V := M))
      (ConstructibleInterpretation.power_of_modelsZF (V := M))
      (F := fun a g => succL.Eval ![a, g] Empty.elim)

theorem botBase_provable : templTheory 0 ![] ⊢ botBase := by
  apply templ_provable
  intro M _ _ s _ _ _
  haveI : M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory) := pure_models (k := 0) (arities := ![])
  simp only [botBase]
  rw [models_reflS]
  simpa [Refl] using bot_refl (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M))
    (ConstructibleInterpretation.power_of_modelsZF (V := M))
    (F := fun a g => succL.Eval ![a, g] Empty.elim)

end LeanProofs.ZFCinPA.LStepBasic
