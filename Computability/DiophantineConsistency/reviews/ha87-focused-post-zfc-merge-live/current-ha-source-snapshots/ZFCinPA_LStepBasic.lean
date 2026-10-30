import ZFCinPA.LStepAnd

set_option autoImplicit false
noncomputable section

/-!
# Disjunction, negation and the constant steps of the reflection generator

* `orTemplate` (six placeholders, as `LStepAnd.andTemplate`): the
  disjunction step, by `satIn_or`;
* `negTemplate`: if `F₁` is a total reflection function for `P₀`,
  `P₄ = ¬P₀` and `F₅ = F₁`, then `F₅` is one for `P₄` (code `c → ⊥`), which
  serves the negated atoms of the environment transform;
* `topBase`, `botBase`: if `P₄` is `⊤` (resp. `⊥`) and `F₅` is the
  successor, then `F₅` is a total reflection function for `P₄` (codes
  `⊥ → ⊥` and `⊥`).

All templates of the generator live over the one language `LStepAnd.L6` and
conclude `totS F₅ ⋏ reflS P₄ F₅`, so a single code builder describes every
conclusion.

The successor function `succP` is also the reflection function of atoms.
-/

namespace LeanProofs.ZFCinPA.LStepBasic

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.LTemplate
open LeanProofs.ZFCinPA.LPieces LeanProofs.ZFCinPA.LInvariant LeanProofs.ZFCinPA.LStepAnd

/-- `g = a ∪ {a}`. -/
def succP : SetTheorySemisentence 2 := EnvTransform.piece 1 (SetTheory.BusyBeaver.ZFC.InternalRank.succF 1 0)

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
  refine ⟨_, isFormCodeSem_or H hc₁ hc₂, fun b hb hcl S hS R hR' a ha U hU t ht => ?_⟩
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
  rw [hdefP, hr₁ b hb hcl₁ S hS R hR' a ha U hU t ht, hr₂ b hb hcl₃ S hS R hR' a ha U hU t ht,
    satIn_or H (isSetStructure_stage H hR hP hb hS hR') hc₁ hc₂
      (envOn_stage H hR hP hb hS ha hU ht)]

include hR in
/-- **The negation step.** -/
theorem neg_step {P₀ P₂ : V → Prop} {F : V → V → Prop}
    (hrefl : Refl H hP P₀ F) (hdefP : ∀ t, P₂ t ↔ ¬ P₀ t) : Refl H hP P₂ F := by
  obtain ⟨c, hc, hr⟩ := hrefl
  refine ⟨_, isFormCodeSem_imp H hc (isFormCodeSem_bot H),
    fun b hb hcl S hS R hR' a ha U hU t ht => ?_⟩
  rw [hdefP, hr b hb hcl S hS R hR' a ha U hU t ht,
    satIn_imp H (isSetStructure_stage H hR hP hb hS hR') hc (isFormCodeSem_bot H)
      (envOn_stage H hR hP hb hS ha hU ht)]
  exact ⟨fun h hs => absurd hs h, fun h hs => satIn_bot H (h hs)⟩

include hR in
/-- `⊤` is reflected (code `⊥ → ⊥`). -/
theorem top_refl {F : V → V → Prop} : Refl H hP (fun _ => True) F :=
  ⟨_, isFormCodeSem_imp H (isFormCodeSem_bot H) (isFormCodeSem_bot H),
    fun b hb _ S hS R hR' a ha U hU t ht => by
      rw [satIn_imp H (isSetStructure_stage H hR hP hb hS hR') (isFormCodeSem_bot H)
        (isFormCodeSem_bot H) (envOn_stage H hR hP hb hS ha hU ht)]
      exact ⟨fun _ h => h, fun _ => trivial⟩⟩

/-- `⊥` is reflected (code `⊥`). -/
theorem bot_refl {F : V → V → Prop} : Refl H hP (fun _ => False) F :=
  ⟨_, isFormCodeSem_bot H, fun _ _ _ _ _ _ _ _ _ _ _ _ _ => ⟨False.elim, satIn_bot H⟩⟩

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

/-- `P₄` is the negation of `P₀`. -/
def negDefP : Sentence L6 := “∀ t, !P₄ t ↔ ¬!P₀ t”

/-- `F₅` is `F₁`. -/
def eqDefF : Sentence L6 := “∀ a, ∀ g, !F₅ a g ↔ !F₁ a g”

/-- The successor, in the template language. -/
def succL : Semisentence L6 2 := lift succP

/-- `F₅` is the successor function. -/
def succDefF : Sentence L6 := “∀ a, ∀ g, !F₅ a g ↔ !succL a g”

/-- `P₄` is `⊤`. -/
def topDefP : Sentence L6 := “∀ t, !P₄ t ↔ ⊤”

/-- `P₄` is `⊥`. -/
def botDefP : Sentence L6 := “∀ t, !P₄ t ↔ ⊥”

/-- **The negation template.** -/
def negTemplate : Sentence L6 :=
  (totS F₁ ⋏ reflS P₀ F₁ ⋏ negDefP ⋏ eqDefF) 🡒 (totS F₅ ⋏ reflS P₄ F₅)

/-- **Base**: the successor is a total reflection function for `⊤`. -/
def topBase : Sentence L6 := (topDefP ⋏ succDefF) 🡒 (totS F₅ ⋏ reflS P₄ F₅)

/-- **Base**: the successor is a total reflection function for `⊥`. -/
def botBase : Sentence L6 := (botDefP ⋏ succDefF) 🡒 (totS F₅ ⋏ reflS P₄ F₅)

section Readings

variable {M : Type} [Nonempty M] [SetStructure M] [Structure L6 M] [Structure.Eq L6 M]
  [Structure.Mem L6 M]

omit [SetStructure M] [Structure.Eq L6 M] [Structure.Mem L6 M] in
theorem models_eqDefF :
    M↓[L6] ⊧ eqDefF ↔ ∀ a g : M, F₅.Eval ![a, g] Empty.elim ↔ F₁.Eval ![a, g] Empty.elim := by
  simp [models_iff, eqDefF]

theorem models_succDefF [M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory)] :
    M↓[L6] ⊧ succDefF ↔ ∀ a g : M, F₅.Eval ![a, g] Empty.elim ↔
      g = _root_.SetTheory.vsucc (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)) a := by
  simp [models_iff, succDefF, succL,
    eval_succP (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M))]

end Readings

/-- Transport of the invariant along a pointwise equivalence of the function. -/
theorem tot_refl_congr {V : Type*} [SetStructure V] {H : _root_.SetTheory.ZFAxioms (memRel V)}
    {hP : ∀ a, ∃ p, ∀ x, memRel V x p ↔ _root_.SetTheory.Sub (memRel V) x a}
    {P : V → Prop} {F G : V → V → Prop} (hFG : ∀ a g, G a g ↔ F a g)
    (htot : Tot F) (hrefl : Refl H hP P F) : Tot G ∧ Refl H hP P G := by
  have hG : G = F := funext fun a => funext fun g => propext (hFG a g)
  subst hG
  exact ⟨htot, hrefl⟩

theorem negTemplate_provable : templTheory 6 ar6 ⊢ negTemplate := by
  apply templ_provable
  intro M _ _ s _ _ _
  haveI : M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory) := pure_models (k := 6) (arities := ar6)
  simp only [negTemplate, Semantics.Imp.models_imply, Semantics.And.models_and]
  rintro ⟨htot, hrefl, hdefP, hdefF⟩
  rw [models_totS] at htot ⊢
  rw [models_reflS] at hrefl ⊢
  rw [models_eqDefF] at hdefF
  have hdefP' : ∀ t : M, P₄.Eval ![t] Empty.elim ↔ ¬ P₀.Eval ![t] Empty.elim := by
    simpa [models_iff, negDefP] using hdefP
  have hr := neg_step (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M))
    (ConstructibleInterpretation.regular_of_modelsZF (V := M))
    (ConstructibleInterpretation.power_of_modelsZF (V := M)) hrefl hdefP'
  exact tot_refl_congr hdefF htot hr

theorem topBase_provable : templTheory 6 ar6 ⊢ topBase := by
  apply templ_provable
  intro M _ _ s _ _ _
  haveI : M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory) := pure_models (k := 6) (arities := ar6)
  simp only [topBase, Semantics.Imp.models_imply, Semantics.And.models_and]
  rintro ⟨hdefP, hdefF⟩
  rw [models_succDefF] at hdefF
  have hdefP' : ∀ t : M, P₄.Eval ![t] Empty.elim ↔ True := by
    simpa [models_iff, topDefP] using hdefP
  rw [models_totS, models_reflS]
  have hP4 : (fun t : M => P₄.Eval ![t] Empty.elim) = fun _ => True :=
    funext fun t => propext (hdefP' t)
  obtain ⟨htot, hrefl⟩ := tot_refl_congr hdefF
    (tot_succ (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)))
    (top_refl (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M))
      (ConstructibleInterpretation.regular_of_modelsZF (V := M))
      (ConstructibleInterpretation.power_of_modelsZF (V := M)))
  rw [← hP4] at hrefl
  exact ⟨htot, hrefl⟩

theorem botBase_provable : templTheory 6 ar6 ⊢ botBase := by
  apply templ_provable
  intro M _ _ s _ _ _
  haveI : M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory) := pure_models (k := 6) (arities := ar6)
  simp only [botBase, Semantics.Imp.models_imply, Semantics.And.models_and]
  rintro ⟨hdefP, hdefF⟩
  rw [models_succDefF] at hdefF
  have hdefP' : ∀ t : M, P₄.Eval ![t] Empty.elim ↔ False := by
    simpa [models_iff, botDefP] using hdefP
  rw [models_totS, models_reflS]
  have hP4 : (fun t : M => P₄.Eval ![t] Empty.elim) = fun _ => False :=
    funext fun t => propext (hdefP' t)
  obtain ⟨htot, hrefl⟩ := tot_refl_congr hdefF
    (tot_succ (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)))
    (bot_refl (ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M))
      (ConstructibleInterpretation.power_of_modelsZF (V := M)))
  rw [← hP4] at hrefl
  exact ⟨htot, hrefl⟩

end LeanProofs.ZFCinPA.LStepBasic
