import ZFCinPA.LMatch

set_option autoImplicit false
noncomputable section

/-!
# The glue templates

Fixed sentences over `GL`, the set language with eight unary placeholders
`G₀ … G₇`, proved in every model of the template theory. Compiled at internal
codes, they carry out the steps of the internal inductions that link
`envForm` with `relativize`:

* `funTemplate`: matching environments are functional;
* `slot0Template`, `slotSTemplate`: a matching environment holds `&a` at the
  slot named by the numeral chain of `a`.

Throughout, `mpBody` is the successor clause of `LMatch.mVal`:
`∃t₁ ∃z (G₂ z ∧ t = econs z t₁ ∧ G₀ t₁)`.
-/

namespace LeanProofs.ZFCinPA.LGlueT

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.LTemplate
open LeanProofs.ZFCinPA.LInvariant LeanProofs.ZFCinPA.EnvTransform
open LeanProofs.ZFCinPA.NumeralOmega (numZeroS succRelS)

abbrev arG : Fin 8 → ℕ := fun _ ↦ 1
abbrev GL := setTemplateLanguage 8 arG

local instance : Language.Mem GL := ⟨Sum.inl Language.Set.Rel.mem⟩

/-- The `i`-th placeholder, read at `#0`. -/
def G (i : Fin 8) : Semisentence GL 1 := .rel (placeholderRel i) ![#0]

/-- The successor clause of the matching code, over `G₀` (previous) and `G₂` (`z = &0`). -/
def mpBody : Semisentence GL 1 := “t. ∃ t₁, ∃ z, !(G 2) z ∧ !(lift econsS) t z t₁ ∧ !(G 0) t₁”

/-- `G₁` is the successor matching predicate. -/
def mpDef : Sentence GL :=
  “∀ t, !(G 1) t ↔ ∃ t₁, ∃ z, !(G 2) z ∧ !(lift econsS) t z t₁ ∧ !(G 0) t₁”

/-- Matching environments of `G i` are functional. -/
def funM (i : Fin 8) : Sentence GL := “∀ t, ¬!(G i) t ∨ !(lift LMatch.funcS) t”

/-- The slot statement: every `G i`-environment holds a `G k`-element at the
`G j`-numeral. -/
def slotS (i j k : Fin 8) : Sentence GL :=
  “∀ t, ¬!(G i) t ∨ ∀ n, ¬!(G j) n ∨ ∃ x, !(G k) x ∧ !(lift LClosure.pmemS) t n x”

/-- `G j` is the numeral zero. -/
def zeroDef (j : Fin 8) : Sentence GL := “∀ n, !(G j) n ↔ !(lift numZeroS) n”

/-- `G j'` is the successor numeral of `G j`, literally the shape of `numChainQ_succ`. -/
def succBody (j : Fin 8) : Semisentence GL 1 := ∃⁰ ((G j ⇜ ![#0]) ⋏ lift succRelS)

def succDef (j j' : Fin 8) : Sentence GL :=
  “∀ n, !(G j') n ↔ ∃ m, !(G j) m ∧ !(lift succRelS) m n”

/-- Every element of the `G j`-numeral is a natural number. -/
def natN (j : Fin 8) : Sentence GL := “∀ m, !(G j) m → !(lift LStepAtom.natP) m”

/-- **Matching environments stay functional.** -/
def funTemplate : Sentence GL := (funM 0 ⋏ mpDef) 🡒 funM 1

/-- **Slot zero holds `&0`.** -/
def slot0Template : Sentence GL := (funM 0 ⋏ mpDef ⋏ zeroDef 3) 🡒 slotS 1 3 2

/-- **The slot step.** -/
def slotSTemplate : Sentence GL :=
  (slotS 0 3 4 ⋏ funM 0 ⋏ mpDef ⋏ succDef 3 5 ⋏ natN 3) 🡒 slotS 1 5 4

section Readings

variable {V : Type*} [SetStructure V] (H : _root_.SetTheory.ZFAxioms (memRel V))

theorem eval_funcS (t : V) (ε : Empty → V) :
    LMatch.funcS.Eval (s := SetTheory.standardStructure V) ![t] ε ↔
      ∀ x y y', _root_.SetTheory.kpair H x y ∈ t → _root_.SetTheory.kpair H x y' ∈ t → y = y' := by
  simp [LMatch.funcS, LClosure.eval_pmemS H, Semiformula.Operator.eq_def]

end Readings

section Models

variable {M : Type} [Nonempty M] [SetStructure M] [Structure GL M] [Structure.Eq GL M]
  [Structure.Mem GL M] [M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory)]

local notation "HM" => ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)

local notation "PH" i:max x:max => Structure.rel (L := GL) (M := M) (placeholderRel i) ![x]

/-- Functionality of an environment. -/
def Fun (t : M) : Prop :=
  ∀ x y y', _root_.SetTheory.kpair HM x y ∈ t → _root_.SetTheory.kpair HM x y' ∈ t → y = y'

theorem models_funM (i : Fin 8) :
    M↓[GL] ⊧ funM i ↔ ∀ t : M, PH i t → Fun t := by
  simp only [models_iff, funM]
  simp [G, eval_funcS HM, Fun, or_iff_not_imp_left]

theorem models_mpDef (hfun : ∀ t : M, PH 0 t → Fun t) :
    M↓[GL] ⊧ mpDef ↔ ∀ t : M, PH 1 t ↔
      ∃ t₁, PH 0 t₁ ∧ ∃ z, PH 2 z ∧
        t = LeanProofs.BoundedZFCConsistency.econs HM z t₁ := by
  simp only [models_iff, mpDef]
  simp [G]
  refine forall_congr' fun t => iff_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨t₁, z, hz, he, h0⟩
    exact ⟨t₁, h0, z, hz, (LStepExT.eval_econsS t z t₁ (hfun t₁ h0)).1 he⟩
  · rintro ⟨t₁, h0, z, hz, he⟩
    exact ⟨t₁, z, hz, (LStepExT.eval_econsS t z t₁ (hfun t₁ h0)).2 he, h0⟩

theorem models_slotS (i j k : Fin 8) :
    M↓[GL] ⊧ slotS i j k ↔ ∀ t : M, PH i t → ∀ n : M,
      PH j n → ∃ x, PH k x ∧
        _root_.SetTheory.kpair HM n x ∈ t := by
  simp [models_iff, slotS, G, LClosure.eval_pmemS HM, or_iff_not_imp_left]

end Models

theorem funTemplate_provable : templTheory 8 arG ⊢ funTemplate := by
  apply templ_provable
  intro M _ _ s _ _ _
  haveI : M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory) := pure_models (k := 8) (arities := arG)
  set H := ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)
  simp only [funTemplate, Semantics.Imp.models_imply, Semantics.And.models_and]
  rintro ⟨hf, hdef⟩
  rw [models_funM] at hf ⊢
  rw [models_mpDef hf] at hdef
  intro t ht
  obtain ⟨t₁, h0, z, -, rfl⟩ := (hdef t).1 ht
  exact LeanProofs.BoundedZFCConsistency.econs_functional H (hf t₁ h0) z

theorem slot0Template_provable : templTheory 8 arG ⊢ slot0Template := by
  apply templ_provable
  intro M _ _ s _ _ _
  haveI : M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory) := pure_models (k := 8) (arities := arG)
  set H := ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)
  simp only [slot0Template, Semantics.Imp.models_imply, Semantics.And.models_and]
  rintro ⟨hf, hdef, hzero⟩
  rw [models_funM] at hf
  rw [models_mpDef hf] at hdef
  simp only [models_iff, zeroDef] at hzero
  simp [G, LNumOK.eval_numZeroS] at hzero
  rw [models_slotS]
  intro t ht n hn
  obtain ⟨t₁, h0, z, hz, rfl⟩ := (hdef t).1 ht
  have hn0 : n = _root_.SetTheory.vempty H := (LClosure.empty_iff n).1 ((hzero n).1 hn)
  refine ⟨z, hz, ?_⟩
  rw [hn0]
  exact (LeanProofs.BoundedZFCConsistency.econs_spec H (hf t₁ h0) z _).2 (Or.inl rfl)

theorem slotSTemplate_provable : templTheory 8 arG ⊢ slotSTemplate := by
  apply templ_provable
  intro M _ _ s _ _ _
  haveI : M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory) := pure_models (k := 8) (arities := arG)
  set H := ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)
  simp only [slotSTemplate, Semantics.Imp.models_imply, Semantics.And.models_and]
  rintro ⟨hslot, hf, hdef, hsucc, hnat⟩
  rw [models_funM] at hf
  rw [models_mpDef hf] at hdef
  rw [models_slotS] at hslot ⊢
  simp only [models_iff, succDef] at hsucc
  simp [G, LNumOK.eval_succRelS] at hsucc
  simp only [models_iff, natN] at hnat
  simp [G, LStepAtom.eval_natP H] at hnat
  intro t ht n hn
  obtain ⟨t₁, h0, z, -, rfl⟩ := (hdef t).1 ht
  obtain ⟨m, hm, hmn⟩ := (hsucc n).1 hn
  obtain ⟨x, hx, hmx⟩ := hslot t₁ h0 m hm
  have hn' : n = _root_.SetTheory.vsucc H m := _root_.SetTheory.ZFAxioms.ext H _ _ fun w =>
    (hmn w).trans (_root_.SetTheory.vsucc_spec H m w).symm
  refine ⟨x, hx, ?_⟩
  rw [hn']
  exact (LeanProofs.BoundedZFCConsistency.econs_spec H (hf t₁ h0) z _).2
    (Or.inr ⟨m, hnat m hm, x, hmx, rfl⟩)

end LeanProofs.ZFCinPA.LGlueT
