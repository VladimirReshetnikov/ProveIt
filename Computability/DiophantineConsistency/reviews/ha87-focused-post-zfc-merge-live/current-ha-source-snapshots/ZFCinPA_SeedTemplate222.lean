import ZFCinPA.TemplateClosure
import ZFCinPA.SeedResources222

set_option autoImplicit false
noncomputable section

/-!
# The seed property for every enlarged relation in every template model

Let `Rf` be any binary formula of any placeholder-enlarged language, read with
the OUTPUT first and the INPUT second. In every model of
`LTemplate.templTheory k arities` the relation it defines has Elliot Glazer's
seed property at every input (`models_seed`). The rank resources of
`SeedResources222.seed_of_closure` are enlarged Separation and Replacement
instances, and the rank-closed limit is a closure point
(`TemplateClosure.closure_point`) of the enlarged function

`γ ↦ succ (γ ∪ ⋃ {least witness rank of x | x ∈ V_γ})`.

No constructibility, choice, or reflection schema is used. Clients state a
fixed template sentence, prove it here semantically, and compile it at
internal matrices with `LTemplate.compileT_provable`.
-/

namespace LeanProofs.ZFCinPA.SeedTemplate222

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.LTemplate
open LeanProofs.ZFCinPA.EnvTransform LeanProofs.ZFCinPA.LPieces LeanProofs.ZFCinPA.LInvariant
open LeanProofs.ZFCinPA.TemplateClosure

variable {k : ℕ} {arities : Fin k → ℕ}

local instance : Language.Mem (setTemplateLanguage k arities) := ⟨Sum.inl Language.Set.Rel.mem⟩

/-! ## Fixed enlarged formulas, parametric in the relation -/

/-- `S = V_a` (`a = #0`, `S = #1`). -/
def isVS : SetTheorySemisentence 2 := piece 1 (SetTheory.BusyBeaver.ZFC.InternalRank.isVF 0 1)

variable (Rf : Semisentence (setTemplateLanguage k arities) 2)

/-- Some output of `x` has rank below `c`. -/
def witS : Semisentence (setTemplateLanguage k arities) 2 :=
  “x c. ∃ S, ∃ y, !(lift isVS) c S ∧ y ∈ S ∧ !Rf y x”

/-- The total least witness rank (the empty ordinal for inputs without outputs). -/
def totS : Semisentence (setTemplateLanguage k arities) 2 :=
  “x c. (!(lift ordP) c ∧ !(witS Rf) x c ∧
      ∀ e, !(lift ordP) e → !(witS Rf) x e → c = e ∨ c ∈ e) ∨
    ((¬∃ y, !Rf y x) ∧ ∀ z, z ∉ c)”

/-- `δ = succ (γ ∪ ⋃ {least witness rank of x | x ∈ V_γ})`. -/
def stepS : Semisentence (setTemplateLanguage k arities) 2 :=
  “γ δ. ∃ S, !(lift isVS) γ S ∧ ∀ z, z ∈ δ ↔
    ((z ∈ γ ∨ ∃ c, (∃ x, x ∈ S ∧ !(totS Rf) x c) ∧ z ∈ c) ∨
      (∀ w, w ∈ z ↔ (w ∈ γ ∨ ∃ c, (∃ x, x ∈ S ∧ !(totS Rf) x c) ∧ w ∈ c)))”

/-- Outputs of inputs from a parameter set (`y = #0`, set `#1`). -/
def outS : Semisentence (setTemplateLanguage k arities) 2 := “y S. ∃ x, x ∈ S ∧ !Rf y x”

/-! ## Semantics -/

section Semantics

open SetTheory.BusyBeaver.ZFC SetTheory.BusyBeaver.ZFC.InternalOrd
  SetTheory.BusyBeaver.ZFC.InternalRank SetTheory.BusyBeaver.ZFC.ZFRank
open LeanProofs.ZFCinPA.CollectionResources254

variable {M : Type} [Nonempty M] [SetStructure M] [s : Structure (setTemplateLanguage k arities) M]
  [Structure.Eq (setTemplateLanguage k arities) M] [Structure.Mem (setTemplateLanguage k arities) M]

/-- `y` is an output of input `x`. -/
abbrev Qr (x y : M) : Prop := Rf.Eval ![y, x] Empty.elim

section Readings

variable [M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory)]

local notation "H0" => ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)

theorem eval_isVS (a S : M) :
    (lift (k := k) (arities := arities) isVS).Eval ![a, S] Empty.elim ↔ IsV H0 a S := by
  rw [eval_lift, isVS, eval_piece, nsat_isVF H0]
  rfl

theorem eval_isVS' (a S : M) : isVS.Eval ![a, S] Empty.elim ↔ IsV H0 a S := by
  rw [isVS, eval_piece, nsat_isVF H0]
  rfl

theorem eval_witS (x c : M) : (witS Rf).Eval ![x, c] Empty.elim ↔ WitnessRank H0 (Qr Rf) x c := by
  simp [witS, WitnessRank, eval_isVS', Qr]

theorem eval_totS (x c : M) : (totS Rf).Eval ![x, c] Empty.elim ↔ TotalRank H0 (Qr Rf) x c := by
  simp [totS, TotalRank, LeastRank, CollectionResources254.Empty, eval_witS, Qr,
    NativeZFContainers254.memRel]

theorem eval_stepS (γ δ : M) : (stepS Rf).Eval ![γ, δ] Empty.elim ↔
    ∃ S, IsV H0 γ S ∧ ∀ z, z ∈ δ ↔
      ((z ∈ γ ∨ ∃ c, (∃ x, x ∈ S ∧ TotalRank H0 (Qr Rf) x c) ∧ z ∈ c) ∨
        (∀ w, w ∈ z ↔ (w ∈ γ ∨ ∃ c, (∃ x, x ∈ S ∧ TotalRank H0 (Qr Rf) x c) ∧ w ∈ c))) := by
  simp [stepS, eval_isVS', eval_totS]

end Readings

omit [Nonempty M] in
omit [Structure.Eq (setTemplateLanguage k arities) M] in
theorem eval_outS (y S : M) : (outS Rf).Eval ![y, S] Empty.elim ↔ ∃ x, x ∈ S ∧ Qr Rf x y := by
  simp [outS, Qr]

variable [M↓[setTemplateLanguage k arities] ⊧* templTheory k arities]

/-- **The seed property of the enlarged relation in every template model.** -/
theorem models_seed (A : M) : KSeed222.SeedProp (memRel M) (Qr Rf) A := by
  haveI hZF : M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory) := pure_models (k := k) (arities := arities)
  have hR := ConstructibleInterpretation.regular_of_modelsZF (V := M)
  set H := ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)
  have hP := ConstructibleInterpretation.power_of_modelsZF (V := M)
  have hSep : ∀ x a : M, ∃ s : M, ∀ c : M, c ∈ s ↔ c ∈ a ∧ WitnessRank H (Qr Rf) x c := by
    intro x a
    obtain ⟨s, hs⟩ := sep_iff (k := k) (arities := arities)
      ((Rewriting.emb (witS Rf) : Semiproposition (setTemplateLanguage k arities) 2) ⇜ ![&0, #0])
      (fun _ => x) a
    refine ⟨s, fun c => (hs c).trans (and_congr_right fun _ => ?_)⟩
    rw [← eval_witS]
    simp
  have htot := totalRank_total H hR hP (Qr Rf) hSep
  have himage : ∀ S : M, ∃ U : M, ∀ c, c ∈ U ↔ ∃ x, x ∈ S ∧ TotalRank H (Qr Rf) x c := by
    intro S
    obtain ⟨U, hU⟩ := repl_iff (k := k) (arities := arities) (Rewriting.emb (totS Rf))
      (fun _ => S) (fun x => by
        obtain ⟨c, hc, hu⟩ := htot x
        exact ⟨c, by simpa [eval_totS] using hc, fun d hd => hu d (by simpa [eval_totS] using hd)⟩) S
    refine ⟨U, fun c => (hU c).trans (exists_congr fun x => and_congr_right fun _ => ?_)⟩
    simpa using eval_totS Rf x c
  have hmk : ∀ γ : M, Ord (memRel M) γ → ∀ S : M, ∃ m, Ord (memRel M) m ∧
      ∀ w, w ∈ m ↔ w ∈ γ ∨ ∃ c, (∃ x, x ∈ S ∧ TotalRank H (Qr Rf) x c) ∧ w ∈ c := by
    intro γ hγ S
    obtain ⟨U, hU⟩ := himage S
    have hUo : ∀ c, c ∈ U → Ord (memRel M) c := fun c hc => by
      obtain ⟨x, -, hT⟩ := (hU c).1 hc
      exact totalRank_ordinal H (Qr Rf) hT
    have hu := ord_vunion H hUo
    refine ⟨_root_.SetTheory.vcup H γ (_root_.SetTheory.vunion H U), ?_, fun w => ?_⟩
    · rcases LStepAnd.vcup_ord H hR hγ hu with h | h <;> rw [h] <;> assumption
    · refine (_root_.SetTheory.vcup_spec H γ _ w).trans (or_congr Iff.rfl ?_)
      refine (_root_.SetTheory.vunion_spec H U w).trans ?_
      exact ⟨fun ⟨c, hwc, hcU⟩ => ⟨c, (hU c).1 hcU, hwc⟩,
        fun ⟨c, hc, hwc⟩ => ⟨c, hwc, (hU c).2 hc⟩⟩
  have hstep_iff : ∀ γ S δ m : M, Ord (memRel M) γ → IsV H γ S →
      (∀ w, w ∈ m ↔ w ∈ γ ∨ ∃ c, (∃ x, x ∈ S ∧ TotalRank H (Qr Rf) x c) ∧ w ∈ c) →
      (FR (stepS Rf) γ δ ↔ δ = _root_.SetTheory.vsucc H m) := by
    intro γ S δ m hγ hS hm
    have key : ∀ z : M, ((z ∈ γ ∨ ∃ c, (∃ x, x ∈ S ∧ TotalRank H (Qr Rf) x c) ∧ z ∈ c) ∨
        (∀ w, w ∈ z ↔ (w ∈ γ ∨ ∃ c, (∃ x, x ∈ S ∧ TotalRank H (Qr Rf) x c) ∧ w ∈ c))) ↔
        z ∈ _root_.SetTheory.vsucc H m := by
      intro z
      refine Iff.trans ?_ (_root_.SetTheory.vsucc_spec H m z).symm
      change _ ↔ z ∈ m ∨ z = m
      rw [hm z]
      refine or_congr Iff.rfl ⟨fun h => ?_, fun h w => by rw [h]; exact hm w⟩
      exact _root_.SetTheory.ZFAxioms.ext H z m fun w => (h w).trans (hm w).symm
    rw [show FR (stepS Rf) γ δ = (stepS Rf).Eval ![γ, δ] Empty.elim from rfl, eval_stepS]
    constructor
    · rintro ⟨S', hS', hz⟩
      have e := isV_unique H hR hγ hS' hS
      subst e
      exact _root_.SetTheory.ZFAxioms.ext H δ _ fun z => (hz z).trans (key z)
    · rintro rfl
      exact ⟨S, hS, fun z => (key z).symm⟩
  have hstepTot : LStepAnd.Tot (FR (stepS Rf) (M := M)) := by
    intro γ hγ
    obtain ⟨S, hS⟩ := isV_exists H hR hP hγ
    obtain ⟨m, hmo, hm⟩ := hmk γ hγ S
    have hδo : Ord (memRel M) (_root_.SetTheory.vsucc H m) := ord_succ H hmo
    have hγδ : γ ∈ _root_.SetTheory.vsucc H m := by
      rcases le_of_sub H hR hγ hmo (fun w hw => (hm w).2 (Or.inl hw)) with h | h
      · rw [h]; exact _root_.SetTheory.vsucc_self H m
      · exact (_root_.SetTheory.vsucc_spec H m γ).2 (Or.inl h)
    exact ⟨_, hδo, hγδ, (hstep_iff γ S _ m hγ hS hm).2 rfl,
      fun δ' hδ' => (hstep_iff γ S δ' m hγ hS hm).1 hδ'⟩
  have hcl : ∀ α, Ord (memRel M) α → ∃ β, IsLim (memRel M) β ∧ α ∈ β ∧
      ∀ γ, γ ∈ β → ∀ S, IsV H γ S → ∀ x, x ∈ S → ∀ c, TotalRank H (Qr Rf) x c → c ∈ β := by
    intro α hα
    obtain ⟨β, hβ, hαβ, hclo⟩ := closure_point (stepS Rf) hstepTot α hα
    refine ⟨β, hβ, hαβ, fun γ hγ S hS x hx c hc => ?_⟩
    have hγo : Ord (memRel M) γ := ord_of_mem hβ.1 hγ
    obtain ⟨m, hmo, hm⟩ := hmk γ hγo S
    have hδβ := hclo γ hγ _ ((hstep_iff γ S _ m hγo hS hm).2 rfl)
    have hco : Ord (memRel M) c := totalRank_ordinal H (Qr Rf) hc
    have hcm : c = m ∨ c ∈ m :=
      le_of_sub H hR hco hmo (fun w hw => (hm w).2 (Or.inr ⟨c, ⟨x, hx, hc⟩, hw⟩))
    have hcδ : c ∈ _root_.SetTheory.vsucc H m := by
      rcases hcm with h | h
      · rw [h]; exact _root_.SetTheory.vsucc_self H m
      · exact (_root_.SetTheory.vsucc_spec H m c).2 (Or.inl h)
    exact hβ.1.1 _ hδβ c hcδ
  have hOut : ∀ S : M, ∃ C : M, ∀ y : M, y ∈ C ↔ y ∈ S ∧ ∃ x, x ∈ S ∧ Qr Rf x y := by
    intro S
    obtain ⟨C, hC⟩ := sep_iff (k := k) (arities := arities)
      ((Rewriting.emb (outS Rf) : Semiproposition (setTemplateLanguage k arities) 2) ⇜ ![#0, &0])
      (fun _ => S) S
    refine ⟨C, fun y => (hC y).trans (and_congr_right fun _ => ?_)⟩
    rw [← eval_outS]
    simp
  exact SeedResources222.seed_of_closure H hR hP (Qr Rf) hSep hcl hOut A

end Semantics

end LeanProofs.ZFCinPA.SeedTemplate222
