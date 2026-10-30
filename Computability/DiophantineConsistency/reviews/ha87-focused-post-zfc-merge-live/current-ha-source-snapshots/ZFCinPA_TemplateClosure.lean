import ZFCinPA.LClosure

set_option autoImplicit false
noncomputable section

/-!
# Closure points for an arbitrary enlarged class function

`LClosure.closure_point` is stated for the placeholder `F₅` of the driver's
six-placeholder language. The same argument works for ANY enlarged binary
formula `Fs` of ANY template language: every Separation/Replacement instance it
uses is for an enlarged formula built from `Fs`, available in every model of
`templTheory k arities` through `LTemplate.sep_iff`/`repl_iff`. This module
restates the four resource formulas with `Fs` in place of `F₅` and proves
`closure_point`: if `Fs` defines a total function on ordinals above its
argument, then above every ordinal there is a nonzero limit closed under it.
-/

namespace LeanProofs.ZFCinPA.TemplateClosure

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.LTemplate
open LeanProofs.ZFCinPA.EnvTransform LeanProofs.ZFCinPA.LPieces LeanProofs.ZFCinPA.LInvariant
open LeanProofs.ZFCinPA.LStepAnd LeanProofs.ZFCinPA.LStepBasic LeanProofs.ZFCinPA.LStepAtom
open LeanProofs.ZFCinPA.LIterate LeanProofs.ZFCinPA.LClosure

variable {k : ℕ} {arities : Fin k → ℕ}

local instance : Language.Mem (setTemplateLanguage k arities) := ⟨Sum.inl Language.Set.Rel.mem⟩

variable (Fs : Semisentence (setTemplateLanguage k arities) 2)

/-- `y = succ (x ∪ ⋃ Fs[x])`. -/
def hstepG : Semisentence (setTemplateLanguage k arities) 2 :=
  “x y. ∃ m, (∀ w, w ∈ m ↔ w ∈ x ∨ ∃ a, a ∈ x ∧ ∃ g, !Fs a g ∧ w ∈ g) ∧ ∀ z, z ∈ y ↔ z ∈ m ∨ z = m”

/-- `f` is a chain of length `n + 1` from `α`. -/
def chainG : Semisentence (setTemplateLanguage k arities) 3 :=
  “α n f. (∃ s, !(lift succP) n s ∧ !(lift funOnP) f s) ∧
    (∃ e, (∀ w, w ∉ e) ∧ !(lift pmemS) f e α) ∧
    (∀ k, ∀ x, !(lift pmemS) f k x → !(lift ordP) x) ∧
    ∀ k, k ∈ n → ∀ x, ∀ y, !(lift pmemS) f k x →
      (∃ s, !(lift succP) k s ∧ !(lift pmemS) f s y) → !(hstepG Fs) x y”

def chainExG : Semisentence (setTemplateLanguage k arities) 2 := “n α. ∃ f, !(chainG Fs) α n f”

def agreeG : Semisentence (setTemplateLanguage k arities) 3 :=
  “k f f'. ∀ x, ∀ x', !(lift pmemS) f k x → !(lift pmemS) f' k x' → x = x'”

def imgG : Semisentence (setTemplateLanguage k arities) 2 :=
  “a g. (!(lift ordP) a ∧ !Fs a g) ∨ (¬!(lift ordP) a ∧ ∀ z, z ∉ g)”

def orbG : Semisentence (setTemplateLanguage k arities) 3 :=
  “n γ α. (!(lift natP) n ∧ ∃ f, !(chainG Fs) α n f ∧ !(lift pmemS) f n γ) ∨
    (¬!(lift natP) n ∧ ∀ z, z ∉ γ)”

section Readings

open SetTheory.BusyBeaver.ZFC.InternalOrd LeanProofs.BoundedZFCConsistency

variable {M : Type} [Nonempty M] [SetStructure M] [Structure (setTemplateLanguage k arities) M]
  [Structure.Eq (setTemplateLanguage k arities) M]
  [Structure.Mem (setTemplateLanguage k arities) M] [M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory)]

local notation "HM" => ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)

/-- The formula's function, as a relation. -/
abbrev FR (a g : M) : Prop := Fs.Eval ![a, g] Empty.elim

omit [Nonempty M] [M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory)] in
theorem eval_hstepG (x y : M) : (hstepG Fs).Eval ![x, y] Empty.elim ↔ HStep (FR Fs) x y := by
  simp [hstepG, HStep]

theorem eval_chainG (α n f : M) :
    (chainG Fs).Eval ![α, n, f] Empty.elim ↔ Chain HM (FR Fs) α n f := by
  simp only [chainG, Chain]
  simp [eval_succP HM, eval_funOnP HM, eval_pmemS HM, eval_hstepG, empty_iff]

omit [M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory)] in
theorem eval_imgG (a g : M) :
    (imgG Fs).Eval ![a, g] Empty.elim ↔
      (Ord (memRel M) a ∧ FR Fs a g) ∨ (¬ Ord (memRel M) a ∧ ∀ z, z ∉ g) := by
  simp [imgG]

theorem eval_chainExG (n α : M) :
    (chainExG Fs).Eval ![n, α] Empty.elim ↔ ∃ f, Chain HM (FR Fs) α n f := by
  simp [chainExG, eval_chainG]

theorem eval_agreeG (j f f' : M) :
    (agreeG (k := k) (arities := arities)).Eval ![j, f, f'] Empty.elim ↔
      ∀ x x', _root_.SetTheory.kpair HM j x ∈ f → _root_.SetTheory.kpair HM j x' ∈ f' → x = x' := by
  simp [agreeG, eval_pmemS HM]

theorem eval_orbG (n γ α : M) :
    (orbG Fs).Eval ![n, γ, α] Empty.elim ↔
      (n ∈ _root_.SetTheory.omegaV HM ∧ ∃ f, Chain HM (FR Fs) α n f ∧
        _root_.SetTheory.kpair HM n γ ∈ f) ∨
      (n ∉ _root_.SetTheory.omegaV HM ∧ ∀ z, z ∉ γ) := by
  simp [orbG, eval_natP HM, eval_chainG, eval_pmemS HM]

end Readings

section Closure

open SetTheory.BusyBeaver.ZFC.InternalOrd LeanProofs.BoundedZFCConsistency

variable {M : Type} [Nonempty M] [SetStructure M] [s : Structure (setTemplateLanguage k arities) M]
  [Structure.Eq (setTemplateLanguage k arities) M]
  [Structure.Mem (setTemplateLanguage k arities) M]
  [M↓[setTemplateLanguage k arities] ⊧* templTheory k arities]

/-- **Closure points exist** for every enlarged total function on ordinals. -/
theorem closure_point :
    haveI : M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory) := pure_models (k := k) (arities := arities)
    Tot (FR Fs (M := M)) → ∀ α : M, Ord (memRel M) α →
      ∃ β, IsLim (memRel M) β ∧ α ∈ β ∧ ∀ a, a ∈ β → ∀ g, FR Fs a g → g ∈ β := by
  haveI : M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory) := pure_models (k := k) (arities := arities)
  intro htot α hα
  have hR := ConstructibleInterpretation.regular_of_modelsZF (V := M)
  set H := ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)
  have himg : ∀ x : M, Ord (memRel M) x → ∃ Y : M, ∀ g, g ∈ Y ↔ ∃ a, a ∈ x ∧ FR Fs a g := by
    intro x hx
    have hfun : ∀ a : M, ∃! g, (imgG Fs).Eval ![a, g] Empty.elim := by
      intro a
      by_cases ha : Ord (memRel M) a
      · obtain ⟨g, -, -, hFg, u⟩ := htot a ha
        refine ⟨g, (eval_imgG Fs a g).2 (Or.inl ⟨ha, hFg⟩), fun g' hg' => ?_⟩
        rcases (eval_imgG Fs a g').1 hg' with ⟨-, h⟩ | ⟨h, -⟩
        · exact u g' h
        · exact absurd ha h
      · refine ⟨_root_.SetTheory.vempty H,
          (eval_imgG Fs a _).2 (Or.inr ⟨ha, fun z => _root_.SetTheory.vempty_spec H z⟩),
          fun g' hg' => ?_⟩
        rcases (eval_imgG Fs a g').1 hg' with ⟨h, -⟩ | ⟨-, h⟩
        · exact absurd h ha
        · exact (empty_iff g').1 h
    obtain ⟨Y, hY⟩ := repl_iff (k := k) (arities := arities) (Rewriting.emb (imgG Fs))
      (fun _ => x) (by simpa using hfun) x
    refine ⟨Y, fun g => ?_⟩
    have hY' := hY g
    simp only [Semiformula.eval_emb] at hY'
    rw [hY']
    refine exists_congr fun a => and_congr_right fun hax => ?_
    rw [eval_imgG]
    have hao : Ord (memRel M) a := ord_of_mem hx hax
    exact ⟨fun h => h.elim (fun h => h.2) (fun h => absurd hao h.1), fun h => Or.inl ⟨hao, h⟩⟩
  have hsepC : ∃ S : M, ∀ n, n ∈ S ↔ n ∈ _root_.SetTheory.omegaV H ∧
      ∃ f, Chain H (FR Fs) α n f := by
    obtain ⟨S, hS⟩ := sep_iff (k := k) (arities := arities)
      ((Rewriting.emb (chainExG Fs) : Semiproposition (setTemplateLanguage k arities) 2) ⇜ ![#0, &0])
      (fun _ => α) (_root_.SetTheory.omegaV H)
    refine ⟨S, fun n => (hS n).trans (and_congr_right fun _ => ?_)⟩
    rw [← eval_chainExG]
    simp
  have hsepA : ∀ f f' : M, ∃ S : M, ∀ j, j ∈ S ↔ j ∈ _root_.SetTheory.omegaV H ∧
      ∀ x x', _root_.SetTheory.kpair H j x ∈ f → _root_.SetTheory.kpair H j x' ∈ f' → x = x' := by
    intro f f'
    obtain ⟨S, hS⟩ := sep_iff (k := k) (arities := arities)
      ((Rewriting.emb (agreeG (k := k) (arities := arities)) :
        Semiproposition (setTemplateLanguage k arities) 3) ⇜ ![#0, &0, &1])
      (fun i => if i = 0 then f else f') (_root_.SetTheory.omegaV H)
    refine ⟨S, fun j => (hS j).trans (and_congr_right fun _ => ?_)⟩
    rw [← eval_agreeG (k := k) (arities := arities)]
    simp
  have horb : ∀ n : M, ∃! γ, (orbG Fs).Eval ![n, γ, α] Empty.elim := by
    intro n
    by_cases hn : n ∈ _root_.SetTheory.omegaV H
    · obtain ⟨f, hf⟩ := chain_exists H hR htot himg hα hsepC n hn
      obtain ⟨γ, hγ⟩ := hf.1.2.1 n (_root_.SetTheory.vsucc_self H n)
      refine ⟨γ, (eval_orbG Fs n γ α).2 (Or.inl ⟨hn, f, hf, hγ⟩), fun γ' hγ' => ?_⟩
      rcases (eval_orbG Fs n γ' α).1 hγ' with ⟨-, f', hf', hγ'f⟩ | ⟨h, -⟩
      · exact chain_agree H hf' hf hn hn (hsepA f' f) n hn γ' γ hγ'f hγ
      · exact absurd hn h
    · refine ⟨_root_.SetTheory.vempty H,
        (eval_orbG Fs n _ α).2 (Or.inr ⟨hn, fun z => _root_.SetTheory.vempty_spec H z⟩),
        fun γ' hγ' => ?_⟩
      rcases (eval_orbG Fs n γ' α).1 hγ' with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd h hn
      · exact (empty_iff γ').1 h
  obtain ⟨O, hO⟩ := repl_iff (k := k) (arities := arities)
    ((Rewriting.emb (orbG Fs) : Semiproposition (setTemplateLanguage k arities) 3) ⇜ ![#0, #1, &0])
    (fun _ => α) (fun n => by simpa using horb n) (_root_.SetTheory.omegaV H)
  refine orbit_closure H hR htot himg hα hsepC hsepA (O := O) fun γ => ?_
  have hO' := hO γ
  simp only [Rewriting.subst, Semiformula.eval_substs] at hO'
  rw [hO']
  refine exists_congr fun n => ?_
  constructor
  · rintro ⟨hn, h⟩
    have h' : (orbG Fs).Eval ![n, γ, α] Empty.elim := by simpa using h
    rcases (eval_orbG Fs n γ α).1 h' with ⟨-, hc⟩ | ⟨h, -⟩
    · exact ⟨hn, hc⟩
    · exact absurd hn h
  · rintro ⟨hn, hc⟩
    refine ⟨hn, ?_⟩
    have h' : (orbG Fs).Eval ![n, γ, α] Empty.elim := (eval_orbG Fs n γ α).2 (Or.inl ⟨hn, hc⟩)
    simpa using h'

end Closure

end LeanProofs.ZFCinPA.TemplateClosure
