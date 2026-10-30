import ZFCinPA.ModelCodedFreeRenaming
import ZFCinPA.OpenedClosure
import ZFCinPA.FiniteTheoryRecognizer

/-!
Actual ZF/ZFC axiom invariance under represented free renaming. The finite
axiom recognizers contain only quotes of ordinary sentences. The two schema
recognizers explicitly supply a shift-fixed body and an internal number of
universal binders. This uses those literal witnesses; it does not postulate
semantic closure of a theory or a proof selector.
-/
namespace LeanProofs.ZFCinPA.ModelCodedRenamingAxioms
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.ModelCodedFreeRenaming
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

lemma shift_qqAlls {body : V} (hb : IsUFormula L body) (count : V) :
    shift L (qqAlls body count) = qqAlls (shift L body) count :=
  OpenedClosure.shift_qqAlls hb count

lemma sentence_quote_shift_fixed (sentence : Sentence L) :
    shift L (⌜sentence⌝ : V) = ⌜sentence⌝ := by
  have hs : Rewriting.shift (sentence : Proposition L) = (sentence : Proposition L) := by
    have h := FirstOrder.Semiformula.rew_univCl' (sentence : Proposition L) Rew.shift
    simp only [FirstOrder.Semiformula.senetnce_univCl'_eq_self] at h
    exact h
  rw [FirstOrder.Sentence.quote_def,←FirstOrder.Semiformula.quote_shift,hs]

lemma singleton_class_iff (sentence : Sentence L) (p : V) :
    (V ⊧/![p] (Theory.Δ₁.singleton sentence).ch.val) ↔ p = (⌜sentence⌝ : V) := FiniteTheoryRecognizer.singleton_class_iff sentence p

/-- The finite recognizer cannot acquire new nonstandard axiom codes. -/
lemma ofList_class_iff (sentences : List (Sentence L)) (p : V) :
    (V ⊧/![p] (Theory.Δ₁.ofList sentences).ch.val) ↔
      ∃ sentence ∈ sentences, p = (⌜sentence⌝ : V) := FiniteTheoryRecognizer.ofList_class_iff sentences p

lemma ofList_class_shift_fixed (sentences : List (Sentence L)) {p : V} :
    (V ⊧/![p] (Theory.Δ₁.ofList sentences).ch.val) → shift L p = p := by
  intro hp
  rcases (ofList_class_iff sentences p).mp hp with ⟨sentence,_,rfl⟩
  exact sentence_quote_shift_fixed sentence

lemma ofFinite_class_shift_fixed (T : Theory L) (finite : Set.Finite T) {p : V} :
    (V ⊧/![p] (Theory.Δ₁.ofFinite T finite).ch.val) → shift L p = p := by
  change (V ⊧/![p] (Theory.Δ₁.ofList finite.toFinset.toList).ch.val) → _
  exact ofList_class_shift_fixed (V := V) finite.toFinset.toList (p := p)

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma union_class_iff (T U : Theory L) [T.Δ₁] [U.Δ₁] (p : V) :
    p ∈ (T ∪ U).Δ₁Class ↔ p ∈ T.Δ₁Class ∨ p ∈ U.Δ₁Class := FiniteTheoryRecognizer.union_class_iff T U p

/-- Every literal schema recognizer supplies the needed closed syntax. -/
lemma schemaRecognizer_shift_fixed {arity : Nat} {Fval : V → V} {p : V}
    (hp : SchemaRecognizer L arity Fval p) : shift L p = p := by
  rcases hp with ⟨count,_,body,_,rfl,hbody,hfixed,_,_⟩
  rw [shift_qqAlls hbody,hfixed]

lemma zf_axiom_shift_fixed {p : V} (hp : p ∈ (𝗭𝗙 : SetTheory).Δ₁Class) :
    shift ℒₛₑₜ p = p := by
  have hcases : p ∈ (𝗘𝗤 ℒₛₑₜ : SetTheory).Δ₁Class ∨
      p ∈ zfFixed.Δ₁Class ∨ p ∈ separationTheory.Δ₁Class ∨
      p ∈ replacementTheory.Δ₁Class := by
    change p ∈ (𝗘𝗤 ℒₛₑₜ ∪ zfFixed ∪ separationTheory ∪ replacementTheory : SetTheory).Δ₁Class at hp
    simpa only [union_class_iff,or_assoc] using hp
  rcases hcases with heq | hfixed | hsep | hrep
  · exact ofFinite_class_shift_fixed (𝗘𝗤 ℒₛₑₜ : SetTheory) Theory.EqAxiom.finite heq
  · change (V ⊧/![p] (Theory.Δ₁.ofList
      [Axiom.empty,Axiom.extentionality,Axiom.pairing,Axiom.union,
       Axiom.power,Axiom.infinity,Axiom.foundation]).ch.val) at hfixed
    exact ofList_class_shift_fixed _ hfixed
  · have h : SepR p := by
      change (V ⊧/![p] sepCh.val) at hsep
      simpa using hsep
    exact schemaRecognizer_shift_fixed h
  · have h : RepR p := by
      change (V ⊧/![p] repCh.val) at hrep
      simpa using hrep
    exact schemaRecognizer_shift_fixed h

lemma zfc_axiom_shift_fixed {p : V} (hp : p ∈ (𝗭𝗙𝗖 : SetTheory).Δ₁Class) :
    shift ℒₛₑₜ p = p := by
  change p ∈ ((𝗭𝗙 : SetTheory) ∪ 𝗔𝗖).Δ₁Class at hp
  rcases (union_class_iff (𝗭𝗙 : SetTheory) 𝗔𝗖 p).mp hp with hzf | hac
  · exact zf_axiom_shift_fixed hzf
  · have h : p = (⌜Axiom.choice⌝ : V) :=
      (singleton_class_iff Axiom.choice p).mp hac
    rw [h]
    exact sentence_quote_shift_fixed Axiom.choice

/-- Actual axiom closure, not a premise about arbitrary semantic schemas. -/
theorem zf_axiom_rename (chosen level offset : V) {p : V}
    (hformula : IsFormula ℒₛₑₜ p) (hp : p ∈ (𝗭𝗙 : SetTheory).Δ₁Class) :
    rename ℒₛₑₜ chosen level offset p = p :=
  rename_of_shift_fixed chosen level offset hformula.isUFormula (zf_axiom_shift_fixed hp)
theorem zfc_axiom_rename (chosen level offset : V) {p : V}
    (hformula : IsFormula ℒₛₑₜ p) (hp : p ∈ (𝗭𝗙𝗖 : SetTheory).Δ₁Class) :
    rename ℒₛₑₜ chosen level offset p = p :=
  rename_of_shift_fixed chosen level offset hformula.isUFormula (zfc_axiom_shift_fixed hp)

theorem zf_rename_mem (chosen level offset : V) {p : V}
    (hformula : IsFormula ℒₛₑₜ p) (hp : p ∈ (𝗭𝗙 : SetTheory).Δ₁Class) :
    rename ℒₛₑₜ chosen level offset p ∈ (𝗭𝗙 : SetTheory).Δ₁Class := by
  rw [zf_axiom_rename chosen level offset hformula hp]
  exact hp
theorem zfc_rename_mem (chosen level offset : V) {p : V}
    (hformula : IsFormula ℒₛₑₜ p) (hp : p ∈ (𝗭𝗙𝗖 : SetTheory).Δ₁Class) :
    rename ℒₛₑₜ chosen level offset p ∈ (𝗭𝗙𝗖 : SetTheory).Δ₁Class := by
  rw [zfc_axiom_rename chosen level offset hformula hp]
  exact hp

end LeanProofs.ZFCinPA.ModelCodedRenamingAxioms
