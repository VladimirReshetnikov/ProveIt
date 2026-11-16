import PA194SourceIsoFacts
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
/-!
# Sums and products exist, in a structure

* `succ_pred_unique`: a successor of `x` that is an ordinal representative has no other
  predecessor.
* `extend_prefix`: a trace graph with domain `x ∪ {x}` extended by an entry at a successor
  `y` of `x` has domain `y ∪ {y}`, and stays functional with values in the domain.
* `add_total`: every two ordinal representatives have a sum that is one, by
  `letter_induction` on the first: a one-entry graph for an empty first summand, and the
  extension of a trace by the successor of its value.
* `mul_total`: the same for products, the new value being a sum of the old value and the
  second factor.
-/
namespace PA194GuardedCompiler
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PA194Schematic

def psiA1 : SF 1 := ∀⁰ (sDom #1 🡒 sDom #0 🡒 (∃⁰ (sDom #0 ⋏ sAdd #2 #1 #0)))
def psiM1 : SF 1 := ∀⁰ (sDom #1 🡒 sDom #0 🡒 (∃⁰ (sDom #0 ⋏ sMul #2 #1 #0)))

section semantics
variable {M : Type} [s : Structure NL M]

theorem ev_psiA1 (x : M) : ev ![x] psiA1 ↔
    ∀ c : M, mD x → mD c → ∃ w : M, mD w ∧ mA x c w := by
  simp [psiA1]
theorem ev_psiM1 (x : M) : ev ![x] psiM1 ↔
    ∀ c : M, mD x → mD c → ∃ w : M, mD w ∧ mMu x c w := by
  simp [psiM1]

end semantics
end PA194GuardedCompiler

namespace PA194SourceModel
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PA194ModelLogic PA194BindSource PA194Schematic PA194GuardedCompiler
open M6.PA.RelationalSource

attribute [local instance] PA194ModelLogic.sourceLanguageAdjTheory

section model
variable {N : Type} [Nonempty N] [s : Structure SourceL N] [Structure.Eq SourceL N]

def PA1 (x : N) : Prop := ∀ c : N, SDom x → SDom c → ∃ w : N, SDom w ∧ SAdd x c w
def PM1 (x : N) : Prop := ∀ c : N, SDom x → SDom c → ∃ w : N, SDom w ∧ SMul x c w

theorem ev_psiA1_iff (f : ℕ → N) (x : N) :
    @ev N (sourceLetters s f) 1 ![x] psiA1 ↔ PA1 x := by
  rw [@ev_psiA1 N (sourceLetters s f) x]
  simp only [mD_iff, mA_iff, PA1]
theorem ev_psiM1_iff (f : ℕ → N) (x : N) :
    @ev N (sourceLetters s f) 1 ![x] psiM1 ↔ PM1 x := by
  rw [@ev_psiM1 N (sourceLetters s f) x]
  simp only [mD_iff, mMu_iff, PM1]

theorem noEdge_empty {e a c : N} (he : SZero e) : ¬SEdge e a c := by
  rintro ⟨p, hp, _⟩
  exact he p hp

theorem succ_pred_unique {x y c : N} (dy : SDom y) (sxy : SSucc x y) (scy : SSucc c y) :
    c = x := by
  have hx : Mem x y := (sxy x).mpr (Or.inr rfl)
  rcases (sxy c).mp ((scy c).mpr (Or.inr rfl)) with h | h
  · rcases (scy x).mp hx with h' | h'
    · exact absurd (dy.1.2.1 x hx c x ⟨h, h'⟩) (dy.2 x hx)
    · exact h'.symm
  · exact h

variable (hsep : ∀ (p : Semiproposition SourceL 1) (f : ℕ → N),
  FirstOrder.Semiformula.Evalf (s := s) f (separationFormula p))
variable (hwa : N↓[SourceL] ⊧ sourceWeakAdjunction)
include hsep hwa

/-- A graph with the single entry for `z` and `c`, for an empty `z`: its domain is
`z ∪ {z}`, it is functional, and no entry has a first component with a member. -/
theorem point_graph {z c : N} (zz : SZero z) :
    ∃ g : N, (∀ a d : N, SEdge g a d ↔ (a = z ∧ d = c)) ∧ SGraphDom z g ∧ SFun g := by
  obtain ⟨e0, he0⟩ := exists_empty hsep
  obtain ⟨g, _, _, _, hg⟩ := exists_extend hsep hwa e0 z c
  have hg' : ∀ a d : N, SEdge g a d ↔ (a = z ∧ d = c) := fun a d =>
    (hg a d).trans ⟨fun h => h.resolve_left (noEdge_empty he0), Or.inr⟩
  refine ⟨g, hg', ?_, ?_⟩
  · intro a
    constructor
    · rintro ⟨d, hd⟩
      exact Or.inr ((hg' a d).mp hd).1
    · rintro (h | h)
      · exact absurd h (zz a)
      · exact ⟨c, (hg' a c).mpr ⟨h, rfl⟩⟩
  · intro a d d' ⟨h1, h2⟩
    rw [((hg' a d).mp h1).2, ((hg' a d').mp h2).2]

theorem extend_prefix {x y g w : N} (dy : SDom y) (sxy : SSucc x y) (dw : SDom w)
    (hgd : SGraphDom x g) (hf : SFun g) (hr : SRange g) :
    ∃ g' : N, (∀ a c : N, SEdge g' a c ↔ (SEdge g a c ∨ (a = y ∧ c = w))) ∧
      (SGraphDom y g' ∧ (SFun g' ∧ SRange g')) := by
  obtain ⟨g', _, _, _, hg'⟩ := exists_extend hsep hwa g y w
  have hxy : Mem x y := (sxy x).mpr (Or.inr rfl)
  have noY : ∀ c : N, ¬SEdge g y c := by
    intro c hc
    rcases (hgd y).mp ⟨c, hc⟩ with h | h
    · exact dom_irrefl dy (dy.1.1 x y ⟨hxy, h⟩)
    · rw [← h] at hxy
      exact dom_irrefl dy hxy
  refine ⟨g', hg', ?_, ?_, ?_⟩
  · intro a
    constructor
    · rintro ⟨c, hc⟩
      rcases (hg' a c).mp hc with h | ⟨e1, _⟩
      · exact Or.inl ((sxy a).mpr ((hgd a).mp ⟨c, h⟩))
      · exact Or.inr e1
    · rintro (h | h)
      · obtain ⟨c, hc⟩ := (hgd a).mpr ((sxy a).mp h)
        exact ⟨c, (hg' a c).mpr (Or.inl hc)⟩
      · exact ⟨w, (hg' a w).mpr (Or.inr ⟨h, rfl⟩)⟩
  · intro a c c' ⟨h1, h2⟩
    rcases (hg' a c).mp h1 with b1 | ⟨e1, e2⟩
    · rcases (hg' a c').mp h2 with b2 | ⟨e3, _⟩
      · exact hf a c c' ⟨b1, b2⟩
      · rw [e3] at b1
        exact absurd b1 (noY c)
    · rcases (hg' a c').mp h2 with b2 | ⟨_, e4⟩
      · rw [e1] at b2
        exact absurd b2 (noY c')
      · rw [e2, e4]
  · intro a c h
    rcases (hg' a c).mp h with b | ⟨_, e2⟩
    · exact hr a c b
    · rw [e2]
      exact dw

theorem add_total (f : ℕ → N) : ∀ x : N, SDom x → PA1 x := by
  have key := letter_induction hsep f psiA1
    (by
      intro z _ zz
      refine (ev_psiA1_iff f z).mpr ?_
      intro c _ dc
      obtain ⟨g, hg, hgd, hf⟩ := point_graph hsep hwa (c := c) zz
      refine ⟨c, dc, z, g, zz, ⟨hgd, hf, ?_, (hg z c).mpr ⟨rfl, rfl⟩, ?_⟩,
        (hg z c).mpr ⟨rfl, rfl⟩⟩
      · intro a d h
        rw [((hg a d).mp h).2]
        exact dc
      · intro a d k ⟨h, hk⟩
        have hka : Mem k a := (hk k).mpr (Or.inr rfl)
        rw [((hg a d).mp h).1] at hka
        exact absurd hka (zz k))
    (by
      intro x y dx dy sxy ih
      have ih' := (ev_psiA1_iff f x).mp ih
      refine (ev_psiA1_iff f y).mpr ?_
      intro c _ dc
      obtain ⟨d, dd, e, g, he, ⟨hgd, hf, hr, hbase, hrec⟩, hedge⟩ := ih' c dx dc
      obtain ⟨w, dw, sdw⟩ := succ_exists hsep hwa dd
      obtain ⟨g', hg', hgd', hf', hr'⟩ := extend_prefix hsep hwa dy sxy dw hgd hf hr
      refine ⟨w, dw, e, g', he, ⟨hgd', hf', hr', (hg' e c).mpr (Or.inl hbase), ?_⟩,
        (hg' y w).mpr (Or.inr ⟨rfl, rfl⟩)⟩
      intro a b k ⟨hab, hka⟩
      rcases (hg' a b).mp hab with h | ⟨e1, e2⟩
      · obtain ⟨d', hd', hs'⟩ := hrec a b k ⟨h, hka⟩
        exact ⟨d', (hg' k d').mpr (Or.inl hd'), hs'⟩
      · rw [e1] at hka
        have hk : k = x := succ_pred_unique dy sxy hka
        rw [hk, e2]
        exact ⟨d, (hg' x d).mpr (Or.inl hedge), sdw⟩)
  intro x hx
  exact (ev_psiA1_iff f x).mp (key x hx)

theorem mul_total (f : ℕ → N) : ∀ x : N, SDom x → PM1 x := by
  have A1 := add_total hsep hwa f
  have key := letter_induction hsep f psiM1
    (by
      intro z dz zz
      refine (ev_psiM1_iff f z).mpr ?_
      intro c _ _
      obtain ⟨g, hg, hgd, hf⟩ := point_graph hsep hwa (c := z) zz
      refine ⟨z, dz, z, g, zz, ⟨hgd, hf, ?_, (hg z z).mpr ⟨rfl, rfl⟩, ?_⟩,
        (hg z z).mpr ⟨rfl, rfl⟩⟩
      · intro a d h
        rw [((hg a d).mp h).2]
        exact dz
      · intro a d k ⟨h, hk⟩
        have hka : Mem k a := (hk k).mpr (Or.inr rfl)
        rw [((hg a d).mp h).1] at hka
        exact absurd hka (zz k))
    (by
      intro x y dx dy sxy ih
      have ih' := (ev_psiM1_iff f x).mp ih
      refine (ev_psiM1_iff f y).mpr ?_
      intro c _ dc
      obtain ⟨d, dd, e, g, he, ⟨hgd, hf, hr, hbase, hrec⟩, hedge⟩ := ih' c dx dc
      obtain ⟨w, dw, adw⟩ := A1 d dd c dd dc
      obtain ⟨g', hg', hgd', hf', hr'⟩ := extend_prefix hsep hwa dy sxy dw hgd hf hr
      refine ⟨w, dw, e, g', he, ⟨hgd', hf', hr', (hg' e e).mpr (Or.inl hbase), ?_⟩,
        (hg' y w).mpr (Or.inr ⟨rfl, rfl⟩)⟩
      intro a b k ⟨hab, hka⟩
      rcases (hg' a b).mp hab with h | ⟨e1, e2⟩
      · obtain ⟨d', hd', hs'⟩ := hrec a b k ⟨h, hka⟩
        exact ⟨d', (hg' k d').mpr (Or.inl hd'), hs'⟩
      · rw [e1] at hka
        have hk : k = x := succ_pred_unique dy sxy hka
        rw [hk, e2]
        exact ⟨d, (hg' x d).mpr (Or.inl hedge), adw⟩)
  intro x hx
  exact (ev_psiM1_iff f x).mp (key x hx)

#print axioms succ_pred_unique
#print axioms extend_prefix
#print axioms add_total
#print axioms mul_total
end model
end PA194SourceModel
