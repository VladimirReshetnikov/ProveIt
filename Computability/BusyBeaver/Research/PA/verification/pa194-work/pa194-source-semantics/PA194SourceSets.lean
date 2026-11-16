import PA194SourceInduction
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
/-!
# Sets in a structure for the source theory

In a nonempty structure with equality that satisfies weak adjunction and the separation
instances (not assumed extensional):

* `wa_spec`: weak adjunction as a statement about membership;
* `exists_empty`, `exists_adjoin` (an object whose members are exactly the members of `a`
  and `c`), `exists_singleton`, `exists_pair`, `exists_kur`;
* `exists_extend`: a graph with one more entry;
* `dom_irrefl`: an ordinal representative is not a member of itself;
* `empty_dom`: an empty object is an ordinal representative;
* `succ_exists`: every ordinal representative has a successor that is an ordinal
  representative.
-/
namespace PA194SourceModel
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PA194ModelLogic PA194BindSource PA194Schematic PA194GuardedCompiler
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal
open M6.PA.RelationalSource.PairGraph

attribute [local instance] PA194ModelLogic.sourceLanguageAdjTheory

section model
variable {N : Type} [Nonempty N] [s : Structure SourceL N] [Structure.Eq SourceL N]

theorem wa_spec (hwa : N↓[SourceL] ⊧ sourceWeakAdjunction) (a c : N) :
    ∃ d : N, (∀ w : N, Mem w a → Mem w d) ∧ Mem c d := by
  have h : ∀ a c : N, ∃ d : N, (∀ w : N, ¬Mem w a ∨ Mem w d) ∧ Mem c d := by
    simpa [models_iff, sourceWeakAdjunction, Mem, Matrix.comp_vecCons', Matrix.constant_eq_singleton]
      using hwa
  obtain ⟨d, h1, h2⟩ := h a c
  exact ⟨d, fun w hw => (h1 w).resolve_left (fun hn => hn hw), h2⟩

/-- "A member of the parameter `&0`, or equal to the parameter `&1`." -/
def adjoinProp : Semiproposition SourceL 1 :=
  mem (.fvar 0) (.bvar 0) ⋎ eq (.bvar 0) (.fvar 1)
/-- "A member of the parameter `&0`." -/
def memProp : Semiproposition SourceL 1 := mem (.fvar 0) (.bvar 0)

theorem eval_adjoinProp (f : ℕ → N) (x : N) :
    FirstOrder.Semiformula.Eval (s := s) ![x] f adjoinProp ↔ (Mem x (f 0) ∨ x = f 1) := by
  show se ![x] f adjoinProp ↔ _
  simp [adjoinProp]
theorem eval_memProp (f : ℕ → N) (x : N) :
    FirstOrder.Semiformula.Eval (s := s) ![x] f memProp ↔ Mem x (f 0) := by
  show se ![x] f memProp ↔ _
  simp [memProp]

theorem dom_irrefl {u : N} (hu : SDom u) : ¬Mem u u := fun h => hu.2 u h h

variable (hsep : ∀ (p : Semiproposition SourceL 1) (f : ℕ → N),
  FirstOrder.Semiformula.Evalf (s := s) f (separationFormula p))
include hsep

theorem exists_empty : ∃ e : N, SZero e := by
  obtain ⟨a⟩ := ‹Nonempty N›
  obtain ⟨e, he⟩ := sep_spec hsep (⊥ : Semiproposition SourceL 1) (fun _ => a) a
  refine ⟨e, fun x hx => ?_⟩
  have h := ((he x).mp hx).2
  simp at h

/-- The members of `a` within `t`. -/
theorem exists_inter (t a : N) : ∃ c : N, ∀ x : N, Mem x c ↔ (Mem x t ∧ Mem x a) := by
  obtain ⟨c, hc⟩ := sep_spec hsep memProp (fun _ => a) t
  exact ⟨c, fun x => (hc x).trans (and_congr Iff.rfl (eval_memProp (fun _ => a) x))⟩

theorem empty_dom {e : N} (he : SZero e) : SDom e := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x y ⟨hx, _⟩
    exact absurd hx (he x)
  · intro x hx
    exact absurd hx (he x)
  · intro x y ⟨hx, _⟩
    exact absurd hx (he x)
  · intro t ⟨hsub, ⟨x, hx⟩⟩
    exact absurd (hsub x hx) (he x)
  · intro x hx
    exact absurd hx (he x)

variable (hwa : N↓[SourceL] ⊧ sourceWeakAdjunction)
include hwa

theorem exists_adjoin (a c : N) : ∃ d : N, ∀ x : N, Mem x d ↔ (Mem x a ∨ x = c) := by
  obtain ⟨d0, h1, h2⟩ := wa_spec hwa a c
  obtain ⟨d, hd⟩ := sep_spec hsep adjoinProp (fun n : ℕ => if n = 0 then a else c) d0
  refine ⟨d, fun x => ?_⟩
  have e := eval_adjoinProp (fun n : ℕ => if n = 0 then a else c) x
  simp only [if_true, one_ne_zero, if_false] at e
  constructor
  · intro hx
    exact e.mp ((hd x).mp hx).2
  · intro hx
    refine (hd x).mpr ⟨?_, e.mpr hx⟩
    rcases hx with h | h
    · exact h1 x h
    · rw [h]
      exact h2

theorem exists_singleton (a : N) : ∃ t : N, SSing a t := by
  obtain ⟨e, he⟩ := exists_empty hsep
  obtain ⟨t, ht⟩ := exists_adjoin hsep hwa e a
  exact ⟨t, fun x => (ht x).trans ⟨fun h => h.resolve_left (he x), Or.inr⟩⟩

theorem exists_pair (a c : N) : ∃ p : N, SPair a c p := by
  obtain ⟨t, ht⟩ := exists_singleton hsep hwa a
  obtain ⟨p, hp⟩ := exists_adjoin hsep hwa t c
  exact ⟨p, fun x => (hp x).trans (or_congr (ht x) Iff.rfl)⟩

theorem exists_kur (a c : N) : ∃ p : N, SKur p a c := by
  obtain ⟨t, ht⟩ := exists_singleton hsep hwa a
  obtain ⟨q, hq⟩ := exists_pair hsep hwa a c
  obtain ⟨p, hp⟩ := exists_pair hsep hwa t q
  exact ⟨p, t, q, ht, hq, hp⟩

/-- The graph `g` with one more entry, for the pair of `a` and `c`. -/
theorem exists_extend (g a c : N) :
    ∃ g' p : N, SKur p a c ∧ (∀ q : N, Mem q g' ↔ (Mem q g ∨ q = p)) ∧
      ∀ x y : N, SEdge g' x y ↔ (SEdge g x y ∨ (x = a ∧ y = c)) := by
  obtain ⟨p, hp⟩ := exists_kur hsep hwa a c
  obtain ⟨g', hg'⟩ := exists_adjoin hsep hwa g p
  refine ⟨g', p, hp, hg', fun x y => ?_⟩
  constructor
  · rintro ⟨q, hq, hk⟩
    rcases (hg' q).mp hq with h | h
    · exact Or.inl ⟨q, h, hk⟩
    · rw [h] at hk
      obtain ⟨e1, e2⟩ := kur_inj hk hp
      exact Or.inr ⟨e1, e2⟩
  · rintro (⟨q, hq, hk⟩ | ⟨e1, e2⟩)
    · exact ⟨q, (hg' q).mpr (Or.inl hq), hk⟩
    · rw [e1, e2]
      exact ⟨p, (hg' p).mpr (Or.inr rfl), hp⟩

/-- Every ordinal representative has a successor, and it is an ordinal representative. -/
theorem succ_exists {u : N} (hu : SDom u) : ∃ w : N, SDom w ∧ SSucc u w := by
  obtain ⟨w, hw⟩ := exists_adjoin hsep hwa u u
  have hT : STrans u := hu.1.1
  have hMT : SMemTrans u := hu.1.2.1
  have hML : SMemLinear u := hu.1.2.2.1
  have hEx : SExtrema u := hu.1.2.2.2
  have hIr : SMemIr u := hu.2
  refine ⟨w, ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩, hw⟩
  · intro x y ⟨hx, hy⟩
    rcases (hw x).mp hx with h | h
    · exact (hw y).mpr (Or.inl (hT x y ⟨h, hy⟩))
    · rw [h] at hy
      exact (hw y).mpr (Or.inl hy)
  · intro x hx
    rcases (hw x).mp hx with h | h
    · exact hMT x h
    · rw [h]
      exact hT
  · intro x y ⟨hx, hy⟩
    rcases (hw x).mp hx with h | h
    · rcases (hw y).mp hy with h' | h'
      · exact hML x y ⟨h, h'⟩
      · rw [h']
        exact Or.inr (Or.inl h)
    · rcases (hw y).mp hy with h' | h'
      · rw [h]
        exact Or.inr (Or.inr h')
      · rw [h, h']
        exact Or.inl rfl
  · intro t ⟨hsub, hne⟩
    constructor
    · -- a least member
      obtain ⟨c, hc⟩ := exists_inter hsep t u
      by_cases hcn : SNonempty c
      · obtain ⟨⟨m, hm, hle⟩, _⟩ := hEx c ⟨fun x hx => ((hc x).mp hx).2, hcn⟩
        refine ⟨m, ((hc m).mp hm).1, fun x hx => ?_⟩
        rcases (hw x).mp (hsub x hx) with h | h
        · exact hle x ((hc x).mpr ⟨hx, h⟩)
        · rw [h]
          exact Or.inr ((hc m).mp hm).2
      · obtain ⟨y, hy⟩ := hne
        have hall : ∀ x : N, Mem x t → x = u := by
          intro x hx
          rcases (hw x).mp (hsub x hx) with h | h
          · exact absurd ⟨x, (hc x).mpr ⟨hx, h⟩⟩ hcn
          · exact h
        have hyu : y = u := hall y hy
        rw [hyu] at hy
        exact ⟨u, hy, fun x hx => Or.inl (hall x hx).symm⟩
    · -- a greatest member
      by_cases hut : Mem u t
      · exact ⟨u, hut, fun x hx => ((hw x).mp (hsub x hx)).symm⟩
      · have hsub' : SSubset t u := by
          intro x hx
          rcases (hw x).mp (hsub x hx) with h | h
          · exact h
          · rw [h] at hx
            exact absurd hx hut
        exact (hEx t ⟨hsub', hne⟩).2
  · intro x hx
    rcases (hw x).mp hx with h | h
    · exact hIr x h
    · rw [h]
      exact dom_irrefl hu

#print axioms wa_spec
#print axioms exists_adjoin
#print axioms exists_extend
#print axioms succ_exists
end model
end PA194SourceModel
