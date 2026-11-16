import PA194SourceSets
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
/-!
# Order isomorphism of ordinal representatives is an equivalence, in a structure

* `iso_of_empty`: two empty objects are isomorphic (by an empty graph).
* `iso_succ`: successors of isomorphic ordinal representatives are isomorphic (the bijection
  with one more entry).
* `iso_refl`, `iso_symm`, `iso_trans`: by `letter_induction` on the first representative,
  with `iso_cancel` and `iso_succ`. No inverse or composite graph is constructed.
-/
namespace PA194GuardedCompiler
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PA194Schematic

def psiRefl : SF 1 := sIso #0 #0
def psiSym : SF 1 := ∀⁰ (sDom #1 🡒 sDom #0 🡒 sIso #1 #0 🡒 sIso #0 #1)
def psiTrans : SF 1 :=
  ∀⁰ ∀⁰ (sDom #2 🡒 sDom #1 🡒 sDom #0 🡒 sIso #2 #1 🡒 sIso #1 #0 🡒 sIso #2 #0)

section semantics
variable {M : Type} [s : Structure NL M]

theorem ev_psiRefl (x : M) : ev ![x] psiRefl ↔ mI x x := by
  simp [psiRefl]
theorem ev_psiSym (x : M) : ev ![x] psiSym ↔ ∀ c : M, mD x → mD c → mI x c → mI c x := by
  simp [psiSym]
theorem ev_psiTrans (x : M) : ev ![x] psiTrans ↔
    ∀ c d : M, mD x → mD c → mD d → mI x c → mI c d → mI x d := by
  simp [psiTrans]

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

def PSym (x : N) : Prop := ∀ c : N, SDom x → SDom c → SIso x c → SIso c x
def PTr (x : N) : Prop :=
  ∀ c d : N, SDom x → SDom c → SDom d → SIso x c → SIso c d → SIso x d

theorem ev_psiRefl_iff (f : ℕ → N) (x : N) :
    @ev N (sourceLetters s f) 1 ![x] psiRefl ↔ SIso x x :=
  (@ev_psiRefl N (sourceLetters s f) x).trans (mI_iff f x x)
theorem ev_psiSym_iff (f : ℕ → N) (x : N) :
    @ev N (sourceLetters s f) 1 ![x] psiSym ↔ PSym x := by
  rw [@ev_psiSym N (sourceLetters s f) x]
  simp only [mD_iff, mI_iff, PSym]
theorem ev_psiTrans_iff (f : ℕ → N) (x : N) :
    @ev N (sourceLetters s f) 1 ![x] psiTrans ↔ PTr x := by
  rw [@ev_psiTrans N (sourceLetters s f) x]
  simp only [mD_iff, mI_iff, PTr]

variable (hsep : ∀ (p : Semiproposition SourceL 1) (f : ℕ → N),
  FirstOrder.Semiformula.Evalf (s := s) f (separationFormula p))
include hsep

theorem iso_of_empty {a c : N} (ha : SZero a) (hc : SZero c) : SIso a c := by
  obtain ⟨e, he⟩ := exists_empty hsep
  refine ⟨e, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact absurd hp (he p)
  · rintro x y ⟨p, hp, _⟩
    exact absurd hp (he p)
  · intro x hx
    exact absurd hx (ha x)
  · intro y hy
    exact absurd hy (hc y)
  · rintro x y z ⟨⟨p, hp, _⟩, _⟩
    exact absurd hp (he p)
  · rintro x x' y ⟨⟨p, hp, _⟩, _⟩
    exact absurd hp (he p)
  · rintro x x' y y' ⟨⟨p, hp, _⟩, _⟩
    exact absurd hp (he p)

variable (hwa : N↓[SourceL] ⊧ sourceWeakAdjunction)
include hwa

theorem iso_succ {u w u' w' : N} (du : SDom u) (du' : SDom u') (sw : SSucc u w)
    (sw' : SSucc u' w') (h : SIso u u') : SIso w w' := by
  obtain ⟨g, hE, hT, hL, hR, hF, hI, hO⟩ := h
  obtain ⟨g', p, hp, hm, hg'⟩ := exists_extend hsep hwa g u u'
  have iu : ¬Mem u u := dom_irrefl du
  have iu' : ¬Mem u' u' := dom_irrefl du'
  have tu : STrans u := du.1.1
  have tu' : STrans u' := du'.1.1
  refine ⟨g', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    rcases (hm q).mp hq with h | h
    · obtain ⟨x, y, hx, hy, hk⟩ := hE q h
      exact ⟨x, y, (sw x).mpr (Or.inl hx), (sw' y).mpr (Or.inl hy), hk⟩
    · rw [h]
      exact ⟨u, u', (sw u).mpr (Or.inr rfl), (sw' u').mpr (Or.inr rfl), hp⟩
  · intro x y hxy
    rcases (hg' x y).mp hxy with h | ⟨e1, e2⟩
    · exact ⟨(sw x).mpr (Or.inl (hT x y h).1), (sw' y).mpr (Or.inl (hT x y h).2)⟩
    · rw [e1, e2]
      exact ⟨(sw u).mpr (Or.inr rfl), (sw' u').mpr (Or.inr rfl)⟩
  · intro x hx
    rcases (sw x).mp hx with h | h
    · obtain ⟨y, hy⟩ := hL x h
      exact ⟨y, (hg' x y).mpr (Or.inl hy)⟩
    · exact ⟨u', (hg' x u').mpr (Or.inr ⟨h, rfl⟩)⟩
  · intro y hy
    rcases (sw' y).mp hy with h | h
    · obtain ⟨x, hx⟩ := hR y h
      exact ⟨x, (hg' x y).mpr (Or.inl hx)⟩
    · exact ⟨u, (hg' u y).mpr (Or.inr ⟨rfl, h⟩)⟩
  · intro x y z ⟨h1, h2⟩
    rcases (hg' x y).mp h1 with a1 | ⟨e1, e2⟩
    · rcases (hg' x z).mp h2 with a2 | ⟨e3, _⟩
      · exact hF x y z ⟨a1, a2⟩
      · rw [e3] at a1
        exact absurd (hT u y a1).1 iu
    · rcases (hg' x z).mp h2 with a2 | ⟨_, e4⟩
      · rw [e1] at a2
        exact absurd (hT u z a2).1 iu
      · rw [e2, e4]
  · intro x x' y ⟨h1, h2⟩
    rcases (hg' x y).mp h1 with a1 | ⟨e1, e2⟩
    · rcases (hg' x' y).mp h2 with a2 | ⟨_, e4⟩
      · exact hI x x' y ⟨a1, a2⟩
      · rw [e4] at a1
        exact absurd (hT x u' a1).2 iu'
    · rcases (hg' x' y).mp h2 with a2 | ⟨e3, _⟩
      · rw [e2] at a2
        exact absurd (hT x' u' a2).2 iu'
      · rw [e1, e3]
  · intro a a' c c' ⟨h1, h2⟩
    rcases (hg' a c).mp h1 with b1 | ⟨e1, e2⟩
    · rcases (hg' a' c').mp h2 with b2 | ⟨e3, e4⟩
      · exact hO a a' c c' ⟨b1, b2⟩
      · rw [e3, e4]
        constructor
        · intro h
          exact absurd (tu a u ⟨(hT a c b1).1, h⟩) iu
        · intro h
          exact absurd (tu' c u' ⟨(hT a c b1).2, h⟩) iu'
    · rcases (hg' a' c').mp h2 with b2 | ⟨e3, e4⟩
      · rw [e1, e2]
        exact ⟨fun _ => (hT a' c' b2).2, fun _ => (hT a' c' b2).1⟩
      · rw [e1, e2, e3, e4]
        exact ⟨fun h => absurd h iu, fun h => absurd h iu'⟩

theorem iso_refl (f : ℕ → N) : ∀ a : N, SDom a → SIso a a := by
  have key := letter_induction hsep f psiRefl
    (by
      intro z _ zz
      exact (ev_psiRefl_iff f z).mpr (iso_of_empty hsep zz zz))
    (by
      intro x y dx _ sxy ih
      exact (ev_psiRefl_iff f y).mpr
        (iso_succ hsep hwa dx dx sxy sxy ((ev_psiRefl_iff f x).mp ih)))
  intro a ha
  exact (ev_psiRefl_iff f a).mp (key a ha)

theorem iso_symm (f : ℕ → N) : ∀ a : N, SDom a → PSym a := by
  have key := letter_induction hsep f psiSym
    (by
      intro z _ zz
      refine (ev_psiSym_iff f z).mpr ?_
      intro c _ _ h
      exact iso_of_empty hsep (iso_right_empty h zz) zz)
    (by
      intro x y dx dy sxy ih
      have ih' := (ev_psiSym_iff f x).mp ih
      refine (ev_psiSym_iff f y).mpr ?_
      intro c _ dc h
      rcases dom_zero_or_succ dc with zc | ⟨c0, dc0, sc⟩
      · exact absurd ((sxy x).mpr (Or.inr rfl)) (iso_left_empty h zc x)
      · have i0 : SIso x c0 := iso_cancel hsep dy dc sxy sc h
        exact iso_succ hsep hwa dc0 dx sc sxy (ih' c0 dx dc0 i0))
  intro a ha
  exact (ev_psiSym_iff f a).mp (key a ha)

theorem iso_trans (f : ℕ → N) : ∀ a : N, SDom a → PTr a := by
  have key := letter_induction hsep f psiTrans
    (by
      intro z _ zz
      refine (ev_psiTrans_iff f z).mpr ?_
      intro c d _ _ _ h1 h2
      exact iso_of_empty hsep zz (iso_right_empty h2 (iso_right_empty h1 zz)))
    (by
      intro x y dx dy sxy ih
      have ih' := (ev_psiTrans_iff f x).mp ih
      refine (ev_psiTrans_iff f y).mpr ?_
      intro c d _ dc dd h1 h2
      rcases dom_zero_or_succ dc with zc | ⟨c0, dc0, sc⟩
      · exact absurd ((sxy x).mpr (Or.inr rfl)) (iso_left_empty h1 zc x)
      · have i0 : SIso x c0 := iso_cancel hsep dy dc sxy sc h1
        rcases dom_zero_or_succ dd with zd | ⟨d0, dd0, sd⟩
        · exact absurd ((sc c0).mpr (Or.inr rfl)) (iso_left_empty h2 zd c0)
        · have i1 : SIso c0 d0 := iso_cancel hsep dc dd sc sd h2
          exact iso_succ hsep hwa dx dd0 sxy sd (ih' c0 d0 dx dc0 dd0 i0 i1))
  intro a ha
  exact (ev_psiTrans_iff f a).mp (key a ha)

#print axioms iso_of_empty
#print axioms iso_succ
#print axioms iso_refl
#print axioms iso_symm
#print axioms iso_trans
end model
end PA194SourceModel
