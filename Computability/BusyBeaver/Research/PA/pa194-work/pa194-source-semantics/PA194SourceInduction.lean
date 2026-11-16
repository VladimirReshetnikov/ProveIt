import PA194SourceModelIso
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
/-!
# Induction over ordinal representatives in a structure

* `dom_mem`: a member of an ordinal representative is an ordinal representative.
* `dom_zero_or_succ`: an ordinal representative is empty or a successor of one of its
  members, which is an ordinal representative (its greatest member).
* `dom_induction`: for a property whose complement is defined by a formula with parameters:
  if it holds for the empty representatives and passes from a representative to its
  successors, it holds for all representatives. A counterexample `x` gives, by separation and
  the least-member clause of `x`, a counterexample all of whose members satisfy the property.
* `letter_induction`: the same for a property given by a formula over the letters.
-/
namespace PA194SourceModel
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PA194ModelLogic PA194BindSource PA194Schematic PA194GuardedCompiler
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal
open M6.PA.RelationalSource.PairGraph

attribute [local instance] PA194ModelLogic.sourceLanguageAdjTheory

section model
variable {N : Type} [s : Structure SourceL N] [Structure.Eq SourceL N]

theorem dom_mem {a x : N} (ha : SDom a) (hx : Mem x a) : SDom x := by
  obtain ⟨⟨hT, hMT, hML, hEx⟩, hIr⟩ := ha
  refine ⟨⟨hMT x hx, ?_, ?_, ?_⟩, ?_⟩
  · intro y hy
    exact hMT y (hT x y ⟨hx, hy⟩)
  · intro y z ⟨hy, hz⟩
    exact hML y z ⟨hT x y ⟨hx, hy⟩, hT x z ⟨hx, hz⟩⟩
  · intro t ⟨hsub, hne⟩
    exact hEx t ⟨fun y hy => hT x y ⟨hx, hsub y hy⟩, hne⟩
  · intro y hy
    exact hIr y (hT x y ⟨hx, hy⟩)

theorem dom_zero_or_succ {a : N} (ha : SDom a) :
    SZero a ∨ ∃ p : N, SDom p ∧ SSucc p a := by
  by_cases hz : SZero a
  · exact Or.inl hz
  · right
    have hne : SNonempty a := by
      by_contra h
      exact hz (fun x hx => h ⟨x, hx⟩)
    obtain ⟨_, ⟨p, hp, hgr⟩⟩ := ha.1.2.2.2 a ⟨fun x hx => hx, hne⟩
    refine ⟨p, dom_mem ha hp, fun y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
    · rcases hgr y hy with h | h
      · exact Or.inr h
      · exact Or.inl h
    · rcases hy with h | h
      · exact ha.1.1 p y ⟨hp, h⟩
      · rw [h]
        exact hp

variable (hsep : ∀ (p : Semiproposition SourceL 1) (f : ℕ → N),
  FirstOrder.Semiformula.Evalf (s := s) f (separationFormula p))
include hsep

theorem dom_induction (p : Semiproposition SourceL 1) (f : ℕ → N) (P : N → Prop)
    (hP : ∀ x : N, FirstOrder.Semiformula.Eval (s := s) ![x] f p ↔ ¬P x)
    (h0 : ∀ z : N, SDom z → SZero z → P z)
    (hS : ∀ x y : N, SDom x → SDom y → SSucc x y → P x → P y) :
    ∀ x : N, SDom x → P x := by
  intro x hx
  by_contra hnx
  have hmin : ∃ m : N, SDom m ∧ ¬P m ∧ ∀ y : N, Mem y m → P y := by
    obtain ⟨bad, hbad⟩ := sep_spec hsep p f x
    by_cases hne : SNonempty bad
    · obtain ⟨⟨m, hm, hle⟩, _⟩ := hx.1.2.2.2 bad ⟨fun y hy => ((hbad y).mp hy).1, hne⟩
      obtain ⟨hmx, hmp⟩ := (hbad m).mp hm
      refine ⟨m, dom_mem hx hmx, (hP m).mp hmp, fun y hy => ?_⟩
      by_contra hny
      have hyx : Mem y x := hx.1.1 m y ⟨hmx, hy⟩
      have hyb : Mem y bad := (hbad y).mpr ⟨hyx, (hP y).mpr hny⟩
      rcases hle y hyb with h | h
      · rw [← h] at hy
        exact hx.2 m hmx hy
      · exact hx.2 m hmx (hx.1.2.1 m hmx y m ⟨hy, h⟩)
    · refine ⟨x, hx, hnx, fun y hy => ?_⟩
      by_contra hny
      exact hne ⟨y, (hbad y).mpr ⟨hy, (hP y).mpr hny⟩⟩
  obtain ⟨m, hm, hnm, hall⟩ := hmin
  rcases dom_zero_or_succ hm with hz | ⟨q, hq, hs⟩
  · exact hnm (h0 m hm hz)
  · exact hnm (hS q m hq hm hs (hall q ((hs q).mpr (Or.inr rfl))))

/-- Induction for a property given by a formula over the letters. -/
theorem letter_induction (f : ℕ → N) (ψ : SF 1)
    (h0 : ∀ z : N, SDom z → SZero z → @ev N (sourceLetters s f) 1 ![z] ψ)
    (hS : ∀ x y : N, SDom x → SDom y → SSucc x y →
      @ev N (sourceLetters s f) 1 ![x] ψ → @ev N (sourceLetters s f) 1 ![y] ψ) :
    ∀ x : N, SDom x → @ev N (sourceLetters s f) 1 ![x] ψ :=
  dom_induction hsep (sinst tau0 (∼ψ)) f (fun x => @ev N (sourceLetters s f) 1 ![x] ψ)
    (fun x => (eval_sinst tau0 s f ![x] (∼ψ)).trans (by simp)) h0 hS

#print axioms dom_mem
#print axioms dom_zero_or_succ
#print axioms dom_induction
#print axioms letter_induction
end model
end PA194SourceModel
