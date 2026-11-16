import PA194SourceModelBase
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
/-!
# Order isomorphism of ordinal representatives in a structure

* `SIso a b`: some graph is an order-preserving bijection between the members of `a` and the
  members of `b`; `se_orderIso` and `mI_iff` identify it with the source formula and with
  the letter for isomorphism.
* `iso_right_empty`, `iso_left_empty`: a representative isomorphic to an empty one is empty.
* `restrict_left`: the entries of a graph whose first component is a member of `x`
  (one separation instance with parameter `x`).
* `iso_cancel`: if `y` is a successor of `x`, `v₁` a successor of `v₀`, both ordinal
  representatives, and `y`, `v₁` are isomorphic, then `x`, `v₀` are isomorphic. The bijection
  sends `x` to `v₀`, and its restriction to the members of `x` is the required bijection.
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

def SEntryW (a c p : N) : Prop := ∃ x y : N, Mem x a ∧ (Mem y c ∧ SKur p x y)
def SEntries (g a c : N) : Prop := ∀ p : N, Mem p g → SEntryW a c p
def STyped (g a c : N) : Prop := ∀ x y : N, SEdge g x y → (Mem x a ∧ Mem y c)
def SLeftTotal (g a : N) : Prop := ∀ x : N, Mem x a → ∃ y : N, SEdge g x y
def SRightTotal (g c : N) : Prop := ∀ y : N, Mem y c → ∃ x : N, SEdge g x y
def SInj (g : N) : Prop := ∀ x x' y : N, (SEdge g x y ∧ SEdge g x' y) → x = x'
def SOrder (g : N) : Prop :=
  ∀ a a' c c' : N, (SEdge g a c ∧ SEdge g a' c') → (Mem a' a ↔ Mem c' c)
def SBij (g a c : N) : Prop :=
  SEntries g a c ∧ (STyped g a c ∧ (SLeftTotal g a ∧ (SRightTotal g c ∧
    (SFun g ∧ (SInj g ∧ SOrder g)))))
/-- `a` and `c` are order-isomorphic. -/
def SIso (a c : N) : Prop := ∃ g : N, SBij g a c

section eval
variable {n : ℕ} (b : Fin n → N) (f : ℕ → N)

@[simp] theorem se_entryWitness (a c p : Term n) :
    se b f (PairGraph.entryWitness a c p) ↔ SEntryW (sv b f a) (sv b f c) (sv b f p) := by
  simp [PairGraph.entryWitness, SEntryW]
@[simp] theorem se_graphEntries (g a c : Term n) :
    se b f (PairGraph.graphEntries g a c) ↔ SEntries (sv b f g) (sv b f a) (sv b f c) := by
  simp [PairGraph.graphEntries, SEntries]
@[simp] theorem se_graphTyped (g a c : Term n) :
    se b f (PairGraph.graphTyped g a c) ↔ STyped (sv b f g) (sv b f a) (sv b f c) := by
  simp [PairGraph.graphTyped, STyped]
@[simp] theorem se_graphLeftTotal (g a : Term n) :
    se b f (PairGraph.graphLeftTotal g a) ↔ SLeftTotal (sv b f g) (sv b f a) := by
  simp [PairGraph.graphLeftTotal, SLeftTotal]
@[simp] theorem se_graphRightTotal (g c : Term n) :
    se b f (PairGraph.graphRightTotal g c) ↔ SRightTotal (sv b f g) (sv b f c) := by
  simp [PairGraph.graphRightTotal, SRightTotal]
@[simp] theorem se_graphInjective (g : Term n) :
    se b f (PairGraph.graphInjective g) ↔ SInj (sv b f g) := by
  simp [PairGraph.graphInjective, SInj]
@[simp] theorem se_graphOrder (g : Term n) :
    se b f (PairGraph.graphOrder g) ↔ SOrder (sv b f g) := by
  simp [PairGraph.graphOrder, SOrder]
@[simp] theorem se_orderBijection (g a c : Term n) :
    se b f (PairGraph.orderBijection g a c) ↔ SBij (sv b f g) (sv b f a) (sv b f c) := by
  simp [PairGraph.orderBijection, SBij]
@[simp] theorem se_orderIso (a c : Term n) :
    se b f (PairGraph.orderIso a c) ↔ SIso (sv b f a) (sv b f c) := by
  simp [PairGraph.orderIso, SIso]

end eval

theorem mI_iff (f : ℕ → N) (x y : N) : @mI N (sourceLetters s f) x y ↔ SIso x y := by
  show se ![x, y] f (PairGraph.orderIso (.bvar 0) (.bvar 1)) ↔ _
  simp

theorem iso_right_empty {a c : N} (h : SIso a c) (ha : SZero a) : SZero c := by
  obtain ⟨g, _, hT, _, hR, _⟩ := h
  intro y hy
  obtain ⟨x, hx⟩ := hR y hy
  exact ha x (hT x y hx).1

theorem iso_left_empty {a c : N} (h : SIso a c) (hc : SZero c) : SZero a := by
  obtain ⟨g, _, hT, hL, _⟩ := h
  intro x hx
  obtain ⟨y, hy⟩ := hL x hx
  exact hc y (hT x y hy).2

/-- "A Kuratowski pair whose first component is a member of the parameter `&0`." -/
def leftProp : Semiproposition SourceL 1 :=
  ∃⁰ ∃⁰ (PairGraph.kuratowski (.bvar 2) (.bvar 1) (.bvar 0) ⋏ mem (.fvar 0) (.bvar 1))

theorem eval_leftProp (f : ℕ → N) (q : N) :
    FirstOrder.Semiformula.Eval (s := s) ![q] f leftProp ↔
      ∃ x y : N, SKur q x y ∧ Mem x (f 0) := by
  show se ![q] f leftProp ↔ _
  simp [leftProp]

variable (hsep : ∀ (p : Semiproposition SourceL 1) (f : ℕ → N),
  FirstOrder.Semiformula.Evalf (s := s) f (separationFormula p))
include hsep

/-- The entries of `g` whose first component is a member of `x`: the members of the new
graph and its edges. -/
theorem restrict_left (g x : N) :
    ∃ g' : N, (∀ p : N, Mem p g' ↔ (Mem p g ∧ ∃ a c : N, SKur p a c ∧ Mem a x)) ∧
      ∀ a c : N, SEdge g' a c ↔ (SEdge g a c ∧ Mem a x) := by
  obtain ⟨g', hg'⟩ := sep_spec hsep leftProp (fun _ => x) g
  have hm : ∀ p : N, Mem p g' ↔ (Mem p g ∧ ∃ a c : N, SKur p a c ∧ Mem a x) := fun p =>
    (hg' p).trans (and_congr Iff.rfl (eval_leftProp (fun _ => x) p))
  refine ⟨g', hm, fun a c => ?_⟩
  constructor
  · rintro ⟨p, hp, hk⟩
    obtain ⟨hpg, a', c', hk', ha'⟩ := (hm p).mp hp
    obtain ⟨e1, _⟩ := kur_inj hk hk'
    subst e1
    exact ⟨⟨p, hpg, hk⟩, ha'⟩
  · rintro ⟨⟨p, hpg, hk⟩, ha⟩
    exact ⟨p, (hm p).mpr ⟨hpg, a, c, hk, ha⟩, hk⟩

/-- Cancellation of a successor on both sides of an isomorphism. -/
theorem iso_cancel {x y v0 v1 : N} (hy : SDom y) (hv : SDom v1) (sx : SSucc x y)
    (sv : SSucc v0 v1) (h : SIso y v1) : SIso x v0 := by
  obtain ⟨g, hE, hT, hL, hR, hF, hI, hO⟩ := h
  have hxy : Mem x y := (sx x).mpr (Or.inr rfl)
  have hv0 : Mem v0 v1 := (sv v0).mpr (Or.inr rfl)
  have irY : ∀ z : N, Mem z y → ¬Mem z z := hy.2
  have irV : ∀ z : N, Mem z v1 → ¬Mem z z := hv.2
  have mtV : ∀ z : N, Mem z v1 → STrans z := hv.1.2.1
  -- the bijection sends `x` to `v0`
  obtain ⟨m, hxm⟩ := hL x hxy
  have hm1 : Mem m v1 := (hT x m hxm).2
  have hmv : m = v0 := by
    rcases (sv m).mp hm1 with hm | hm
    · exfalso
      obtain ⟨a, ha⟩ := hR v0 hv0
      rcases (sx a).mp (hT a v0 ha).1 with hax | hax
      · have h1 : Mem v0 m := (hO x a m v0 ⟨hxm, ha⟩).mp hax
        exact irV m hm1 (mtV m hm1 v0 m ⟨h1, hm⟩)
      · rw [hax] at ha
        have e : v0 = m := hF x v0 m ⟨ha, hxm⟩
        rw [e] at hm
        exact irV m hm1 hm
    · exact hm
  rw [hmv] at hxm
  -- an entry with first component in `x` has its second component in `v0`
  have key : ∀ a c : N, SEdge g a c → Mem a x → Mem c v0 := by
    intro a c hac hax
    rcases (sv c).mp (hT a c hac).2 with hc | hc
    · exact hc
    · exfalso
      rw [hc] at hac
      have e : a = x := hI a x v0 ⟨hac, hxm⟩
      rw [e] at hax
      exact irY x hxy hax
  obtain ⟨g', hm', hg'⟩ := restrict_left hsep g x
  refine ⟨g', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨hpg, a, c, hk, ha⟩ := (hm' p).mp hp
    exact ⟨a, c, ha, key a c ⟨p, hpg, hk⟩ ha, hk⟩
  · intro a c hac
    obtain ⟨h1, h2⟩ := (hg' a c).mp hac
    exact ⟨h2, key a c h1 h2⟩
  · intro a ha
    obtain ⟨c, hc⟩ := hL a ((sx a).mpr (Or.inl ha))
    exact ⟨c, (hg' a c).mpr ⟨hc, ha⟩⟩
  · intro c hc
    obtain ⟨a, ha⟩ := hR c ((sv c).mpr (Or.inl hc))
    rcases (sx a).mp (hT a c ha).1 with hax | hax
    · exact ⟨a, (hg' a c).mpr ⟨ha, hax⟩⟩
    · exfalso
      rw [hax] at ha
      have e : c = v0 := hF x c v0 ⟨ha, hxm⟩
      rw [e] at hc
      exact irV v0 hv0 hc
  · intro a c c' ⟨h1, h2⟩
    exact hF a c c' ⟨((hg' a c).mp h1).1, ((hg' a c').mp h2).1⟩
  · intro a a' c ⟨h1, h2⟩
    exact hI a a' c ⟨((hg' a c).mp h1).1, ((hg' a' c).mp h2).1⟩
  · intro a a' c c' ⟨h1, h2⟩
    exact hO a a' c c' ⟨((hg' a c).mp h1).1, ((hg' a' c').mp h2).1⟩

#print axioms mI_iff
#print axioms iso_cancel
end model
end PA194SourceModel
