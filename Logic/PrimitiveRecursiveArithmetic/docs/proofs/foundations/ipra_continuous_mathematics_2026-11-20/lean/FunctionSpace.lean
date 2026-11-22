import Mathlib.Tactic.Linarith
import Mathlib.Data.Rat.Lemmas

/-! Finite upper Lipschitz envelopes and their exact rational uniform distance.
No decidable equality on points is used. A code is a list of centres and heights.
Invalid negative heights are excluded by the presentation when a [0,1] range is needed. -/
namespace Precision.FunctionSpace

structure RationalSpace (X : Type) where
  d : X → X → ℚ
  self : ∀ x, d x x = 0
  tri : ∀ x y z, d x z ≤ d x y + d y z
  symm : ∀ x y, d x y = d y x

variable {X : Type}
abbrev Code (X : Type) := List (X × ℚ)
def lip (S : RationalSpace X) (L : ℚ) (f : X → ℚ) : Prop :=
  ∀ x y, f x ≤ f y + L*S.d x y

def eval (S : RationalSpace X) (L : ℚ) : Code X → X → ℚ
  | [], _ => 1
  | (a,b) :: c, x => min (b + L*S.d x a) (eval S L c x)

def excess (h : X → ℚ) : Code X → ℚ
  | [] => 0
  | (a,b) :: c => max (h a - b) (excess h c)

def dist (S : RationalSpace X) (L : ℚ) (A B : Code X) : ℚ :=
  max (excess (eval S L B) A) (excess (eval S L A) B)

theorem nonnegDist (S : RationalSpace X) (x y : X) : 0 ≤ S.d x y := by
  have h := S.tri x y x
  rw [S.self, S.symm y x] at h
  linarith

theorem eval_cap (S : RationalSpace X) (L : ℚ) (A : Code X) (x : X) : eval S L A x ≤ 1 := by
  induction A with
  | nil => exact le_refl _
  | cons a _ ih => exact le_trans (min_le_right _ _) ih

theorem eval_lip (S : RationalSpace X) {L : ℚ} (hL : 0 ≤ L) (A : Code X) : lip S L (eval S L A) := by
  induction A with
  | nil =>
    intro x y
    have h := mul_nonneg hL (nonnegDist S x y)
    simp only [eval]
    linarith
  | cons p c ih =>
    obtain ⟨a,b⟩ := p
    intro x y
    have m := mul_le_mul_of_nonneg_left (S.tri x y a) hL
    have h := ih x y
    simp only [eval]
    by_cases hc : b + L*S.d y a ≤ eval S L c y
    · rw [min_eq_left hc]
      exact le_trans (min_le_left _ _) (by linarith)
    · rw [min_eq_right (le_of_not_ge hc)]
      exact le_trans (min_le_right _ _) (by linarith)

theorem eval_anchor (S : RationalSpace X) (L : ℚ) (A : Code X) {a : X} {b : ℚ}
    (hm : (a,b) ∈ A) (x : X) : eval S L A x ≤ b+L*S.d x a := by
  induction A with
  | nil => simp at hm
  | cons p c ih =>
    rcases List.mem_cons.mp hm with eq | tail
    · subst p
      exact min_le_left _ _
    · exact le_trans (min_le_right _ _) (ih tail)

theorem excess_iff (h : X → ℚ) (A : Code X) (e : ℚ) :
    excess h A ≤ e ↔ 0 ≤ e ∧ ∀ p ∈ A, h p.1 - p.2 ≤ e := by
  induction A with
  | nil => simp [excess]
  | cons p c ih =>
    obtain ⟨a,b⟩ := p
    simp only [excess, max_le_iff, ih, List.forall_mem_cons]
    exact ⟨fun ⟨s,t,u⟩ => ⟨t,s,u⟩, fun ⟨t,s,u⟩ => ⟨s,t,u⟩⟩

theorem dominated (S : RationalSpace X) {L e : ℚ} (A : Code X) {h : X → ℚ}
    (hc : ∀ x, h x ≤ 1) (hl : lip S L h) (he : 0 ≤ e)
    (ha : ∀ p ∈ A, h p.1 - p.2 ≤ e) (x : X) : h x-e ≤ eval S L A x := by
  induction A with
  | nil => have hn := hc x; simp only [eval]; linarith
  | cons p c ih =>
    obtain ⟨a,b⟩ := p
    have hn := ha (a,b) List.mem_cons_self
    change h a - b ≤ e at hn
    exact le_min (by linarith [hl x a]) (ih (fun q hq => ha q (List.mem_cons_of_mem _ hq)))

theorem dist_spec (S : RationalSpace X) {L : ℚ} (hL : 0 ≤ L) (A B : Code X) (e : ℚ) :
    dist S L A B ≤ e ↔ 0 ≤ e ∧ ∀ x,
      eval S L B x - eval S L A x ≤ e ∧ eval S L A x - eval S L B x ≤ e := by
  simp only [dist, max_le_iff, excess_iff]
  constructor
  · intro ⟨⟨he,ab⟩,_,ba⟩
    refine ⟨he,fun x => ⟨?_,?_⟩⟩
    · linarith [dominated S A (eval_cap S L B) (eval_lip S hL B) he ab x]
    · linarith [dominated S B (eval_cap S L A) (eval_lip S hL A) he ba x]
  · intro ⟨he,hab⟩
    refine ⟨⟨he,?_⟩,he,?_⟩
    · rintro ⟨a,b⟩ hm
      have ha := eval_anchor S L A hm a
      rw [S.self] at ha
      dsimp only
      linarith [(hab a).1]
    · rintro ⟨a,b⟩ hm
      have hb := eval_anchor S L B hm a
      rw [S.self] at hb
      dsimp only
      linarith [(hab a).2]

/-- Produces a rational pseudometric for iterating the construction. -/
def codeSpace (S : RationalSpace X) (L : ℚ) (hL : 0 ≤ L) : RationalSpace (Code X) where
  d := dist S L
  self A := by
    apply le_antisymm
    · exact (dist_spec S hL A A 0).2 ⟨le_refl _, fun x => by simp⟩
    · exact ((dist_spec S hL A A _).1 (le_refl _)).1
  symm A B := max_comm _ _
  tri A B C := by
    obtain ⟨hp,p⟩ := (dist_spec S hL A B _).1 (le_refl _)
    obtain ⟨hq,q⟩ := (dist_spec S hL B C _).1 (le_refl _)
    apply (dist_spec S hL A C _).2
    refine ⟨add_nonneg hp hq, fun x => ⟨?_,?_⟩⟩
    · linarith [(p x).1, (q x).1]
    · linarith [(p x).2, (q x).2]

/-- Valid codes represent unit-interval-valued functions. -/
def Valid (A : Code X) := ∀ p ∈ A, 0 ≤ p.2 ∧ p.2 ≤ 1
abbrev UnitCode (X : Type) := {A : Code X // Valid A}

theorem eval_nonneg (S : RationalSpace X) {L : ℚ} (hL : 0 ≤ L) (A : Code X)
    (ok : Valid A) (x : X) : 0 ≤ eval S L A x := by
  induction A with
  | nil => exact zero_le_one
  | cons p c ih =>
    obtain ⟨a,b⟩ := p
    exact le_min (add_nonneg (ok (a,b) List.mem_cons_self).1 (mul_nonneg hL (nonnegDist S x a)))
      (ih (fun q hq => ok q (List.mem_cons_of_mem _ hq)))

def unitCodeSpace (S : RationalSpace X) (L : ℚ) (hL : 0 ≤ L) : RationalSpace (UnitCode X) where
  d A B := (codeSpace S L hL).d A.val B.val
  self A := (codeSpace S L hL).self A.val
  symm A B := (codeSpace S L hL).symm A.val B.val
  tri A B C := (codeSpace S L hL).tri A.val B.val C.val

/-- Finite noisy data yield an inner function-space net. -/
theorem cover (S : RationalSpace X) {L δ η : ℚ} (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (A : Code X) (f : X → ℚ) (hcap : ∀ x, f x ≤ 1) (hf : lip S L f)
    (samples : ∀ p ∈ A, f p.1 - p.2 ≤ δ ∧ p.2 - f p.1 ≤ δ)
    (net : ∀ x, ∃ p ∈ A, S.d x p.1 ≤ η) (x : X) :
    f x - δ ≤ eval S L A x ∧ eval S L A x ≤ f x + δ + 2*L*η := by
  refine ⟨dominated S A hcap hf hδ (fun p hp => (samples p hp).1) x, ?_⟩
  obtain ⟨⟨a,b⟩,hm,hn⟩ := net x
  change S.d x a ≤ η at hn
  have hu := (samples (a,b) hm).2
  change b-f a ≤ δ at hu
  have hl := hf a x
  rw [S.symm a x] at hl
  linarith [eval_anchor S L A hm x, mul_le_mul_of_nonneg_left hn hL]

/-- A feasible fit at tolerance e is itself an explicit candidate map. -/
def Fits (S : RationalSpace X) (L e : ℚ) (u f : X → ℚ) : Prop :=
  lip S L f ∧ ∀ x, (0 ≤ f x ∧ f x ≤ 1) ∧ (f x - u x ≤ e ∧ u x - f x ≤ e)

theorem pull_fit {Y : Type} {S : RationalSpace X} {T : RationalSpace Y}
    (r : Y → X) (hr : ∀ a b, S.d (r a) (r b) ≤ T.d a b)
    {L e : ℚ} (hL : 0 ≤ L) {u f : X → ℚ} (h : Fits S L e u f) :
    Fits T L e (u ∘ r) (f ∘ r) := by
  refine ⟨?_, fun y => h.2 (r y)⟩
  intro a b
  exact le_trans (h.1 (r a) (r b)) (add_le_add_right (mul_le_mul_of_nonneg_left (hr a b) hL) _)

theorem fits_retract {Y : Type} (S : RationalSpace X) (T : RationalSpace Y)
    (r : Y → X) (s : X → Y) (hr : ∀ a b, S.d (r a) (r b) ≤ T.d a b)
    (hs : ∀ a b, T.d (s a) (s b) ≤ S.d a b) (split : ∀ x, r (s x) = x)
    {L e : ℚ} (hL : 0 ≤ L) (u : X → ℚ) :
    (∃ f, Fits S L e u f) ↔ ∃ h, Fits T L e (u ∘ r) h := by
  constructor
  · rintro ⟨f,hf⟩
    exact ⟨f ∘ r, pull_fit r hr hL hf⟩
  · rintro ⟨g,hg⟩
    have h := pull_fit s hs hL hg
    have hsplit : (u ∘ r) ∘ s = u := funext (fun x => congrArg u (split x))
    exact ⟨g ∘ s, hsplit ▸ h⟩

#print axioms unitCodeSpace
#print axioms cover
end Precision.FunctionSpace
