import Mathlib.Tactic.Linarith

/-! The real-part algebra of reflection is independent of analytic continuation.
The index type permits functional equations exchanging a character with its dual.
For a one-function application take the index type to be Unit. -/
namespace RiemannIPRA.StripReflection

section
variable {R A I : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

def StripLine (re : A → R) (Z : I → A → Prop) : Prop :=
  ∀ i s, 0 < re s → re s < 1 → Z i s → re s = 1/2

def RightFree (re : A → R) (Z : I → A → Prop) : Prop :=
  ∀ i s, 1/2 < re s → re s < 1 → ¬ Z i s

def LeftFree (re : A → R) (Z : I → A → Prop) : Prop :=
  ∀ i s, 0 < re s → re s < 1/2 → ¬ Z i s

/-- Reflection of a zero may land in another member of the family. -/
structure Reflects (re : A → R) (Z : I → A → Prop) where
  dual : I → I
  mirror : A → A
  coordinate : ∀ s, re (mirror s) = 1 - re s
  zero : ∀ i s, 0 < re s → re s < 1 → Z i s → Z (dual i) (mirror s)

/-- A functional equation supplies the direction of zero propagation even
if its multiplying factor has zeros. -/
def fromFunctionalEquation {V : Type*} [MulZeroClass V] (re : A → R) (F W : I → A → V)
    (dual : I → I) (mirror : A → A) (coord : ∀ s, re (mirror s) = 1-re s)
    (eqn : ∀ i s, 0 < re s → re s < 1 → F (dual i) (mirror s) = W i s * F i s) :
    Reflects re (fun i s => F i s = 0) where
  dual := dual
  mirror := mirror
  coordinate := coord
  zero := by intro i s h0 h1 hz; rw [eqn i s h0 h1,hz,mul_zero]

omit [IsStrictOrderedRing R] in
/-- Multiplication by a factor nonzero in the open strip preserves its
zero-line assertion. For clearing a pole at 1 the factor is s−1. -/
theorem removeFactor {V : Type*} [MulZeroClass V] [NoZeroDivisors V]
    (re : A → R) (F C : I → A → V) (hc : ∀ i s, 0 < re s → re s < 1 → C i s ≠ 0) :
    StripLine re (fun i s => C i s*F i s = 0) ↔ StripLine re (fun i s => F i s = 0) := by
  constructor
  · intro h i s h0 h1 hz
    exact h i s h0 h1 (by change C i s * F i s = 0; rw [hz,mul_zero])
  · intro h i s h0 h1 hz
    exact h i s h0 h1 ((mul_eq_zero.mp hz).resolve_left (hc i s h0 h1))

theorem line_iff_two_halves (re : A → R) (Z : I → A → Prop) :
    StripLine re Z ↔ RightFree re Z ∧ LeftFree re Z := by
  constructor
  · intro line
    constructor
    · intro i s hr h1 hz
      have h0 : 0 < re s := by linarith
      have := line i s h0 h1 hz
      linarith
    · intro i s h0 hl hz
      have h1 : re s < 1 := by linarith
      have := line i s h0 h1 hz
      linarith
  · rintro ⟨right, left⟩ i s h0 h1 hz
    rcases lt_trichotomy (re s) (1/2) with hl | he | hr
    · exact (left i s h0 hl hz).elim
    · exact he
    · exact (right i s hr h1 hz).elim

theorem halves_iff {re : A → R} {Z : I → A → Prop} (h : Reflects re Z) :
    RightFree re Z ↔ LeftFree re Z := by
  constructor
  · intro right i s h0 hl hz
    have eq := h.coordinate s
    have h1 : re s < 1 := by linarith
    exact right (h.dual i) (h.mirror s) (by linarith) (by linarith) (h.zero i s h0 h1 hz)
  · intro left i s hr h1 hz
    have eq := h.coordinate s
    have h0 : 0 < re s := by linarith
    exact left (h.dual i) (h.mirror s) (by linarith) (by linarith) (h.zero i s h0 h1 hz)

theorem line_iff_right {re : A → R} {Z : I → A → Prop} (h : Reflects re Z) :
    StripLine re Z ↔ RightFree re Z := by
  rw [line_iff_two_halves]
  exact ⟨And.left, fun r => ⟨r,(halves_iff h).mp r⟩⟩

theorem line_iff_left {re : A → R} {Z : I → A → Prop} (h : Reflects re Z) :
    StripLine re Z ↔ LeftFree re Z := (line_iff_right h).trans (halves_iff h)
end

end RiemannIPRA.StripReflection
