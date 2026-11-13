import Foundation.FirstOrder.Arithmetic.IOpen.Basic
import Mathlib.Tactic.Ring
import BusyBeaver.ZFC.Code254

/-!
The literal Cantor pairing used by C254, represented over arbitrary IOpen
models. Foundation's own Szudzik pairing is deliberately not used here.
This is a fixed arithmetic graph package, not the full PA machine theorem.
-/

namespace SetTheory.BusyBeaver.ZFC.ArithmeticCantor

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

noncomputable def triangle (s : V) : V := s * (s + 1) / 2

lemma triangle_double (s : V) : 2 * triangle s = s * (s + 1) := by
  apply (mul_div_self_of_dvd).2
  rcases even_or_odd s with ⟨r, h | h⟩
  · refine ⟨r * (s + 1), ?_⟩
    rw [h]
    ring
  · refine ⟨s * (r + 1), ?_⟩
    rw [h]
    ring

lemma triangle_succ (s : V) : triangle (s + 1) = triangle s + s + 1 := by
  apply mul_left_cancel₀ (show (2 : V) ≠ 0 by simp)
  rw [mul_add, mul_add, triangle_double, triangle_double]
  ring

lemma triangle_mono {s t : V} (h : s ≤ t) : triangle s ≤ triangle t := by
  apply (mul_le_mul_iff_right₀ (show (0 : V) < 2 by simp)).mp
  rw [triangle_double, triangle_double]
  exact mul_le_mul h (by simpa [add_comm] using add_le_add_right h 1) (by simp) (by simp)

lemma le_triangle (s : V) : s ≤ triangle s := by
  rcases Arithmetic.zero_le s with (rfl | hs)
  · simp [triangle]
  · have h1 : 1 ≤ s := by simpa using (lt_iff_succ_le.mp hs)
    have hm : 2 * s ≤ s * (s + 1) := by
      have := mul_le_mul_of_nonneg_left (add_le_add_right h1 1) (Arithmetic.zero_le s)
      simpa [one_add_one_eq_two, mul_comm, add_comm] using this
    apply (mul_le_mul_iff_right₀ (show (0 : V) < 2 by simp)).mp
    rwa [triangle_double]

noncomputable def cantor (a b : V) : V := triangle (a + b) + b

lemma cantor_double (a b : V) :
    2 * cantor a b = (a + b) * (a + b + 1) + 2 * b := by
  unfold cantor
  rw [mul_add, triangle_double]

lemma cantor_graph {p a b : V} :
    p = cantor a b ↔ 2 * p = (a + b) * (a + b + 1) + 2 * b := by
  have h := cantor_double a b
  constructor
  · rintro rfl; exact h
  · intro hp
    exact mul_left_cancel₀ (show (2 : V) ≠ 0 by simp) (hp.trans h.symm)

lemma components_le (a b : V) : a ≤ cantor a b ∧ b ≤ cantor a b := by
  constructor
  · exact le_trans (by simp : a ≤ a + b)
      (le_trans (le_triangle (a + b)) (by simp [cantor]))
  · simp [cantor]

lemma diagonal_lt {a b c d : V} (h : a + b < c + d) : cantor a b < cantor c d := by
  calc
    cantor a b = triangle (a + b) + b := rfl
    _ ≤ triangle (a + b) + (a + b) := _root_.add_le_add le_rfl (show b ≤ a + b from by simp)
    _ < triangle (a + b) + (a + b) + 1 := lt_add_one _
    _ = triangle (a + b + 1) := (triangle_succ _).symm
    _ ≤ triangle (c + d) := triangle_mono (lt_iff_succ_le.mp h)
    _ ≤ cantor c d := by simp [cantor]

lemma cantor_injective {a b c d : V} (h : cantor a b = cantor c d) : a = c ∧ b = d := by
  have hs : a + b = c + d := by
    rcases lt_trichotomy (a + b) (c + d) with hl | he | hr
    · have := diagonal_lt hl; exact False.elim (by simpa [h] using this)
    · exact he
    · have := diagonal_lt hr; exact False.elim (by simpa [h] using this)
  have hb : b = d := by
    apply add_left_cancel (a := triangle (c + d))
    simpa only [cantor, hs] using h
  subst d
  exact ⟨add_right_cancel hs, rfl⟩

/-- A triangular interval exists at every model element, using open induction. -/
lemma diagonal_exists (p : V) : ∃ s, triangle s ≤ p ∧ p < triangle (s + 1) := by
  have counter : ¬(p + 1) * (p + 1 + 1) ≤ 2 * p := by
    apply not_le.mpr
    rw [←triangle_double]
    exact mul_lt_mul_of_pos_left (lt_of_lt_of_le (lt_add_one p) (le_triangle (p + 1))) (by simp)
  obtain ⟨s, hlow, hhigh⟩ := least_number
    (P := fun s : V => s * (s + 1) ≤ 2 * p)
    ⟨“s. s * (s + 1) ≤ 2 * &p”, by simp, by intro s; simp⟩
    (by simp) counter
  refine ⟨s, ?_, ?_⟩
  · apply (mul_le_mul_iff_right₀ (show (0 : V) < 2 by simp)).mp
    rwa [triangle_double]
  · apply (mul_lt_mul_iff_right₀ (show (0 : V) < 2 by simp)).mp
    rw [triangle_double]
    exact not_le.mp hhigh

lemma cantor_surjective (p : V) : ∃ a b, a ≤ p ∧ b ≤ p ∧ p = cantor a b := by
  obtain ⟨s, hlow, hhigh⟩ := diagonal_exists p
  have hb : p - triangle s ≤ s := by
    have hle : p ≤ triangle s + s := by
      rw [triangle_succ] at hhigh
      exact le_iff_lt_succ.mpr hhigh
    exact tsub_le_iff_right.mpr (by simpa [add_comm] using hle)
  have hsum : (s - (p - triangle s)) + (p - triangle s) = s := tsub_add_cancel_of_le hb
  have he : p = cantor (s - (p - triangle s)) (p - triangle s) := by
    simp only [cantor, hsum]
    exact (add_tsub_cancel_of_le hlow).symm
  obtain ⟨ha, hb⟩ := components_le (s - (p - triangle s)) (p - triangle s)
  exact ⟨_, _, by simpa [←he] using ha, by simpa [←he] using hb, he⟩

noncomputable def first (p : V) : V := (cantor_surjective p).choose
noncomputable def second (p : V) : V := (cantor_surjective p).choose_spec.choose

lemma projections_spec (p : V) :
    first p ≤ p ∧ second p ≤ p ∧ p = cantor (first p) (second p) :=
  (cantor_surjective p).choose_spec.choose_spec

@[simp] lemma cantor_projections (p : V) : cantor (first p) (second p) = p :=
  (projections_spec p).2.2.symm

@[simp] lemma first_cantor (a b : V) : first (cantor a b) = a :=
  (cantor_injective (cantor_projections (cantor a b))).1

@[simp] lemma second_cantor (a b : V) : second (cantor a b) = b :=
  (cantor_injective (cantor_projections (cantor a b))).2

/-- Output first, then the two inputs: the exact fixed bounded polynomial graph. -/
def pairDef : 𝚺₀.Semisentence 3 :=
  .mkSigma “p a b. 2 * p = (a + b) * (a + b + 1) + 2 * b”

instance cantor_defined : 𝚺₀-Function₂[V] cantor via pairDef := .mk fun v => by
  simp [pairDef, cantor_graph]

def firstDef : 𝚺₀.Semisentence 2 :=
  .mkSigma “a p. a ≤ p ∧ ∃ b <⁺ p, !pairDef p a b”

def secondDef : 𝚺₀.Semisentence 2 :=
  .mkSigma “b p. b ≤ p ∧ ∃ a <⁺ p, !pairDef p a b”

instance first_defined : 𝚺₀-Function₁[V] first via firstDef := .mk fun v => by
  simp [firstDef]
  constructor
  · rintro ⟨ha, b, hb, he⟩
    exact (cantor_injective (he.symm.trans (cantor_projections (v 1)).symm)).1
  · intro he
    exact ⟨by simpa [he] using (projections_spec (v 1)).1,
      second (v 1), (projections_spec (v 1)).2.1,
      by simpa [he] using (cantor_projections (v 1)).symm⟩

instance second_defined : 𝚺₀-Function₁[V] second via secondDef := .mk fun v => by
  simp [secondDef]
  constructor
  · rintro ⟨hb, a, ha, he⟩
    exact (cantor_injective (he.symm.trans (cantor_projections (v 1)).symm)).2
  · intro he
    exact ⟨by simpa [he] using (projections_spec (v 1)).2.1,
      first (v 1), (projections_spec (v 1)).1, by simpa [he] using (cantor_projections (v 1)).symm⟩

/-! ## Exact adapter to the standard natural-number implementation

The generic model's division and projections were chosen from existence proofs.
Their standard-Nat values are identified by recurrence and inverse uniqueness,
without an added arithmetic premise or a new division implementation assumption.
These all-input adapters do not arithmetize the whole evaluator or literal trace.
-/

@[simp] theorem triangle_nat (n : Nat) : triangle n = SetTheory.Cantor.tri n := by
  induction n with
  | zero => simp [triangle, SetTheory.Cantor.tri]
  | succ n ih =>
    change triangle (n + 1) = SetTheory.Cantor.tri n + n + 1
    rw [triangle_succ, ih]

/-- The pairing orientation is exactly the live numerical calculus's `P`. -/
@[simp] theorem cantor_nat (a b : Nat) : cantor a b = Code254.P a b := by
  simp only [cantor, triangle_nat, Code254.P, SetTheory.Cantor.toNat]
  exact Nat.add_comm _ _

/-- Both choice-defined inverse components agree with the actual recursive
anti-diagonal decoder on every natural, including zero. -/
theorem projections_nat (p : Nat) :
    (first p, second p) = SetTheory.Cantor.ofNat p := by
  apply SetTheory.Cantor.toNat_inj
  change Code254.P (first p) (second p) = SetTheory.Cantor.toNat (SetTheory.Cantor.ofNat p)
  rw [← cantor_nat, cantor_projections, SetTheory.Cantor.toNat_ofNat]

@[simp] theorem first_nat (p : Nat) : first p = (SetTheory.Cantor.ofNat p).1 :=
  congrArg Prod.fst (projections_nat p)

@[simp] theorem second_nat (p : Nat) : second p = (SetTheory.Cantor.ofNat p).2 :=
  congrArg Prod.snd (projections_nat p)

/-- The fixed polynomial graph represents the actual code pairing over Nat. -/
instance codeP_defined : HierarchySymbol.DefinedFunction₂ (V := Nat) 𝚺₀ Code254.P pairDef := by
  have he : (cantor : Nat → Nat → Nat) = Code254.P :=
    funext fun a => funext fun b => cantor_nat a b
  rw [← he]
  exact cantor_defined

/-- The same fixed bounded inverse graph represents the literal left decoder. -/
instance codeFirst_defined :
    HierarchySymbol.DefinedFunction₁ (V := Nat) 𝚺₀ (fun p => (SetTheory.Cantor.ofNat p).1) firstDef := by
  have he : (first : Nat → Nat) = fun p => (SetTheory.Cantor.ofNat p).1 :=
    funext first_nat
  rw [← he]
  exact first_defined

/-- The same fixed bounded inverse graph represents the literal right decoder. -/
instance codeSecond_defined :
    HierarchySymbol.DefinedFunction₁ (V := Nat) 𝚺₀ (fun p => (SetTheory.Cantor.ofNat p).2) secondDef := by
  have he : (second : Nat → Nat) = fun p => (SetTheory.Cantor.ofNat p).2 :=
    funext second_nat
  rw [← he]
  exact second_defined

/-- An explicit familiar standard-Nat graph, with no model parameter. -/
theorem codeP_graph (p a b : Nat) :
    p = Code254.P a b ↔ 2 * p = (a + b) * (a + b + 1) + 2 * b := by
  have h := cantor_graph (V := Nat) (p := p) (a := a) (b := b)
  rw [← numeral_two_eq_two] at h
  simpa only [cantor_nat, Nat.numeral_eq] using h

end SetTheory.BusyBeaver.ZFC.ArithmeticCantor
