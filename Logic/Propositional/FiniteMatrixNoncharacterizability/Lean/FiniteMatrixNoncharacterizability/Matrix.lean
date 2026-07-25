import FiniteMatrixNoncharacterizability.Dugundji
import FiniteMatrixNoncharacterizability.Pigeonhole

/-!
# Deterministic truth-functional matrices

Designatedness is deliberately arbitrary: it may designate one value, many
values, or none.  Likewise, no algebraic laws are built into the four truth
functions.  The impossibility proof assumes only theorem-level soundness for
IPC, which is weaker than requiring every natural-deduction rule to preserve
semantic consequence.
-/

namespace LeanProofs
namespace FiniteMatrixNoncharacterizability

open NaturalDeduction
open NaturalDeduction.Formula

/-- A deterministic truth-functional matrix for propositional logic. -/
structure LogicalMatrix (V : Type u) where
  falsum : V
  conj : V → V → V
  disj : V → V → V
  impl : V → V → V
  designated : V → Prop

/-- Explicit finite evidence: the carrier injects into `Fin n`.

This slightly more general representation (“at most `n` values”) avoids any
dependence on a finite-cardinality library. -/
structure FiniteEncoding (V : Type u) (n : Nat) where
  encode : V → Fin n
  injective : Function.Injective encode

namespace LogicalMatrix

/-- Evaluation in a logical matrix under an atom valuation. -/
def eval (m : LogicalMatrix V) (v : α → V) : Formula α → V
  | .atom a => v a
  | .falsum => m.falsum
  | p ⋏ q => m.conj (eval m v p) (eval m v q)
  | p ⋎ q => m.disj (eval m v p) (eval m v q)
  | p ⇒ q => m.impl (eval m v p) (eval m v q)

/-- Matrix validity quantifies over every valuation of the atoms. -/
def Valid (m : LogicalMatrix V) (p : Formula α) : Prop :=
  ∀ v : α → V, m.designated (m.eval v p)

/-- Evaluating a renamed formula under `v` agrees with evaluating the original
formula under any valuation that matches `v ∘ r` pointwise.  The congruence and
renaming laws below are both instances of this single induction. -/
theorem eval_rename_congr (m : LogicalMatrix V) {v : β → V} {v' : α → V}
    (r : α → β) (h : ∀ a, v (r a) = v' a) (p : Formula α) :
    m.eval v (rename r p) = m.eval v' p := by
  induction p with
  | atom a => exact h a
  | falsum => rfl
  | conj p q ihp ihq => simp only [rename, eval, ihp, ihq]
  | disj p q ihp ihq => simp only [rename, eval, ihp, ihq]
  | impl p q ihp ihq => simp only [rename, eval, ihp, ihq]

/-- Pointwise-equal valuations evaluate every formula equally. -/
theorem eval_congr (m : LogicalMatrix V) {v₁ v₂ : α → V}
    (h : ∀ a, v₁ a = v₂ a) (p : Formula α) :
    m.eval v₁ p = m.eval v₂ p :=
  (m.eval_rename_congr (fun a => a) (fun _ => rfl) p).symm.trans
    (m.eval_rename_congr (fun a => a) h p)

/-- Syntactic atom renaming agrees with precomposition of a valuation. -/
theorem eval_rename (m : LogicalMatrix V) (v : β → V) (r : α → β)
    (p : Formula α) :
    m.eval v (rename r p) = m.eval (fun a => v (r a)) p :=
  m.eval_rename_congr r (fun _ => rfl) p

end LogicalMatrix

/-- Every intuitionistic theorem is valid in the matrix.  This is the weakest
soundness hypothesis needed by the finite-matrix impossibility argument. -/
def SoundForIPCTheorems (m : LogicalMatrix V) : Prop :=
  ∀ {p : Formula Nat}, IntuitionisticallyDerives [] p → m.Valid p

/-- A valuation designates every member of a finite context. -/
def DesignatesContext (m : LogicalMatrix V) (v : Nat → V) (Γ : Context Nat) : Prop :=
  ∀ {p}, p ∈ Γ → m.designated (m.eval v p)

/-- Matrix consequence for a finite context. -/
def MatrixEntails (m : LogicalMatrix V) (Γ : Context Nat) (p : Formula Nat) : Prop :=
  ∀ v, DesignatesContext m v Γ → m.designated (m.eval v p)

/-- The customary stronger rule-preservation assumption: every IPC sequent
derivable by natural deduction is valid as a matrix consequence. -/
def SoundForIPCSequents (m : LogicalMatrix V) : Prop :=
  ∀ {Γ : Context Nat} {p : Formula Nat},
    IntuitionisticallyDerives Γ p → MatrixEntails m Γ p

/-- Full natural-deduction rule preservation implies the theorem-level
soundness used by the impossibility theorem. -/
theorem sequent_sound_implies_theorem_sound (m : LogicalMatrix V)
    (h : SoundForIPCSequents m) : SoundForIPCTheorems m := by
  intro p hp v
  exact h hp v (by simp [DesignatesContext])

/-- Every matrix-valid formula is an intuitionistic theorem. -/
def CompleteForIPCTheorems (m : LogicalMatrix V) : Prop :=
  ∀ {p : Formula Nat}, m.Valid p → IntuitionisticallyDerives [] p

/-- A characteristic matrix gives exactly the IPC theorems. -/
def CharacteristicForIPC (m : LogicalMatrix V) : Prop :=
  ∀ p : Formula Nat, m.Valid p ↔ IntuitionisticallyDerives [] p

theorem characteristic_sound (m : LogicalMatrix V) (h : CharacteristicForIPC m) :
    SoundForIPCTheorems m := by
  intro p hp
  exact (h p).2 hp

theorem characteristic_complete (m : LogicalMatrix V) (h : CharacteristicForIPC m) :
    CompleteForIPCTheorems m := by
  intro p hp
  exact (h p).1 hp

/-- Replace the atom `j` by the atom `i`, fixing every other atom. -/
def identifyAtom (i j : Nat) (a : Nat) : Nat :=
  if a = j then i else a

theorem valuation_identifyAtom {v : Nat → V} {i j : Nat} (h : v i = v j) :
    ∀ a, v (identifyAtom i j a) = v a := by
  intro a
  by_cases ha : a = j
  · subst a
    simpa [identifyAtom] using h
  · simp [identifyAtom, ha]

/-- A collision among the values of two atoms makes the corresponding Gödel
formula designated, using only theorem-level IPC soundness. -/
theorem designated_dugundji_of_collision (m : LogicalMatrix V)
    (hs : SoundForIPCTheorems m) (v : Nat → V) {i j n : Nat}
    (hij : i < j) (hjn : j ≤ n) (hvalue : v i = v j) :
    m.designated (m.eval v (dugundji n)) := by
  let r := identifyAtom i j
  have hr : r i = r j := by simp [r, identifyAtom, Nat.ne_of_lt hij]
  have hderives : IntuitionisticallyDerives [] (rename r (dugundji n)) :=
    intuitionistic_renamed_dugundji_of_collision r hij hjn hr
  have hdesignated := hs hderives v
  rw [LogicalMatrix.eval_rename] at hdesignated
  have heval : m.eval (fun a => v (r a)) (dugundji n) =
      m.eval v (dugundji n) :=
    m.eval_congr (valuation_identifyAtom hvalue) (dugundji n)
  rwa [heval] at hdesignated

/-- **Finite-matrix half of Gödel's theorem.**

If the carrier injects into `Fin n`, theorem-level IPC soundness forces
the `(n + 1)`-atom Gödel formula to be matrix-valid. -/
theorem finite_sound_matrix_validates_dugundji (m : LogicalMatrix V)
    (e : FiniteEncoding V n) (hs : SoundForIPCTheorems m) :
    m.Valid (dugundji n) := by
  intro v
  let f : Fin (n + 1) → Fin n := fun i => e.encode (v i.val)
  obtain ⟨i, j, hij, hvalue⟩ := fin_pigeonhole n f
  have hv : v i.val = v j.val := e.injective hvalue
  have hvalNe : i.val ≠ j.val := by
    intro h
    exact hij (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hvalNe with hlt | hgt
  · exact designated_dugundji_of_collision m hs v hlt (by omega) hv
  · exact designated_dugundji_of_collision m hs v hgt (by omega) hv.symm

/-- Every logical matrix has a nonempty carrier, witnessed by its interpretation
of falsity. -/
theorem logicalMatrix_carrier_nonempty (m : LogicalMatrix V) : Nonempty V :=
  ⟨m.falsum⟩

end FiniteMatrixNoncharacterizability
end LeanProofs
