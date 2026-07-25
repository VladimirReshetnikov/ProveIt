import FiniteMatrixNoncharacterizability.Dugundji

/-!
# Kripke soundness and the branching countermodel

The countermodel has a root and one incomparable leaf for each atom in
Gödel's formula.  At leaf `i`, exactly atom `pᵢ` is forced.  Hence no two
distinct atoms are equivalent at the root.
-/

namespace LeanProofs
namespace FiniteMatrixNoncharacterizability

open NaturalDeduction
open NaturalDeduction.Formula

/-- A Kripke model with a reflexive-transitive accessibility relation and a
persistent atomic valuation. -/
structure KripkeModel (α : Type u) where
  World : Type v
  le : World → World → Prop
  le_refl : ∀ w, le w w
  le_trans : ∀ {u v w}, le u v → le v w → le u w
  atom : World → α → Prop
  atom_mono : ∀ {w w' a}, le w w' → atom w a → atom w' a

namespace KripkeModel

/-- Standard intuitionistic forcing. -/
def Forces (K : KripkeModel α) (w : K.World) : Formula α → Prop
  | .atom a => K.atom w a
  | .falsum => False
  | p ⋏ q => K.Forces w p ∧ K.Forces w q
  | p ⋎ q => K.Forces w p ∨ K.Forces w q
  | p ⇒ q => ∀ w', K.le w w' → K.Forces w' p → K.Forces w' q

/-- Forcing persists along accessibility. -/
theorem forces_mono (K : KripkeModel α) {w w' : K.World} (hww' : K.le w w')
    (p : Formula α) : K.Forces w p → K.Forces w' p := by
  induction p generalizing w w' with
  | atom a => exact K.atom_mono hww'
  | falsum => exact fun h => h.elim
  | conj p q ihp ihq =>
      intro h
      exact ⟨ihp hww' h.1, ihq hww' h.2⟩
  | disj p q ihp ihq =>
      intro h
      exact h.elim (fun hp => Or.inl (ihp hww' hp))
        (fun hq => Or.inr (ihq hww' hq))
  | impl p q ihp ihq =>
      intro h w'' hw'w'' hp
      exact h w'' (K.le_trans hww' hw'w'') hp

/-- A world forces a context when it forces each assumption in it. -/
def ForcesContext (K : KripkeModel α) (w : K.World) (Γ : Context α) : Prop :=
  ∀ {p}, p ∈ Γ → K.Forces w p

theorem forcesContext_mono (K : KripkeModel α) {w w' : K.World}
    (hww' : K.le w w') {Γ : Context α} (hΓ : K.ForcesContext w Γ) :
    K.ForcesContext w' Γ := by
  intro p hp
  exact K.forces_mono hww' p (hΓ hp)

/-- Extending a forced context by a forced assumption keeps it forced. -/
theorem forcesContext_cons (K : KripkeModel α) {w : K.World} {p : Formula α}
    {Γ : Context α} (hp : K.Forces w p) (hΓ : K.ForcesContext w Γ) :
    K.ForcesContext w (p :: Γ) := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs
  · exact hp
  · exact hΓ hs

/-- Soundness of the shared intuitionistic natural-deduction calculus for
Kripke semantics. -/
theorem intuitionistic_sound {Γ : Context α} {p : Formula α}
    (h : IntuitionisticallyDerives Γ p) (K : KripkeModel α) (w : K.World)
    (hΓ : K.ForcesContext w Γ) : K.Forces w p := by
  induction h generalizing w with
  | assumption hp => exact hΓ hp
  | logicalAxiom hp => exact hp.elim
  | falseElim _ ih => exact (ih w hΓ).elim
  | andIntro _ _ ihp ihq => exact ⟨ihp w hΓ, ihq w hΓ⟩
  | andElimLeft _ ih => exact (ih w hΓ).1
  | andElimRight _ ih => exact (ih w hΓ).2
  | orIntroLeft _ ih => exact Or.inl (ih w hΓ)
  | orIntroRight _ ih => exact Or.inr (ih w hΓ)
  | orElim _ _ _ ihpq ihp ihq =>
      exact (ihpq w hΓ).elim
        (fun hp => ihp w (K.forcesContext_cons hp hΓ))
        (fun hq => ihq w (K.forcesContext_cons hq hΓ))
  | impIntro _ ih =>
      intro w' hww' hp
      exact ih w' (K.forcesContext_cons hp (K.forcesContext_mono hww' hΓ))
  | impElim _ _ ihpq ihp => exact ihpq w hΓ w (K.le_refl w) (ihp w hΓ)

end KripkeModel

/-- Worlds of the finite branching countermodel: `none` is the root and
`some i` is leaf `i`. -/
abbrev BranchWorld (leaves : Nat) := Option (Fin leaves)

def branchLE : BranchWorld leaves → BranchWorld leaves → Prop
  | none, _ => True
  | some i, some j => i = j
  | some _, none => False

def branchAtom : BranchWorld leaves → Nat → Prop
  | none, _ => False
  | some i, a => i.val = a

/-- The root with `leaves` incomparable one-atom leaves. -/
def branchModel (leaves : Nat) : KripkeModel Nat where
  World := BranchWorld leaves
  le := branchLE
  le_refl := by
    intro w
    cases w <;> simp [branchLE]
  le_trans := by
    intro u v w huv hvw
    cases u <;> cases v <;> cases w <;> simp_all [branchLE]
  atom := branchAtom
  atom_mono := by
    intro w w' a hww' ha
    cases w <;> cases w' <;> simp_all [branchLE, branchAtom]

theorem branch_root_not_forces_biconditional {leaves i j : Nat}
    (hi : i < leaves) (hne : i ≠ j) :
    ¬ (branchModel leaves).Forces none
      (biconditional (.atom i) (.atom j)) := by
  intro h
  have himpl := h.1
  let wi : Fin leaves := ⟨i, hi⟩
  have hj : (branchModel leaves).Forces (some wi) (.atom j) :=
    himpl (some wi) (by trivial) (by rfl)
  exact hne (by simpa [KripkeModel.Forces, branchModel, branchAtom] using hj)

theorem branch_root_not_forces_pairRow {leaves j k : Nat}
    (hj : j < leaves) (hk : k ≤ j) :
    ¬ (branchModel leaves).Forces none (pairRow j k) := by
  induction k with
  | zero => simp [pairRow, KripkeModel.Forces]
  | succ k ih =>
      intro h
      rcases h with hpair | hrow
      · exact branch_root_not_forces_biconditional (by omega) (by omega) hpair
      · exact ih (by omega) hrow

/-- The explicit branching model refutes `dugundji n` at its root. -/
theorem branch_root_not_forces_dugundji {leaves n : Nat} (hn : n < leaves) :
    ¬ (branchModel leaves).Forces none (dugundji n) := by
  induction n with
  | zero => simp [dugundji, KripkeModel.Forces]
  | succ n ih =>
      intro h
      rcases h with hrow | hdugundji
      · exact branch_root_not_forces_pairRow hn (Nat.le_refl _) hrow
      · exact ih (by omega) hdugundji

/-- **Kripke half of Gödel's theorem.**  The formula forced by every sound
`n`-valued matrix is not an IPC theorem. -/
theorem dugundji_not_intuitionistically_derivable (n : Nat) :
    ¬ IntuitionisticallyDerives [] (dugundji n) := by
  intro h
  have hforced := KripkeModel.intuitionistic_sound h (branchModel (n + 1)) none
    (by simp [KripkeModel.ForcesContext])
  exact branch_root_not_forces_dugundji (Nat.lt_succ_self n) hforced

end FiniteMatrixNoncharacterizability
end LeanProofs
