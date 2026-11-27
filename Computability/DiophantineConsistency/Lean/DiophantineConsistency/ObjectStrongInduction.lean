import BoundedZFCConsistency.OmegaRecursion

/-! # Strong induction for displayed formulas over internal omega

This is definable strong induction. It does not make the internal carrier
externally well-founded or permit induction on an arbitrary external predicate.
-/
namespace DiophantineConsistency.ObjectStrongInduction
open SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency
universe u
variable {V : Type u} {mem : V → V → Prop}

private def bodyMap : Nat → Nat
  | 0 => 0
  | k+1 => k+2

/-- At induction coordinate `n`, every member below it satisfies `phi`. -/
def belowForm (phi : Form) : Form :=
  fAll (fImp (fMem 0 1) (rename bodyMap phi))

theorem belowForm_spec (phi : Form) (n : V) (ee : Nat → V) :
    Sat mem (scons n ee) (belowForm phi) ↔
      ∀ m,mem m n → Sat mem (scons m ee) phi := by
  change (∀ m,mem m n → Sat mem (scons m (scons n ee)) (rename bodyMap phi)) ↔ _
  apply forall_congr'
  intro m
  apply imp_congr_right
  intro _
  rw [Sat_rename]
  apply Sat_ext
  intro i
  cases i <;> rfl

theorem strong_induction (H : ZFAxioms mem) (phi : Form) (ee : Nat → V)
    (hstep : ∀ n,mem n (omegaV H) →
      (∀ m,mem m n → Sat mem (scons m ee) phi) → Sat mem (scons n ee) phi) :
    ∀ n,mem n (omegaV H) → Sat mem (scons n ee) phi := by
  have hind : ∀ n,mem n (omegaV H) → Sat mem (scons n ee) (belowForm phi) := by
    apply omega_ind H (belowForm phi) ee
    · apply (belowForm_spec phi (vempty H) ee).mpr
      intro m hm
      exact False.elim (vempty_spec H m hm)
    · intro n hn ih
      apply (belowForm_spec phi (vsucc H n) ee).mpr
      intro m hm
      rcases (vsucc_spec H n m).mp hm with hlt | heq
      · exact (belowForm_spec phi n ee).mp ih m hlt
      · subst m
        exact hstep n hn ((belowForm_spec phi n ee).mp ih)
  intro n hn
  exact hstep n hn ((belowForm_spec phi n ee).mp (hind n hn))

end DiophantineConsistency.ObjectStrongInduction
