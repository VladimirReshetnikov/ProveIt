import BusyBeaver.ZFC.KQ1Model
import BusyBeaver.ZFC.ProfileAxioms
import ZF.Zf

/-!
Actual formula-indexed Separation in the bisimulation quotient of a `QHyp` structure.

The collection instance below is a literal equality-free Form matrix;
there is no collection hypothesis for arbitrary semantic predicates.
The invariant predicate is the checked quotient translation of the
requested formula. A quotient environment is lifted to representatives,
and sat_quotient supplies the actual first-order Separation property.

This is one axiom schema, not the full quotient ZF interpretation. The
argument follows the trace construction in the attributed upstream
S_ax.v:sep_core at 297ab8df7e5de329605c3875b4934643b371a5e3,
using the existing equality-free profile resources.
-/

namespace SetTheory.BusyBeaver.ZFC.KQ1Separation

open KQHyp

open Form Profile ProfileCollection ProfileComposition ProfileAxioms
open ProfileSyntax ProfileModel CompositionModel DeepPositiveClosure

universe u
variable {V : Type u}

/-- Input stays at 0; parameter k moves past the output and domain slots. -/
def separationRename : Nat → Nat
  | 0 => 0
  | k + 1 => k + 3

def separationChoiceForm (phi : Form) : Form :=
  fAnd (fMem 0 2) (fAnd (sameForm 1 0)
    (rename separationRename (KQ1Model.translate phi)))

theorem equalityFree_separationChoiceForm (phi : Form) :
    EqualityFree (separationChoiceForm phi) :=
  ⟨True.intro, ⟨equalityFree_sameForm 1 0,
    equalityFree_rename (KQ1Model.translate phi) separationRename
      (KQ1Model.equalityFree_translate phi)⟩⟩

theorem sat_separationChoiceForm (mem : V → V → Prop) (phi : Form)
    (a : V) (env : Nat → V) (x y : V) :
    MatrixRelation mem (separationChoiceForm phi) (scons a env) x y ↔
      SeparationChoice mem a (fun z => KQ1Model.RelSat mem (scons z env) phi) x y := by
  have hr := Sat_rename_ext (mem := mem) (KQ1Model.translate phi) separationRename
    (scons x (scons y (scons a env))) (scons x env)
    (fun n => match n with | 0 => rfl | _ + 1 => rfl)
  exact and_congr Iff.rfl (and_congr (sat_sameForm mem _ 1 0)
    (hr.trans (KQ1Model.sat_translate mem phi (scons x env))))

theorem separation_instance (mem : V → V → Prop) (h : ModelsGIC mem)
    (a : V) (phi : Form) (env : Nat → V) :
    CollectionInstance mem
      (SeparationChoice mem a (fun z => KQ1Model.RelSat mem (scons z env) phi)) :=
  instance_of_matrix mem h (separationChoiceForm phi)
    (equalityFree_separationChoiceForm phi) (scons a env) _
    (sat_separationChoiceForm mem phi a env)

/-- Arbitrary actual source formulas supply interpreted Separation. -/
theorem interpreted_separation (mem : V → V → Prop) (witness : V)
    (h : QHyp mem) (a : V) (phi : Form) (env : Nat → V) :
    ∃ b, SubD mem b a ∧ ∀ z, Member mem z b ↔
      Member mem z a ∧ KQ1Model.RelSat mem (scons z env) phi := by
  apply separation_of_instance mem a (fun z => KQ1Model.RelSat mem (scons z env) phi)
    h.refl (fun _ _ _ => h.trans) _
    (separation_instance mem h.gic a phi env)
  intro x y hxy
  apply KQ1Model.relSat_congr mem witness h phi (scons x env) (scons y env)
  intro n
  cases n with
  | zero => exact hxy
  | succ n => exact h.refl (env n)

/-- Only a sequence of representatives of an already supplied quotient environment. -/
noncomputable def liftEnv (mem : V → V → Prop) (witness : V) (h : QHyp mem)
    (env : Nat → KQ1Model.Domain mem witness h) : Nat → V :=
  fun i => Classical.choose (Quotient.exists_rep (env i))

theorem mk_liftEnv (mem : V → V → Prop) (witness : V) (h : QHyp mem)
    (env : Nat → KQ1Model.Domain mem witness h) (i : Nat) :
    KQ1Model.mk mem witness h (liftEnv mem witness h env i) = env i :=
  Classical.choose_spec (Quotient.exists_rep (env i))

/-- The full quotient has Separation for every actual formula and parameter valuation.
This has exactly the semantic shape of the repository's ZFAxioms.sep field. -/
theorem quotient_separation (mem : V → V → Prop) (witness : V) (h : QHyp mem)
    (phi : Form) (env : Nat → KQ1Model.Domain mem witness h)
    (a : KQ1Model.Domain mem witness h) :
    ∃ b, ∀ x, KQ1Model.quotientMember mem witness h x b ↔
      KQ1Model.quotientMember mem witness h x a ∧
        SetTheory.Sat (KQ1Model.quotientMember mem witness h) (scons x env) phi := by
  induction a using Quotient.ind with
  | _ a =>
    let rawEnv := liftEnv mem witness h env
    obtain ⟨b, _, hb⟩ := interpreted_separation mem witness h a phi rawEnv
    refine ⟨KQ1Model.mk mem witness h b, ?_⟩
    intro x
    induction x using Quotient.ind with
    | _ x =>
      have he : (fun i => KQ1Model.mk mem witness h (rawEnv i)) = env := by
        funext i
        exact mk_liftEnv mem witness h env i
      have hs := KQ1Model.sat_quotient mem witness h phi (scons x rawEnv)
      rw [KQ1Model.mk_scons, he] at hs
      exact (hb x).trans (and_congr Iff.rfl hs.symm)

/-- Every repository Separation formula holds under every quotient valuation. -/
theorem quotient_sep_form (mem : V → V → Prop) (witness : V) (h : QHyp mem) :
    ∀ phi env, SetTheory.Sat (KQ1Model.quotientMember mem witness h) env (Sep_form phi) :=
  bridge_Sep.mpr (quotient_separation mem witness h)

end SetTheory.BusyBeaver.ZFC.KQ1Separation
