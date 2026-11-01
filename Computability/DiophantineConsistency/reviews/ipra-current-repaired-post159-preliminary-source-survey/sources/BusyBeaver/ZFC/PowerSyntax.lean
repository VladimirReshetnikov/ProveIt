import BusyBeaver.ZFC.ProfileAxioms
import BusyBeaver.ZFC.ProfileModel

/-!
Fixed equality-free first-order adapters for the profile Power Set filter.

SubD is membership in the raw predecessor-profile classes of a's members.
The common bound contains all such traces, including copies outside the
first transitive container. The resulting profile power is a resource for
the interpreted Power Set theorem, not by itself the quotient axiom.
-/

namespace SetTheory.BusyBeaver.ZFC.PowerSyntax

open Form Profile ProfilePairs ProfileCollection ProfileComposition ProfileAxioms
open ProfileSyntax ProfileModel DeepPositiveClosure

universe u
variable {V : Type u}

def subDForm (r a : Nat) : Form :=
  fAll (fImp (fMem 0 (r + 1)) (classMemberForm 0 (a + 1)))

theorem sat_subDForm (mem : V → V → Prop) (env : Nat → V) (r a : Nat) :
    Sat mem env (subDForm r a) ↔ SubD mem (env r) (env a) :=
  ⟨fun h z hz => (sat_classMemberForm mem _ 0 (a + 1)).mp (h z hz),
    fun h z hz => (sat_classMemberForm mem _ 0 (a + 1)).mpr (h z hz)⟩

theorem equalityFree_subDForm (r a : Nat) : EqualityFree (subDForm r a) :=
  ⟨True.intro, equalityFree_classMemberForm 0 (a + 1)⟩

def powerChoiceForm : Form :=
  fAnd (fMem 0 3) (fAnd (sameForm 1 0) (subDForm 0 2))

theorem equalityFree_powerChoiceForm : EqualityFree powerChoiceForm :=
  ⟨True.intro, ⟨equalityFree_sameForm 1 0, equalityFree_subDForm 0 2⟩⟩

theorem power_instance (mem : V → V → Prop) (hModel : ModelsGIC mem) (a bound : V) :
    CollectionInstance mem (PowerChoice mem a bound) :=
  instance_of_matrix mem hModel powerChoiceForm equalityFree_powerChoiceForm
    (scons a (fun _ => bound)) _ fun _ _ =>
      and_congr Iff.rfl (and_congr (sat_sameForm mem _ 1 0) (sat_subDForm mem _ 0 2))

/-- Actual Form-indexed CP/GIC supplies the profile-power resource. -/
theorem power_profile_of_model (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem)
    (a : V) : ∃ p, (∀ v, mem v p → SubD mem v a) ∧
      ∀ r, SubD mem r a → ClassMember mem r p := by
  obtain ⟨bound, hBound⟩ := subD_bound mem a ((sat_containerForm mem (fun _ => witness)).mp (h.1 _))
  exact power_profile_of_instance mem a bound hBound (power_instance mem h.2 a bound)

#print axioms power_instance
#print axioms power_profile_of_model

end SetTheory.BusyBeaver.ZFC.PowerSyntax
