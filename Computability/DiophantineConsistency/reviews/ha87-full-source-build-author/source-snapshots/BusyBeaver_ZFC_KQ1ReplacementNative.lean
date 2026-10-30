import BusyBeaver.ZFC.KQ1Collect

/-!
Native Replacement after quotient collection, for the unchanged QHyp interface.
This implements the guarded-image proposal in the repository's collection-first
and native-replacement research packets against the pinned current sources.
Every collection call uses one actual Form; no semantic comprehension is assumed.
-/
namespace SetTheory.BusyBeaver.ZFC.KQ1ReplacementNative

open Form ProfileCollection DeepPositiveClosure KQHyp
universe u
variable {V : Type u}

/-- Only uniqueness on the guarded input domain is needed. -/
theorem exact_image (mem r : V → V → Prop) (a : V)
    (functional : ∀ x y z, mem x a → r x y → r x z → y = z)
    (collect : CollectionInstance mem (fun x y => mem x a ∧ r x y)) :
    ∃ b, ∀ y, mem y b ↔ ∃ x, mem x a ∧ r x y := by
  obtain ⟨b, support, cover⟩ := collect a
  refine ⟨b, fun y => ⟨support y, ?_⟩⟩
  rintro ⟨x, hxa, hxy⟩
  obtain ⟨z, hzb, _, hxz⟩ := cover x hxa ⟨y, hxa, hxy⟩
  exact (functional x z y hxa hxz hxy) ▸ hzb

/-- Swap output/input slots and skip the newly inserted domain parameter. -/
def guardRename : Nat → Nat
  | 0 => 1
  | 1 => 0
  | k + 2 => k + 3

def guardForm (phi : Form) : Form := fAnd (fMem 0 2) (rename guardRename phi)

theorem sat_guardForm (mem : V → V → Prop) (phi : Form)
    (a : V) (env : Nat → V) (x y : V) :
    MatrixRelation mem (guardForm phi) (scons a env) x y ↔
      mem x a ∧ relOf mem phi env y x :=
  and_congr Iff.rfl (Sat_rename_relOf phi guardRename
    (scons x (scons y (scons a env))) env y x
    (fun n => match n with | 0 => rfl | 1 => rfl | _ + 2 => rfl))

/-- Replacement derived entirely in the native model, with literal equality. -/
theorem replacement_of_collection (mem : V → V → Prop)
    (collect : ∀ phi env, CollectionInstance mem (MatrixRelation mem phi env))
    (phi : Form) (env : Nat → V) (hFunctional : Functional (relOf mem phi env))
    (a : V) : ∃ b, ∀ y, mem y b ↔ ∃ x, mem x a ∧ relOf mem phi env y x := by
  apply exact_image mem (fun x y => relOf mem phi env y x) a
    (fun x y z _ => hFunctional x y z)
  intro domain
  obtain ⟨b, support, cover⟩ := collect (guardForm phi) (scons a env) domain
  refine ⟨b, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hxy⟩ := support y hy
    exact ⟨x, (sat_guardForm mem phi a env x y).mp hxy⟩
  · rintro x hx ⟨y, hxy⟩
    obtain ⟨z, hzb, hxz⟩ := cover x hx ⟨y, (sat_guardForm mem phi a env x y).mpr hxy⟩
    exact ⟨z, hzb, (sat_guardForm mem phi a env x z).mp hxz⟩

/-- Same public endpoint type as the existing quotient Replacement theorem. -/
theorem quotient_replacement (mem : V → V → Prop) (witness : V) (h : QHyp mem)
    (phi : Form) (env : Nat → KQ1Model.Domain mem witness h)
    (hFunctional : Functional (relOf (KQ1Model.quotientMember mem witness h) phi env))
    (a : KQ1Model.Domain mem witness h) :
    ∃ b, ∀ y, KQ1Model.quotientMember mem witness h y b ↔
      ∃ x, KQ1Model.quotientMember mem witness h x a ∧
        relOf (KQ1Model.quotientMember mem witness h) phi env y x :=
  replacement_of_collection _ (KQ1Collect.quotient_collection mem witness h)
    phi env hFunctional a

theorem quotient_repl_form (mem : V → V → Prop) (witness : V) (h : QHyp mem) :
    ∀ phi env, Sat (KQ1Model.quotientMember mem witness h) env (Repl_form phi) :=
  fun phi env => (bridge_Repl phi env).mpr (quotient_replacement mem witness h phi env)

end SetTheory.BusyBeaver.ZFC.KQ1ReplacementNative
