import BusyBeaver.ZFC.ProfileModel
import ZF.Zf

/-!
Native-equality consequences of formula-indexed GIC.

Proposed new module; it uses the real repository Form, Sat, relOf,
Functional and CollectionInstance at commit 6d9800d1ca67.
No quotient-specific reasoning is needed after quotient_fullGIC.
-/

namespace SetTheory.BusyBeaver.ZFC.GICConsequences

open Form ProfileCollection ProfileSyntax ProfileModel

universe u
variable {V : Type u}

def FullGIC (mem : V → V → Prop) : Prop :=
  ∀ phi env, Sat mem env (gicForm phi)

theorem exact_image_of_collection (mem : V → V → Prop)
    (r : V → V → Prop) (a : V)
    (functional : ∀ x y z, mem x a → r x y → r x z → y = z)
    (collect : CollectionInstance mem (fun x y => mem x a ∧ r x y)) :
    ∃ b, ∀ y, mem y b ↔ ∃ x, mem x a ∧ r x y := by
  obtain ⟨b, support, cover⟩ := collect a
  refine ⟨b, fun y => ⟨?_, ?_⟩⟩
  · intro hy
    exact support y hy
  · rintro ⟨x, hxa, hxy⟩
    obtain ⟨z, hzb, _, hxz⟩ := cover x hxa ⟨y, hxa, hxy⟩
    exact (functional x z y hxa hxz hxy) ▸ hzb

/-- GIC input/output occupy slots 0/1; relOf uses output/input. -/
def imageRename : Nat → Nat
  | 0 => 1
  | 1 => 0
  | k + 2 => k + 3

def imageMatrix (phi : Form) : Form :=
  fAnd (fMem 0 2) (rename imageRename phi)

theorem image_instance (mem : V → V → Prop) (h : FullGIC mem)
    (phi : Form) (env : Nat → V) (a : V) :
    CollectionInstance mem (fun x y => mem x a ∧ relOf mem phi env y x) := by
  apply collectionInstance_congr mem _ _ _
    ((sat_gicForm mem (imageMatrix phi) (scons a env)).mp
      (h (imageMatrix phi) (scons a env)))
  intro x y
  exact and_congr Iff.rfl
    (Sat_rename_relOf phi imageRename
      (scons x (scons y (scons a env))) env y x
      (fun n => match n with | 0 => rfl | 1 => rfl | _ + 2 => rfl))

theorem replacement (mem : V → V → Prop) (h : FullGIC mem)
    (phi : Form) (env : Nat → V) (hf : Functional (relOf mem phi env))
    (a : V) :
    ∃ b, ∀ y, mem y b ↔ ∃ x, mem x a ∧ relOf mem phi env y x :=
  exact_image_of_collection mem (fun x y => relOf mem phi env y x) a
    (fun x y z _ => hf x y z) (image_instance mem h phi env a)

/-- The partial identity on phi; parameters keep their relative order. -/
def filterMatrix (phi : Form) : Form :=
  fAnd (fEq 0 1) (rename Nat.succ phi)

theorem filter_iff (mem : V → V → Prop) (phi : Form) (env : Nat → V)
    (x y : V) :
    relOf mem (filterMatrix phi) env y x ↔
      y = x ∧ Sat mem (scons x env) phi :=
  and_congr Iff.rfl (Sat_rename_ext phi Nat.succ
    (scons y (scons x env)) (scons x env) (fun _ => rfl))

theorem separation_of_replacement (mem : V → V → Prop)
    (repl : ∀ (phi : Form) (env : Nat → V), Functional (relOf mem phi env) →
      ∀ a, ∃ b, ∀ y, mem y b ↔ ∃ x, mem x a ∧ relOf mem phi env y x)
    (phi : Form) (env : Nat → V) (a : V) :
    ∃ b, ∀ y, mem y b ↔ mem y a ∧ Sat mem (scons y env) phi := by
  have hf : Functional (relOf mem (filterMatrix phi) env) := by
    intro x y z hy hz
    exact ((filter_iff mem phi env x y).mp hy).1.trans
      ((filter_iff mem phi env x z).mp hz).1.symm
  obtain ⟨b, hb⟩ := repl (filterMatrix phi) env hf a
  refine ⟨b, fun y => (hb y).trans ⟨?_, ?_⟩⟩
  · rintro ⟨x, hxa, hxy⟩
    obtain ⟨hyx, hp⟩ := (filter_iff mem phi env x y).mp hxy
    exact hyx.symm ▸ ⟨hxa, hp⟩
  · intro hy
    exact ⟨y, hy.1, (filter_iff mem phi env y y).mpr ⟨rfl, hy.2⟩⟩

theorem separation (mem : V → V → Prop) (h : FullGIC mem)
    (phi : Form) (env : Nat → V) (a : V) :
    ∃ b, ∀ y, mem y b ↔ mem y a ∧ Sat mem (scons y env) phi :=
  separation_of_replacement mem (replacement mem h) phi env a

theorem separation_form (mem : V → V → Prop) (h : FullGIC mem) :
    ∀ phi env, Sat mem env (Sep_form phi) :=
  bridge_Sep.mpr (separation mem h)

theorem replacement_form (mem : V → V → Prop) (h : FullGIC mem) :
    ∀ phi env, Sat mem env (Repl_form phi) := by
  intro phi env
  exact (bridge_Repl phi env).mpr (replacement mem h phi env)

#print axioms exact_image_of_collection
#print axioms replacement
#print axioms separation_of_replacement
#print axioms separation

end SetTheory.BusyBeaver.ZFC.GICConsequences
