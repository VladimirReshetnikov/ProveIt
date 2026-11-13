import BusyBeaver.ZFC.DeepPositiveClosure
import BusyBeaver.ZFC.Bootstrap

/-!
Bootstrap instances obtained from the actual first-order PSC schema.

`ModelsPSC` quantifies over `SetTheory.Form` matrices and parameter environments,
not arbitrary semantic relations. Every relation used below is explicitly
represented by a formula. The theory here permits logical equality and uses
the subset seed. Its first-order Separation conclusion ranges over formulas.
This does not supply a coded proof transformer or the full ZFC calibration.
-/

namespace SetTheory.BusyBeaver.ZFC.DefinableClosure

open Form PositiveClosure DeepPositiveClosure

universe u
variable {V : Type u}

/-- Validity of every actual matrix instance, including logical equality. -/
def ModelsPSC (mem : V → V → Prop) : Prop :=
  ∀ phi env, Sat mem env (pscForm phi)

/-- A semantic relation represented by one formula and parameter environment. -/
def DefinableRelation (mem : V → V → Prop) (r : V → V → Prop) : Prop :=
  ∃ phi env, ∀ x y, MatrixRelation mem phi env x y ↔ r x y

theorem closureInstance_congr (mem : V → V → Prop) (seed r s : V → V → Prop)
    (h : ∀ x y, r x y ↔ s x y) (hr : ClosureInstance mem seed r) :
    ClosureInstance mem seed s := by
  intro hBound a
  have hrBound : SubsetBounded mem r := by
    intro x
    obtain ⟨b, hb⟩ := hBound x
    exact ⟨b, fun y hy => hb y ((h x y).mp hy)⟩
  obtain ⟨c, hc, hs⟩ := hr hrBound a
  refine ⟨c, ?_, ?_⟩
  · intro x y hx hxy
    exact hc x y hx ((h x y).mpr hxy)
  · intro y hy
    obtain ⟨x, hxy⟩ := hs y hy
    exact ⟨x, (h x y).mp hxy⟩

theorem instance_of_definable (mem : V → V → Prop) (hModel : ModelsPSC mem)
    (r : V → V → Prop) (hDef : DefinableRelation mem r) :
    ClosureInstance mem (Sub mem) r := by
  obtain ⟨phi, env, h⟩ := hDef
  exact closureInstance_congr mem (Sub mem) _ r h
    ((sat_pscForm mem phi env).mp (hModel phi env))

/-- Ignore the input slot to form a constant relation from a unary matrix. -/
theorem constant_definable (mem : V → V → Prop) (phi : Form) (env : Nat → V) :
    DefinableRelation mem (fun _ y => Sat mem (scons y env) phi) := by
  refine ⟨rename Nat.succ phi, env, ?_⟩
  intro x y
  exact Sat_rename_ext phi Nat.succ (scons x (scons y env)) (scons y env)
    (fun _ => rfl)

theorem singleton_definable (mem : V → V → Prop) (t : V) :
    DefinableRelation mem (fun _ y => y = t) := by
  exact ⟨fEq 1 2, (fun _ => t), fun _ _ => Iff.rfl⟩

theorem power_definable (mem : V → V → Prop) (a : V) :
    DefinableRelation mem (fun _ y => Sub mem y a) := by
  exact ⟨subsetForm 1 2, (fun _ => a), fun _ _ => Iff.rfl⟩

def singForm : Form :=
  fAll (fIff (fMem 0 1) (fEq 0 2))

def isSingletonForm : Form :=
  fEx (fAll (fIff (fMem 0 2) (fEq 0 1)))

def switchForm : Form :=
  fOr singForm
    (fAnd (fImp isSingletonForm fBot) (subsetForm 1 0))

theorem sat_singForm (mem : V → V → Prop) (x y : V) (env : Nat → V) :
    Sat mem (scons x (scons y env)) singForm ↔ Sing mem x y := by
  change (∀ z, Sat mem (scons z (scons x (scons y env)))
    (fIff (fMem 0 1) (fEq 0 2))) ↔ _
  constructor
  · intro h z
    exact Sat_fIff.mp (h z)
  · intro h z
    exact Sat_fIff.mpr (h z)

theorem sat_isSingletonForm (mem : V → V → Prop) (x y : V) (env : Nat → V) :
    Sat mem (scons x (scons y env)) isSingletonForm ↔ ∃ t, Sing mem x t := by
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, fun z => Sat_fIff.mp (ht z)⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, fun z => Sat_fIff.mpr (ht z)⟩

theorem sat_switchForm (mem : V → V → Prop) (x y : V) (env : Nat → V) :
    Sat mem (scons x (scons y env)) switchForm ↔ Switch mem x y := by
  change (Sat mem _ singForm ∨
    ((Sat mem _ isSingletonForm → False) ∧ Sub mem y x)) ↔ _
  constructor
  · intro h
    rcases h with h | ⟨h, hSub⟩
    · exact Or.inl ((sat_singForm mem x y env).mp h)
    · exact Or.inr ⟨fun hs => h ((sat_isSingletonForm mem x y env).mpr hs), hSub⟩
  · intro h
    rcases h with h | ⟨h, hSub⟩
    · exact Or.inl ((sat_singForm mem x y env).mpr h)
    · exact Or.inr ⟨fun hs => h ((sat_isSingletonForm mem x y env).mp hs), hSub⟩

theorem switch_definable (mem : V → V → Prop) (witness : V) :
    DefinableRelation mem (Switch mem) := by
  exact ⟨switchForm, (fun _ => witness), fun x y => sat_switchForm mem x y _⟩

theorem singletons_of_model (mem : V → V → Prop) (witness : V)
    (hModel : ModelsPSC mem) : SingletonsExact mem := by
  exact singletons_of_instances mem (Sub mem) witness (sub_refl mem)
    (fun t => instance_of_definable mem hModel _ (singleton_definable mem t))

theorem empty_of_model (mem : V → V → Prop) (witness : V)
    (hModel : ModelsPSC mem) : ∃ e, ∀ y, ¬ mem y e := by
  have hDef : DefinableRelation mem (fun _ _ => False) :=
    ⟨fBot, (fun _ => witness), fun _ _ => Iff.rfl⟩
  obtain ⟨e, he⟩ := constant_exact_of_instance mem (Sub mem) witness (sub_refl mem)
    (fun _ => False) ⟨witness, fun _ h => h.elim⟩
    (instance_of_definable mem hModel _ hDef)
  exact ⟨e, fun y hy => (he y).mp hy⟩

theorem power_of_model (mem : V → V → Prop) (witness : V)
    (hModel : ModelsPSC mem) (a : V) :
    ∃ p, ∀ y, mem y p ↔ Sub mem y a := by
  exact power_of_instance mem (Sub mem) witness (sub_refl mem) a
    (instance_of_definable mem hModel _ (power_definable mem a))

theorem transitive_cover_of_model (mem : V → V → Prop) (witness : V)
    (hModel : ModelsPSC mem) (a : V) :
    ∃ c, Transitive mem c ∧ Sub mem a c := by
  exact positive_decoder_cover mem (Sub mem) (sub_refl mem)
    (singletons_of_model mem witness hModel)
    (instance_of_definable mem hModel _ (switch_definable mem witness)) a

def separationRename : Nat → Nat
  | 0 => 1
  | k + 1 => k + 3

theorem separation_definable (mem : V → V → Prop) (a : V)
    (phi : Form) (env : Nat → V) :
    DefinableRelation mem (fun _ y => mem y a ∧ Sat mem (scons y env) phi) := by
  refine ⟨fAnd (fMem 1 2) (rename separationRename phi), scons a env, ?_⟩
  intro x y
  change (mem y a ∧ Sat mem _ (rename separationRename phi)) ↔ _
  have hRename := Sat_rename_ext (mem := mem) phi separationRename
    (scons x (scons y (scons a env))) (scons y env)
    (fun n => match n with | 0 => rfl | _ + 1 => rfl)
  exact and_congr Iff.rfl hRename

/-- Full Separation for actual formulas, with all parameter environments. -/
theorem separation_of_model (mem : V → V → Prop) (witness : V)
    (hModel : ModelsPSC mem) (a : V) (phi : Form) (env : Nat → V) :
    ∃ s, ∀ y, mem y s ↔ mem y a ∧ Sat mem (scons y env) phi := by
  exact separation_of_instances mem (Sub mem) witness (sub_refl mem)
    (singletons_of_model mem witness hModel)
    (instance_of_definable mem hModel _ (switch_definable mem witness)) a _
    (instance_of_definable mem hModel _ (separation_definable mem a phi env))

theorem union_definable (mem : V → V → Prop) (a : V) :
    DefinableRelation mem (fun _ y => ∃ x, mem x a ∧ mem y x) := by
  exact ⟨fEx (fAnd (fMem 0 3) (fMem 2 0)), (fun _ => a),
    fun _ _ => Iff.rfl⟩

theorem union_of_model (mem : V → V → Prop) (witness : V)
    (hModel : ModelsPSC mem) (a : V) :
    ∃ s, ∀ y, mem y s ↔ ∃ x, mem x a ∧ mem y x := by
  exact union_of_instances mem (Sub mem) witness (sub_refl mem)
    (singletons_of_model mem witness hModel)
    (instance_of_definable mem hModel _ (switch_definable mem witness)) a
    (instance_of_definable mem hModel _ (union_definable mem a))

theorem twoCycle_definable (mem : V → V → Prop) (a b : V) :
    DefinableRelation mem (Bootstrap.TwoCycle a b) := by
  exact ⟨fOr (fAnd (fEq 0 2) (fEq 1 3)) (fAnd (fEq 0 3) (fEq 1 2)),
    scons a (fun _ => b), fun _ _ => Iff.rfl⟩

theorem pairing_of_model (mem : V → V → Prop) (hModel : ModelsPSC mem) :
    Bootstrap.PairingSets mem := by
  intro a b
  exact Bootstrap.pairing_of_instance mem (Sub mem) (sub_refl mem) a b
    (instance_of_definable mem hModel _ (twoCycle_definable mem a b))

def rootedRename : Nat → Nat
  | 0 => 0
  | 1 => 1
  | k + 2 => k + 4

theorem rootedImage_definable (mem : V → V → Prop) (a root : V)
    (phi : Form) (env : Nat → V) :
    DefinableRelation mem (Bootstrap.RootedImage mem a root (MatrixRelation mem phi env)) := by
  refine ⟨fOr (fAnd (fEq 0 3) (fMem 1 2))
    (fAnd (fMem 0 2) (rename rootedRename phi)), scons a (scons root env), ?_⟩
  intro x y
  have hRename := Sat_rename_ext (mem := mem) phi rootedRename
    (scons x (scons y (scons a (scons root env)))) (scons x (scons y env))
    (fun n => match n with | 0 => rfl | 1 => rfl | _ + 2 => rfl)
  change ((x = root ∧ mem y a) ∨ (mem x a ∧ Sat mem _ (rename rootedRename phi))) ↔ _
  exact or_congr Iff.rfl (and_congr Iff.rfl hRename)

def imageRename : Nat → Nat
  | 0 => 0
  | 1 => 1
  | k + 2 => k + 3

def imageForm (phi : Form) : Form :=
  fEx (fAnd (fMem 0 2) (rename imageRename phi))

theorem sat_imageForm (mem : V → V → Prop) (a y : V)
    (phi : Form) (env : Nat → V) :
    Sat mem (scons y (scons a env)) (imageForm phi) ↔
      ∃ x, mem x a ∧ MatrixRelation mem phi env x y := by
  have hRename (x : V) := Sat_rename_ext (mem := mem) phi imageRename
    (scons x (scons y (scons a env))) (scons x (scons y env))
    (fun n => match n with | 0 => rfl | 1 => rfl | _ + 2 => rfl)
  constructor
  · rintro ⟨x, hx, hr⟩
    exact ⟨x, hx, (hRename x).mp hr⟩
  · rintro ⟨x, hx, hr⟩
    exact ⟨x, hx, (hRename x).mpr hr⟩

/-- Partial functional Replacement, restricted to actual first-order matrices. -/
theorem partial_replacement_of_model (mem : V → V → Prop) (witness : V)
    (hModel : ModelsPSC mem) (a : V) (phi : Form) (env : Nat → V)
    (hFunctional : Bootstrap.PartialFunctionalOn mem a (MatrixRelation mem phi env)) :
    ∃ b, ∀ y, mem y b ↔ ∃ x, mem x a ∧ MatrixRelation mem phi env x y := by
  obtain ⟨root, hRoot⟩ := separation_of_model mem witness hModel a
    (fImp (fMem 0 0) fBot) env
  obtain ⟨union, hUnion⟩ := union_of_model mem witness hModel a
  apply Bootstrap.partial_replacement_of_instance mem (Sub mem) (sub_refl mem)
    a root union (MatrixRelation mem phi env) hRoot hUnion hFunctional
    (instance_of_definable mem hModel _ (rootedImage_definable mem a root phi env))
  intro c
  obtain ⟨b, hb⟩ := separation_of_model mem witness hModel c (imageForm phi) (scons a env)
  refine ⟨b, ?_⟩
  intro y
  exact (hb y).trans (and_congr Iff.rfl (sat_imageForm mem a y phi env))

def successorForm : Form :=
  fAll (fIff (fMem 0 2) (fOr (fMem 0 1) (fEq 0 1)))

theorem successor_definable (mem : V → V → Prop) (witness : V) :
    DefinableRelation mem (Bootstrap.Successor mem) := by
  refine ⟨successorForm, (fun _ => witness), ?_⟩
  intro x y
  constructor
  · intro h z
    exact Sat_fIff.mp (h z)
  · intro h z
    exact Sat_fIff.mpr (h z)

/-- Infinity follows from the definable successor instance, without Extensionality. -/
theorem infinity_of_model (mem : V → V → Prop) (witness : V)
    (hModel : ModelsPSC mem) :
    ∃ empty i, (∀ y, ¬ mem y empty) ∧ Bootstrap.Inductive mem empty i := by
  obtain ⟨e, he⟩ := empty_of_model mem witness hModel
  have hEmpty : Exact mem (fun _ => False) e :=
    fun y => ⟨he y, False.elim⟩
  obtain ⟨empty, i, hempty, hi⟩ := Bootstrap.infinity_of_instance mem (Sub mem)
    (sub_refl mem) e hEmpty (singletons_of_model mem witness hModel)
    (pairing_of_model mem hModel) (union_of_model mem witness hModel)
    (instance_of_definable mem hModel _ (successor_definable mem witness))
  exact ⟨empty, i, fun y hy => (hempty y).mp hy, hi⟩

#print axioms instance_of_definable
#print axioms separation_of_model
#print axioms union_of_model
#print axioms partial_replacement_of_model
#print axioms infinity_of_model

end SetTheory.BusyBeaver.ZFC.DefinableClosure
