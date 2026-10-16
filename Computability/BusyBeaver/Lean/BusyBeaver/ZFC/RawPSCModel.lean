import BusyBeaver.ZFC.RawPSCProfile
import BusyBeaver.ZFC.DeepPositiveClosure

/-!
Actual equality-free first-order instances for the raw PSC bootstrap.

ModelsRawPSC quantifies only over equality-free SetTheory.Form matrices and
parameter environments. Every resource is obtained from a represented matrix;
no arbitrary semantic relation is promoted to a schema instance. The fixed
hereditary-domain predicates also have checked equality-free Form adapters.
These results do not yet prove the complete hereditary interpretation,
deductive/consistency calibration or any compiler or machine endpoint.
-/

namespace SetTheory.BusyBeaver.ZFC.RawPSCModel

open Form PositiveClosure Profile RawPSCProfile PSCSaturation DeepPositiveClosure

universe u
variable {V : Type u}

def ModelsRawPSC (mem : V → V → Prop) : Prop :=
  ∀ phi, EqualityFree phi → ∀ env, Sat mem env (pscForm phi)

def EqFreeDefinableRelation (mem : V → V → Prop) (r : V → V → Prop) : Prop :=
  ∃ phi env, EqualityFree phi ∧ ∀ x y, MatrixRelation mem phi env x y ↔ r x y

theorem closureInstance_congr (mem : V → V → Prop) (r s : V → V → Prop)
    (h : ∀ x y, r x y ↔ s x y) (hr : ClosureInstance mem (Sub mem) r) :
    ClosureInstance mem (Sub mem) s := by
  intro hBound a
  have hrBound : SubsetBounded mem r := by
    intro x
    obtain ⟨b, hb⟩ := hBound x
    exact ⟨b, fun y hy => hb y ((h x y).mp hy)⟩
  obtain ⟨c, hClosed, hSupport⟩ := hr hrBound a
  refine ⟨c, ?_, ?_⟩
  · intro x y hx hxy
    exact hClosed x y hx ((h x y).mpr hxy)
  · intro y hy
    obtain ⟨x, hxy⟩ := hSupport y hy
    exact ⟨x, (h x y).mp hxy⟩

theorem instance_of_definable (mem : V → V → Prop) (hModel : ModelsRawPSC mem)
    (r : V → V → Prop) (hDef : EqFreeDefinableRelation mem r) :
    ClosureInstance mem (Sub mem) r := by
  obtain ⟨phi, env, hFree, hRep⟩ := hDef
  exact closureInstance_congr mem _ r hRep
    ((sat_pscForm mem phi env).mp (hModel phi hFree env))

theorem constant_definable (mem : V → V → Prop) (phi : Form) (env : Nat → V)
    (hFree : EqualityFree phi) :
    EqFreeDefinableRelation mem (fun _ y => Sat mem (scons y env) phi) := by
  refine ⟨rename Nat.succ phi, env, equalityFree_rename phi Nat.succ hFree, ?_⟩
  intro x y
  exact Sat_rename_ext phi Nat.succ (scons x (scons y env)) (scons y env)
    (fun _ => rfl)

theorem sameForm_equalityFree (i j : Nat) : EqualityFree (sameForm i j) := by
  exact ⟨⟨True.intro, True.intro⟩, ⟨True.intro, True.intro⟩⟩

def fullForm (i j : Nat) : Form :=
  fAnd (sameForm i j)
    (fAll (fIff (fMem (i + 1) 0) (fMem (j + 1) 0)))

theorem sat_fullForm (mem : V → V → Prop) (env : Nat → V) (i j : Nat) :
    Sat mem env (fullForm i j) ↔ RawPSCProfile.Full mem (env i) (env j) := by
  constructor
  · rintro ⟨hSame, hOut⟩
    exact ⟨(sat_sameForm mem env i j).mp hSame, fun z => Sat_fIff.mp (hOut z)⟩
  · rintro ⟨hSame, hOut⟩
    exact ⟨(sat_sameForm mem env i j).mpr hSame, fun z => Sat_fIff.mpr (hOut z)⟩

theorem equalityFree_fullForm (i j : Nat) : EqualityFree (fullForm i j) := by
  exact ⟨sameForm_equalityFree i j,
    ⟨⟨True.intro, True.intro⟩, ⟨True.intro, True.intro⟩⟩⟩

def twinSingForm (s t : Nat) : Form :=
  fAll (fIff (fMem 0 (s + 1)) (fullForm 0 (t + 1)))

theorem sat_twinSingForm (mem : V → V → Prop) (env : Nat → V) (s t : Nat) :
    Sat mem env (twinSingForm s t) ↔ TwinSing mem (env s) (env t) := by
  constructor
  · intro h z
    exact (Sat_fIff.mp (h z)).trans (sat_fullForm mem (scons z env) 0 (t + 1))
  · intro h z
    exact Sat_fIff.mpr ((h z).trans (sat_fullForm mem (scons z env) 0 (t + 1)).symm)

theorem equalityFree_twinSingForm (s t : Nat) : EqualityFree (twinSingForm s t) := by
  exact ⟨⟨True.intro, equalityFree_fullForm 0 (t + 1)⟩,
    ⟨equalityFree_fullForm 0 (t + 1), True.intro⟩⟩

def isTwinForm (x : Nat) : Form := fEx (twinSingForm (x + 1) 0)

theorem sat_isTwinForm (mem : V → V → Prop) (env : Nat → V) (x : Nat) :
    Sat mem env (isTwinForm x) ↔ ∃ t, TwinSing mem (env x) t := by
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, (sat_twinSingForm mem (scons t env) (x + 1) 0).mp ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, (sat_twinSingForm mem (scons t env) (x + 1) 0).mpr ht⟩

theorem equalityFree_isTwinForm (x : Nat) : EqualityFree (isTwinForm x) :=
  equalityFree_twinSingForm (x + 1) 0

def twinSwitchForm : Form :=
  fOr (twinSingForm 0 1)
    (fAnd (fImp (isTwinForm 0) fBot) (subsetForm 1 0))

theorem sat_twinSwitchForm (mem : V → V → Prop) (env : Nat → V) (x y : V) :
    MatrixRelation mem twinSwitchForm env x y ↔ TwinSwitch mem x y := by
  constructor
  · intro h
    rcases h with h | ⟨hNot, hSub⟩
    · exact Or.inl ((sat_twinSingForm mem _ 0 1).mp h)
    · exact Or.inr ⟨fun ht => hNot ((sat_isTwinForm mem _ 0).mpr ht), hSub⟩
  · intro h
    rcases h with h | ⟨hNot, hSub⟩
    · exact Or.inl ((sat_twinSingForm mem _ 0 1).mpr h)
    · exact Or.inr ⟨fun ht => hNot ((sat_isTwinForm mem _ 0).mp ht), hSub⟩

theorem equalityFree_twinSwitchForm : EqualityFree twinSwitchForm := by
  exact ⟨equalityFree_twinSingForm 0 1,
    ⟨⟨equalityFree_isTwinForm 0, True.intro⟩, equalityFree_subsetForm 1 0⟩⟩

theorem twin_definable (mem : V → V → Prop) (t : V) :
    EqFreeDefinableRelation mem (fun _ y => RawPSCProfile.Full mem y t) := by
  exact ⟨fullForm 1 2, (fun _ => t), equalityFree_fullForm 1 2,
    fun _ _ => sat_fullForm mem _ 1 2⟩

theorem switch_definable (mem : V → V → Prop) (witness : V) :
    EqFreeDefinableRelation mem (TwinSwitch mem) := by
  exact ⟨twinSwitchForm, (fun _ => witness), equalityFree_twinSwitchForm,
    fun x y => sat_twinSwitchForm mem _ x y⟩

theorem twins_of_model (mem : V → V → Prop) (witness : V) (hModel : ModelsRawPSC mem) :
    TwinSingletons mem := by
  exact twins_of_instances mem (Sub mem) witness (sub_refl mem)
    (fun t => instance_of_definable mem hModel _ (twin_definable mem t))

theorem empty_of_model (mem : V → V → Prop) (witness : V) (hModel : ModelsRawPSC mem) :
    ∃ e, ∀ z, ¬ mem z e := by
  exact empty_of_instance mem (Sub mem) witness (sub_refl mem)
    (instance_of_definable mem hModel _
      ⟨fBot, (fun _ => witness), True.intro, fun _ _ => Iff.rfl⟩)

theorem power_of_model (mem : V → V → Prop) (witness : V) (hModel : ModelsRawPSC mem)
    (a : V) : ∃ p, Exact mem (fun y => Sub mem y a) p := by
  exact power_of_instance mem (Sub mem) witness (sub_refl mem) a
    (instance_of_definable mem hModel _
      ⟨subsetForm 1 2, (fun _ => a), equalityFree_subsetForm 1 2, fun _ _ => Iff.rfl⟩)

theorem transitive_cover_of_model (mem : V → V → Prop) (witness : V)
    (hModel : ModelsRawPSC mem) (a : V) : ∃ c, Transitive mem c ∧ Sub mem a c := by
  exact transitive_cover_of_instances mem (Sub mem) (sub_refl mem)
    (twins_of_model mem witness hModel)
    (instance_of_definable mem hModel _ (switch_definable mem witness)) a

def separationRename : Nat → Nat
  | 0 => 1
  | k + 1 => k + 3

theorem separation_definable (mem : V → V → Prop) (a : V) (phi : Form)
    (env : Nat → V) (hFree : EqualityFree phi) :
    EqFreeDefinableRelation mem (fun _ y => mem y a ∧ Sat mem (scons y env) phi) := by
  refine ⟨fAnd (fMem 1 2) (rename separationRename phi), scons a env,
    ⟨True.intro, equalityFree_rename phi separationRename hFree⟩, ?_⟩
  intro x y
  have hRename := Sat_rename_ext (mem := mem) phi separationRename
    (scons x (scons y (scons a env))) (scons y env)
    (fun n => match n with | 0 => rfl | _ + 1 => rfl)
  exact and_congr Iff.rfl hRename

/-- Full raw Separation for arbitrary actual equality-free matrices and parameters. -/
theorem separation_of_model (mem : V → V → Prop) (witness : V)
    (hModel : ModelsRawPSC mem) (a : V) (phi : Form) (env : Nat → V)
    (hFree : EqualityFree phi) :
    ∃ b, Exact mem (fun y => mem y a ∧ Sat mem (scons y env) phi) b := by
  exact separation_of_cover_instance mem (Sub mem) witness (sub_refl mem) a _
    (transitive_cover_of_model mem witness hModel a)
    (instance_of_definable mem hModel _ (separation_definable mem a phi env hFree))

theorem union_definable (mem : V → V → Prop) (a : V) :
    EqFreeDefinableRelation mem (fun _ y => ∃ x, mem x a ∧ mem y x) := by
  exact ⟨fEx (fAnd (fMem 0 3) (fMem 2 0)), (fun _ => a),
    ⟨True.intro, True.intro⟩, fun _ _ => Iff.rfl⟩

theorem union_of_model (mem : V → V → Prop) (witness : V) (hModel : ModelsRawPSC mem)
    (a : V) : ∃ b, Exact mem (fun y => ∃ x, mem x a ∧ mem y x) b := by
  exact union_of_cover_instance mem (Sub mem) witness (sub_refl mem) a
    (transitive_cover_of_model mem witness hModel a)
    (instance_of_definable mem hModel _ (union_definable mem a))

def saturatedForm (a : Nat) : Form :=
  fAll (fAll (fImp (sameForm 1 0)
    (fImp (fMem 1 (a + 2)) (fMem 0 (a + 2)))))

theorem sat_saturatedForm (mem : V → V → Prop) (env : Nat → V) (a : Nat) :
    Sat mem env (saturatedForm a) ↔ Saturated mem (env a) := by
  constructor
  · intro h x y hxy hx
    exact h x y ((sat_sameForm mem _ 1 0).mpr hxy) hx
  · intro h x y hxy hx
    exact h x y ((sat_sameForm mem _ 1 0).mp hxy) hx

theorem equalityFree_saturatedForm (a : Nat) : EqualityFree (saturatedForm a) := by
  exact ⟨sameForm_equalityFree 1 0, ⟨True.intro, True.intro⟩⟩

def transitiveForm (t : Nat) : Form :=
  fAll (fImp (fMem 0 (t + 1)) (subsetForm 0 (t + 1)))

theorem sat_transitiveForm (mem : V → V → Prop) (env : Nat → V) (t : Nat) :
    Sat mem env (transitiveForm t) ↔ Transitive mem (env t) := Iff.rfl

theorem equalityFree_transitiveForm (t : Nat) : EqualityFree (transitiveForm t) :=
  ⟨True.intro, equalityFree_subsetForm 0 (t + 1)⟩

def pureForm (a : Nat) : Form :=
  fAnd (saturatedForm a) (fEx (fAnd (transitiveForm 0)
    (fAnd (subsetForm (a + 1) 0) (fAll (fImp (fMem 0 1) (saturatedForm 0))))))

theorem sat_pureForm (mem : V → V → Prop) (env : Nat → V) (a : Nat) :
    Sat mem env (pureForm a) ↔ Pure mem (env a) := by
  constructor
  · rintro ⟨ha, t, ht, hat, hMembers⟩
    exact ⟨(sat_saturatedForm mem env a).mp ha, t,
      (sat_transitiveForm mem _ 0).mp ht, hat,
      fun x hx => (sat_saturatedForm mem _ 0).mp (hMembers x hx)⟩
  · rintro ⟨ha, t, ht, hat, hMembers⟩
    exact ⟨(sat_saturatedForm mem env a).mpr ha, t,
      (sat_transitiveForm mem _ 0).mpr ht, hat,
      fun x hx => (sat_saturatedForm mem _ 0).mpr (hMembers x hx)⟩

theorem equalityFree_pureForm (a : Nat) : EqualityFree (pureForm a) := by
  exact ⟨equalityFree_saturatedForm a, ⟨equalityFree_transitiveForm 0,
    ⟨equalityFree_subsetForm (a + 1) 0, ⟨True.intro, equalityFree_saturatedForm 0⟩⟩⟩⟩

def profileImageForm (a y : Nat) : Form :=
  fEx (fAnd (fMem 0 (a + 1)) (sameForm 0 (y + 1)))

theorem sat_profileImageForm (mem : V → V → Prop) (env : Nat → V) (a y : Nat) :
    Sat mem env (profileImageForm a y) ↔ ProfileImage mem (env a) (env y) := by
  constructor
  · rintro ⟨x, hxa, hxy⟩
    exact ⟨x, hxa, (sat_sameForm mem _ 0 (y + 1)).mp hxy⟩
  · rintro ⟨x, hxa, hxy⟩
    exact ⟨x, hxa, (sat_sameForm mem _ 0 (y + 1)).mpr hxy⟩

theorem equalityFree_profileImageForm (a y : Nat) : EqualityFree (profileImageForm a y) :=
  ⟨True.intro, sameForm_equalityFree 0 (y + 1)⟩

theorem profileImage_definable (mem : V → V → Prop) (a : V) :
    EqFreeDefinableRelation mem (fun _ y => ProfileImage mem a y) := by
  exact ⟨profileImageForm 2 1, (fun _ => a), equalityFree_profileImageForm 2 1,
    fun _ _ => sat_profileImageForm mem _ 2 1⟩

theorem purity_cut_of_model (mem : V → V → Prop) (witness : V) (hModel : ModelsRawPSC mem)
    (v : V) : ∃ c, PurityCut mem v c := by
  obtain ⟨c, hc⟩ := separation_of_model mem witness hModel v (pureForm 0)
    (fun _ => witness) (equalityFree_pureForm 0)
  refine ⟨c, ?_⟩
  intro x
  exact (hc x).trans (and_congr Iff.rfl (sat_pureForm mem _ 0))

theorem saturation_of_model (mem : V → V → Prop) (witness : V) (hModel : ModelsRawPSC mem)
    (a : V) : ∃ b, SatExtension mem a b := by
  obtain ⟨union, hUnion⟩ := union_of_model mem witness hModel a
  exact saturation_of_instance mem (Sub mem) witness (sub_refl mem) a union hUnion
    (instance_of_definable mem hModel _ (profileImage_definable mem a))

theorem pure_upward_of_model (mem : V → V → Prop) (witness : V) (hModel : ModelsRawPSC mem)
    (a : V) (hSat : Saturated mem a) (hMembers : ∀ x, mem x a → Pure mem x) : Pure mem a := by
  exact pure_of_saturated_members mem a hSat hMembers
    (transitive_cover_of_model mem witness hModel a) (purity_cut_of_model mem witness hModel)

theorem pure_nonempty_of_model (mem : V → V → Prop) (witness : V)
    (hModel : ModelsRawPSC mem) : ∃ e, Pure mem e :=
  pure_nonempty mem (empty_of_model mem witness hModel)

theorem guarded_definable (mem : V → V → Prop) (r : V → V → Prop)
    (hDef : EqFreeDefinableRelation mem r) :
    EqFreeDefinableRelation mem (Guarded mem r) := by
  obtain ⟨phi, env, hFree, hRep⟩ := hDef
  refine ⟨fAnd (pureForm 0) (fAnd (pureForm 1) phi), env,
    ⟨equalityFree_pureForm 0, ⟨equalityFree_pureForm 1, hFree⟩⟩, ?_⟩
  intro x y
  exact and_congr (sat_pureForm mem _ 0)
    (and_congr (sat_pureForm mem _ 1) (hRep x y))

/-- Actual schema resources transfer the supplied definable invariant relation.
Invariance and its interpreted local bound remain explicit hypotheses. -/
theorem pure_hull_of_model (mem : V → V → Prop) (witness : V)
    (hModel : ModelsRawPSC mem) (r : V → V → Prop)
    (hDef : EqFreeDefinableRelation mem r)
    (hBound : PureLocalBound mem r) (hInvariant : PureRelationInvariant mem r) (a : V) :
    ∃ c, PureHull mem r a c := by
  exact pure_hull_of_instance mem r hBound hInvariant
    (instance_of_definable mem hModel _ (guarded_definable mem r hDef))
    (saturation_of_model mem witness hModel)
    (transitive_cover_of_model mem witness hModel)
    (purity_cut_of_model mem witness hModel) a

#print axioms instance_of_definable
#print axioms twins_of_model
#print axioms transitive_cover_of_model
#print axioms separation_of_model
#print axioms union_of_model
#print axioms sat_pureForm
#print axioms saturation_of_model
#print axioms pure_upward_of_model
#print axioms pure_hull_of_model

end SetTheory.BusyBeaver.ZFC.RawPSCModel
