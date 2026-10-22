import BusyBeaver.ZFC.ProfileModel
import BusyBeaver.ZFC.ProfileComposition

/-!
First-order equality-free matrix adapters for composition of bisimulations.

Every collection resource is obtained from the actual Form-indexed GIC schema.
The definitions preserve input/output slots and arbitrary parameter values.
This is an interpretation layer, not a coded proof compiler or TM endpoint.
-/

namespace SetTheory.BusyBeaver.ZFC.CompositionModel

open Form Profile ProfilePairs ProfileCollection ProfileComposition ProfileSyntax ProfileModel
open DeepPositiveClosure

universe u
variable {V : Type u}

def unionChoiceForm : Form :=
  fAnd (fEx (fAnd (fMem 0 3) (fMem 1 0))) (sameForm 1 0)

theorem equalityFree_unionChoiceForm : EqualityFree unionChoiceForm := by
  exact ⟨⟨True.intro, True.intro⟩, equalityFree_sameForm 1 0⟩

theorem union_instance (mem : V → V → Prop) (hModel : ModelsGIC mem) (family : V) :
    CollectionInstance mem (UnionChoice mem family) := by
  apply instance_of_matrix mem hModel unionChoiceForm equalityFree_unionChoiceForm
    (fun _ => family) _
  intro x y
  exact and_congr Iff.rfl (sat_sameForm mem _ 1 0)

def fiberChoiceForm : Form :=
  fAnd (fMem 0 2) (fEx (fEx (fEx (fAnd (orderedPairForm 2 1 6)
    (fAnd (orderedPairForm 1 0 3) (orderedPairForm 2 0 4))))))

theorem equalityFree_fiberChoiceForm : EqualityFree fiberChoiceForm := by
  exact ⟨True.intro, ⟨equalityFree_orderedPairForm 2 1 6,
    ⟨equalityFree_orderedPairForm 1 0 3, equalityFree_orderedPairForm 2 0 4⟩⟩⟩

theorem fiber_instance (mem : V → V → Prop) (hModel : ModelsGIC mem) (r2 d : V) :
    CollectionInstance mem (FiberChoice mem r2 d) := by
  apply instance_of_matrix mem hModel fiberChoiceForm equalityFree_fiberChoiceForm
    (scons r2 (fun _ => d)) _
  intro c e
  constructor
  · rintro ⟨hc, s, t, u, hst, htu, hsu⟩
    exact ⟨hc, s, t, u, (sat_orderedPairForm mem _ 2 1 6).mp hst,
      (sat_orderedPairForm mem _ 1 0 3).mp htu,
      (sat_orderedPairForm mem _ 2 0 4).mp hsu⟩
  · rintro ⟨hc, s, t, u, hst, htu, hsu⟩
    exact ⟨hc, s, t, u, (sat_orderedPairForm mem _ 2 1 6).mpr hst,
      (sat_orderedPairForm mem _ 1 0 3).mpr htu,
      (sat_orderedPairForm mem _ 2 0 4).mpr hsu⟩

def fiberProfileForm (r d s : Nat) : Form :=
  fAll (fAll (fIff (appForm (s + 2) 1 0)
    (fEx (fAnd (orderedPairForm 2 0 (d + 3)) (appForm (r + 3) 0 1)))))

theorem sat_fiberProfileForm (mem : V → V → Prop) (env : Nat → V) (r d s : Nat) :
    Sat mem env (fiberProfileForm r d s) ↔ FiberProfile mem (env r) (env d) (env s) := by
  have hRight (a b : V) :
      Sat mem (scons b (scons a env))
        (fEx (fAnd (orderedPairForm 2 0 (d + 3)) (appForm (r + 3) 0 1))) ↔
      ∃ t, OrderedPair mem a t (env d) ∧ App mem (env r) t b := by
    constructor
    · rintro ⟨t, hat, htb⟩
      exact ⟨t, (sat_orderedPairForm mem _ 2 0 (d + 3)).mp hat,
        (sat_appForm mem _ (r + 3) 0 1).mp htb⟩
    · rintro ⟨t, hat, htb⟩
      exact ⟨t, (sat_orderedPairForm mem _ 2 0 (d + 3)).mpr hat,
        (sat_appForm mem _ (r + 3) 0 1).mpr htb⟩
  constructor
  · intro h a b
    exact (sat_appForm mem _ (s + 2) 1 0).symm.trans
      ((Sat_fIff.mp (h a b)).trans (hRight a b))
  · intro h a b
    apply Sat_fIff.mpr
    exact (sat_appForm mem _ (s + 2) 1 0).trans ((h a b).trans (hRight a b).symm)

theorem equalityFree_fiberProfileForm (r d s : Nat) : EqualityFree (fiberProfileForm r d s) := by
  have hRight := And.intro (equalityFree_orderedPairForm 2 0 (d + 3))
    (equalityFree_appForm (r + 3) 0 1)
  exact ⟨⟨equalityFree_appForm (s + 2) 1 0, hRight⟩,
    ⟨hRight, equalityFree_appForm (s + 2) 1 0⟩⟩

def compositionChoiceForm : Form :=
  fAnd (fMem 0 2) (fiberProfileForm 3 0 1)

theorem equalityFree_compositionChoiceForm : EqualityFree compositionChoiceForm := by
  exact ⟨True.intro, equalityFree_fiberProfileForm 3 0 1⟩

theorem composition_instance (mem : V → V → Prop) (hModel : ModelsGIC mem) (r1 r2 : V) :
    CollectionInstance mem (CompositionChoice mem r1 r2) := by
  apply instance_of_matrix mem hModel compositionChoiceForm equalityFree_compositionChoiceForm
    (scons r1 (fun _ => r2)) _
  intro d s
  exact and_congr Iff.rfl (sat_fiberProfileForm mem _ 3 0 1)

theorem eqv_trans_of_model (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem)
    {x y z : V} (hxy : Eqv mem x y) (hyz : Eqv mem y z) : Eqv mem x z := by
  exact eqv_trans_of_instances mem
    (transContainers_of_containers ((sat_containerForm mem (fun _ => witness)).mp (h.1 _)))
    (orderedPairs_of_model mem witness h)
    (fiber_instance mem h.2) (composition_instance mem h.2) (union_instance mem h.2) hxy hyz

def matchChoiceForm : Form :=
  fAnd (fMem 0 2) (fEx (fAnd (fMem 0 4)
    (fAnd (bisimForm 2) (appForm 2 1 0))))

def backMatchChoiceForm : Form :=
  fAnd (fMem 0 3) (fEx (fAnd (fMem 0 3)
    (fAnd (bisimForm 2) (appForm 2 0 1))))

theorem equalityFree_matchChoiceForm : EqualityFree matchChoiceForm := by
  exact ⟨True.intro, ⟨True.intro, ⟨equalityFree_bisimForm 2, equalityFree_appForm 2 1 0⟩⟩⟩

theorem equalityFree_backMatchChoiceForm : EqualityFree backMatchChoiceForm := by
  exact ⟨True.intro, ⟨True.intro, ⟨equalityFree_bisimForm 2, equalityFree_appForm 2 0 1⟩⟩⟩

theorem match_instance (mem : V → V → Prop) (hModel : ModelsGIC mem) (x y : V) :
    CollectionInstance mem (MatchChoice mem x y) := by
  apply instance_of_matrix mem hModel matchChoiceForm equalityFree_matchChoiceForm
    (scons x (fun _ => y)) _
  intro a r
  constructor
  · rintro ⟨ha, b, hb, hr, hab⟩
    exact ⟨ha, b, hb, (sat_bisimForm mem _ 2).mp hr, (sat_appForm mem _ 2 1 0).mp hab⟩
  · rintro ⟨ha, b, hb, hr, hab⟩
    exact ⟨ha, b, hb, (sat_bisimForm mem _ 2).mpr hr, (sat_appForm mem _ 2 1 0).mpr hab⟩

theorem backMatch_instance (mem : V → V → Prop) (hModel : ModelsGIC mem) (x y : V) :
    CollectionInstance mem (BackMatchChoice mem x y) := by
  apply instance_of_matrix mem hModel backMatchChoiceForm equalityFree_backMatchChoiceForm
    (scons x (fun _ => y)) _
  intro b r
  constructor
  · rintro ⟨hb, a, ha, hr, hab⟩
    exact ⟨hb, a, ha, (sat_bisimForm mem _ 2).mp hr, (sat_appForm mem _ 2 0 1).mp hab⟩
  · rintro ⟨hb, a, ha, hr, hab⟩
    exact ⟨hb, a, ha, (sat_bisimForm mem _ 2).mpr hr, (sat_appForm mem _ 2 0 1).mpr hab⟩

theorem eqv_extensionality_of_model (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem)
    (x y : V) (hMembers : ∀ z, Member mem z x ↔ Member mem z y) : Eqv mem x y := by
  exact eqv_extensionality_of_instances mem
    (transContainers_of_containers ((sat_containerForm mem (fun _ => witness)).mp (h.1 _)))
    (pairs_of_model mem witness h) (union_instance mem h.2)
    (match_instance mem h.2) (backMatch_instance mem h.2)
    (eqv_refl_of_model mem witness h)
    (fun _ _ hxy => eqv_symm_of_model mem witness h hxy) x y hMembers

#print axioms eqv_trans_of_model
#print axioms eqv_extensionality_of_model

end SetTheory.BusyBeaver.ZFC.CompositionModel
