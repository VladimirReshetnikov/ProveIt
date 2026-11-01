import BusyBeaver.ZFC.FiniteSetsCore
import BusyBeaver.ZFC.ProfileModel
import ZF.Zf

/-!
The internally well-founded part, with one literal GIC witness instance.

The definitions follow the well-founded-part interpretation in the attributed
busy-beaver snapshot, ZF/stdzf_r3/regcon/WF.v, pin
297ab8df7e5de329605c3875b4934643b371a5e3. Here the already available
formula-indexed GIC collects transitive well-founded witnesses directly;
there is no choice of a canonical witness and no inference of Collection
from functional Replacement without Foundation.

The finite base has Extensionality, Pairing, Union and actual Form Separation.
The only Separation matrix used below is membership in a parameter, for an
intersection. WF closure requests one displayed GIC formula. Its matrix is
equality-free. InternallyWellFounded quantifies over represented sets, not
arbitrary external subsets, and no external WellFounded relation is assumed.
This is not yet the full ZF interpretation or a consistency comparison.
-/

namespace SetTheory.BusyBeaver.ZFC.WellFoundedPart

open Form PositiveClosure DeepPositiveClosure ProfileCollection ProfileSyntax

universe u
variable {V : Type u} {mem : V → V → Prop}

def NonemptySet (mem : V → V → Prop) (s : V) : Prop := ∃ x, mem x s

def Minimal (mem : V → V → Prop) (m s : V) : Prop :=
  mem m s ∧ ∀ z, mem z m → ¬ mem z s

def InternallyWellFounded (mem : V → V → Prop) (t : V) : Prop :=
  ∀ s, Sub mem s t → NonemptySet mem s → ∃ m, Minimal mem m s

def TW (mem : V → V → Prop) (t : V) : Prop :=
  Transitive mem t ∧ InternallyWellFounded mem t

def WF (mem : V → V → Prop) (x : V) : Prop :=
  ∃ t, TW mem t ∧ mem x t

def transitiveForm (i : Nat) : Form :=
  fAll (fImp (fMem 0 (i + 1)) (subsetForm 0 (i + 1)))

def nonemptyForm (i : Nat) : Form := fEx (fMem 0 (i + 1))

def minimalElementForm (m s : Nat) : Form :=
  fAnd (fMem m s)
    (fAll (fImp (fMem 0 (m + 1)) (fImp (fMem 0 (s + 1)) fBot)))

def minimalForm (i : Nat) : Form := fEx (minimalElementForm 0 (i + 1))

def wellFoundedForm (i : Nat) : Form :=
  fAll (fImp (subsetForm 0 (i + 1))
    (fImp (nonemptyForm 0) (minimalForm 0)))

def twForm (i : Nat) : Form := fAnd (transitiveForm i) (wellFoundedForm i)

def wfForm (i : Nat) : Form := fEx (fAnd (twForm 0) (fMem (i + 1) 0))

/-- Input 0, witness output 1; there are no additional parameters. -/
def witnessForm : Form := fAnd (twForm 1) (fMem 0 1)

theorem sat_transitiveForm (mem : V → V → Prop) (env : Nat → V) (i : Nat) :
    Sat mem env (transitiveForm i) ↔ Transitive mem (env i) :=
  forall_congr' fun x => imp_congr_right fun _ => sat_subsetForm mem (scons x env) 0 (i + 1)

theorem sat_nonemptyForm (mem : V → V → Prop) (env : Nat → V) (i : Nat) :
    Sat mem env (nonemptyForm i) ↔ NonemptySet mem (env i) := Iff.rfl

theorem sat_minimalElementForm (mem : V → V → Prop) (env : Nat → V) (m s : Nat) :
    Sat mem env (minimalElementForm m s) ↔ Minimal mem (env m) (env s) := Iff.rfl

theorem sat_minimalForm (mem : V → V → Prop) (env : Nat → V) (i : Nat) :
    Sat mem env (minimalForm i) ↔ ∃ m, Minimal mem m (env i) :=
  exists_congr fun m => sat_minimalElementForm mem (scons m env) 0 (i + 1)

theorem sat_wellFoundedForm (mem : V → V → Prop) (env : Nat → V) (i : Nat) :
    Sat mem env (wellFoundedForm i) ↔ InternallyWellFounded mem (env i) :=
  forall_congr' fun s => imp_congr (sat_subsetForm mem (scons s env) 0 (i + 1))
    (imp_congr (sat_nonemptyForm mem (scons s env) 0) (sat_minimalForm mem (scons s env) 0))

theorem sat_twForm (mem : V → V → Prop) (env : Nat → V) (i : Nat) :
    Sat mem env (twForm i) ↔ TW mem (env i) :=
  and_congr (sat_transitiveForm mem env i) (sat_wellFoundedForm mem env i)

theorem sat_wfForm (mem : V → V → Prop) (env : Nat → V) (i : Nat) :
    Sat mem env (wfForm i) ↔ WF mem (env i) :=
  exists_congr fun t => and_congr (sat_twForm mem (scons t env) 0) Iff.rfl

theorem sat_witnessForm (mem : V → V → Prop) (env : Nat → V) (x t : V) :
    MatrixRelation mem witnessForm env x t ↔ TW mem t ∧ mem x t :=
  and_congr (sat_twForm mem (scons x (scons t env)) 1) Iff.rfl

theorem equalityFree_witnessForm : EqualityFree witnessForm := by
  simp [witnessForm, twForm, transitiveForm, wellFoundedForm, nonemptyForm,
    minimalForm, minimalElementForm, subsetForm, EqualityFree]

theorem equalityFree_wfForm (i : Nat) : EqualityFree (wfForm i) := by
  simp [wfForm, twForm, transitiveForm, wellFoundedForm, nonemptyForm,
    minimalForm, minimalElementForm, subsetForm, EqualityFree]

/-- This is exactly the Separation instance with matrix Mem(0,1). -/
theorem intersection_exists (B : FiniteSets.Base mem) (s t : V) :
    ∃ b, ∀ x, mem x b ↔ mem x s ∧ mem x t :=
  B.sep (fMem 0 1) (fun _ => t) s

/-- Meeting a TW set suffices: intersect, take a minimal element, and use
transitivity to rule out children lying elsewhere in the original set. -/
theorem minimal_of_meets_tw (B : FiniteSets.Base mem) (t : V) (ht : TW mem t)
    (s : V) (hMeet : ∃ x, mem x s ∧ mem x t) : ∃ m, Minimal mem m s := by
  obtain ⟨b, hb⟩ := intersection_exists B s t
  have hSub : Sub mem b t := fun x hx => ((hb x).mp hx).2
  obtain ⟨x, hxs, hxt⟩ := hMeet
  obtain ⟨m, hmb, hMin⟩ := ht.2 b hSub ⟨x, (hb x).mpr ⟨hxs, hxt⟩⟩
  refine ⟨m, ((hb m).mp hmb).1, ?_⟩
  intro z hzm hzs
  exact hMin z hzm ((hb z).mpr ⟨hzs, ht.1 m (hSub m hmb) z hzm⟩)

theorem tw_union (B : FiniteSets.Base mem) (c : V)
    (hFamily : ∀ t, mem t c → TW mem t) : TW mem (FiniteSets.union B c) := by
  constructor
  · intro x hx z hz
    obtain ⟨t, hxt, htc⟩ := (FiniteSets.union_spec B c x).mp hx
    exact (FiniteSets.union_spec B c z).mpr
      ⟨t, (hFamily t htc).1 x hxt z hz, htc⟩
  · intro s hs hne
    obtain ⟨x, hxs⟩ := hne
    obtain ⟨t, hxt, htc⟩ := (FiniteSets.union_spec B c x).mp (hs x hxs)
    exact minimal_of_meets_tw B t (hFamily t htc) s ⟨x, hxs, hxt⟩

/-- Adjoin a set whose every member already lies in the TW set. -/
theorem tw_adjoin (B : FiniteSets.Base mem) (u a : V)
    (hu : TW mem u) (ha : Sub mem a u) : TW mem (FiniteSets.insert B u a) := by
  constructor
  · intro x hx z hz
    rcases (FiniteSets.insert_spec B u a x).mp hx with hx | hxa
    · exact (FiniteSets.insert_spec B u a z).mpr (Or.inl (hu.1 x hx z hz))
    · have hza : mem z a := hxa ▸ hz
      exact (FiniteSets.insert_spec B u a z).mpr (Or.inl (ha z hza))
  · intro s hs hne
    classical
    by_cases hMeet : ∃ x, mem x s ∧ mem x u
    · exact minimal_of_meets_tw B u hu s hMeet
    · obtain ⟨x, hxs⟩ := hne
      rcases (FiniteSets.insert_spec B u a x).mp (hs x hxs) with hxu | hxa
      · exact False.elim (hMeet ⟨x, hxs, hxu⟩)
      · subst x
        exact ⟨a, hxs, fun z hza hzs => hMeet ⟨z, hzs, ha z hza⟩⟩

/-- A single displayed actual GIC formula collects all needed TW witnesses.
No schema over arbitrary semantic relations is a premise. -/
theorem wf_closure (B : FiniteSets.Base mem) (a : V)
    (hG : Sat mem (fun _ => a) (gicForm witnessForm))
    (ha : ∀ x, mem x a → WF mem x) : WF mem a := by
  have hc : CollectionInstance mem (fun x t => TW mem t ∧ mem x t) :=
    ProfileModel.collectionInstance_congr mem _ _ (sat_witnessForm mem (fun _ => a))
      ((sat_gicForm mem witnessForm (fun _ => a)).mp hG)
  obtain ⟨c, hSupport, hCover⟩ := hc a
  have hFamily : ∀ t, mem t c → TW mem t := fun t ht => (hSupport t ht).elim fun _ h => h.1
  have haU : Sub mem a (FiniteSets.union B c) := by
    intro x hx
    obtain ⟨t, htc, _, hxt⟩ := hCover x hx (ha x hx)
    exact (FiniteSets.union_spec B c x).mpr ⟨t, hxt, htc⟩
  exact ⟨FiniteSets.insert B (FiniteSets.union B c) a,
    tw_adjoin B _ a (tw_union B c hFamily) haU,
    (FiniteSets.insert_spec B _ a a).mpr (Or.inr rfl)⟩

theorem wf_closure_of_equalityFree_gic (B : FiniteSets.Base mem)
    (hG : ProfileModel.ModelsGIC mem) (a : V)
    (ha : ∀ x, mem x a → WF mem x) : WF mem a :=
  wf_closure B a (hG witnessForm equalityFree_witnessForm (fun _ => a)) ha

theorem wf_mem {x y : V} (hx : WF mem x) (hy : mem y x) : WF mem y := by
  obtain ⟨t, ht, hxt⟩ := hx
  exact ⟨t, ht, ht.1 x hxt y hy⟩

/-- Pairing alone supplies the TW singleton witness for an actual empty set. -/
theorem wf_empty (B : FiniteSets.Base mem) (e : V) (he : ∀ z, ¬ mem z e) :
    WF mem e := by
  have ht : TW mem (FiniteSets.singleton B e) := by
    constructor
    · intro x hx z hz
      have hxe := (FiniteSets.singleton_spec B e x).mp hx
      subst x
      exact False.elim (he z hz)
    · intro s hs hne
      obtain ⟨x, hxs⟩ := hne
      have hxe := (FiniteSets.singleton_spec B e x).mp (hs x hxs)
      subst x
      exact ⟨e, hxs, fun z hze => False.elim (he z hze)⟩
  exact ⟨FiniteSets.singleton B e, ht, (FiniteSets.singleton_spec B e e).mpr rfl⟩

/-- The ordinary well-founded-part minimal-element property is internal. -/
theorem wf_minimal (a : V) (ha : WF mem a) (hne : NonemptySet mem a) :
    ∃ m, mem m a ∧ WF mem m ∧ ∀ z, mem z m → ¬ mem z a := by
  obtain ⟨t, ht, hat⟩ := ha
  obtain ⟨m, hm, hMin⟩ := ht.2 a (ht.1 a hat) hne
  exact ⟨m, hm, ⟨t, ht, ht.1 a hat m hm⟩, hMin⟩

def Domain (mem : V → V → Prop) := {x : V // WF mem x}

def domainMem (mem : V → V → Prop) (x y : Domain mem) : Prop := mem x.1 y.1

/-- The actual Reg_form holds in the WF subtype. Other ZF axioms still
require their interpreted instance proofs; this is not a full model claim. -/
theorem domain_regular (mem : V → V → Prop) :
    ∀ env : Nat → Domain mem, Sat (domainMem mem) env Reg_form := by
  apply bridge_Reg.mpr
  intro a hne
  obtain ⟨x, hx⟩ := hne
  obtain ⟨m, hm, hwm, hMin⟩ := wf_minimal a.1 a.2 ⟨x.1, hx⟩
  refine ⟨⟨m, hwm⟩, hm, ?_⟩
  rintro ⟨z, hzm, hza⟩
  exact hMin z.1 hzm hza

end SetTheory.BusyBeaver.ZFC.WellFoundedPart
