import BusyBeaver.ZFC.ProfileCollection
import BusyBeaver.ZFC.DeepPositiveClosure

/-!
Actual first-order syntax for the equality-free collection interpretation.

The GIC matrix uses input slot 0, output slot 1 and parameter slots 2+k.
Profile-singleton, pair and ordered-pair predicates have checked satisfaction
specifications. No logical equality is introduced by these definitions.
This is not yet the whole bisimulation interpretation or a machine theorem.
-/

namespace SetTheory.BusyBeaver.ZFC.ProfileSyntax

open Form Profile ProfilePairs ProfileCollection DeepPositiveClosure

universe u
variable {V : Type u}

/-- Transport an equivalence using only its two implications. -/
theorem iff_congr_iff {a b c d : Prop} (ha : a ↔ c) (hb : b ↔ d) :
    (a ↔ b) ↔ (c ↔ d) :=
  ⟨fun h => ha.symm.trans (h.trans hb), fun h => ha.trans (h.trans hb.symm)⟩

def classMemberForm (i j : Nat) : Form :=
  fEx (fAnd (fMem 0 (j + 1)) (sameForm (i + 1) 0))

def singletonForm (i j : Nat) : Form :=
  fAll (fIff (classMemberForm 0 (i + 1)) (sameForm 0 (j + 1)))

def pairForm (p i j : Nat) : Form :=
  fAll (fIff (classMemberForm 0 (p + 1))
    (fOr (sameForm 0 (i + 1)) (sameForm 0 (j + 1))))

def orderedPairForm (i j c : Nat) : Form :=
  fEx (fEx (fAnd (singletonForm 1 (i + 2))
    (fAnd (pairForm 0 (i + 2) (j + 2)) (pairForm (c + 2) 1 0))))

theorem sat_classMemberForm (mem : V → V → Prop) (env : Nat → V) (i j : Nat) :
    Sat mem env (classMemberForm i j) ↔ ClassMember mem (env i) (env j) :=
  exists_congr fun z => and_congr Iff.rfl (sat_sameForm mem (scons z env) (i + 1) 0)

theorem sat_singletonForm (mem : V → V → Prop) (env : Nat → V) (i j : Nat) :
    Sat mem env (singletonForm i j) ↔ Singleton mem (env i) (env j) :=
  forall_congr' fun z => Sat_fIff.trans (iff_congr_iff
    (sat_classMemberForm mem (scons z env) 0 (i + 1))
    (sat_sameForm mem (scons z env) 0 (j + 1)))

theorem sat_pairForm (mem : V → V → Prop) (env : Nat → V) (p i j : Nat) :
    Sat mem env (pairForm p i j) ↔ Pair mem (env p) (env i) (env j) :=
  forall_congr' fun z => Sat_fIff.trans (iff_congr_iff
    (sat_classMemberForm mem (scons z env) 0 (p + 1)) (or_congr
      (sat_sameForm mem (scons z env) 0 (i + 1))
      (sat_sameForm mem (scons z env) 0 (j + 1))))

theorem sat_orderedPairForm (mem : V → V → Prop) (env : Nat → V) (i j c : Nat) :
    Sat mem env (orderedPairForm i j c) ↔
      OrderedPair mem (env i) (env j) (env c) :=
  exists_congr fun s => exists_congr fun p =>
    and_congr (sat_singletonForm mem (scons p (scons s env)) 1 (i + 2))
      (and_congr (sat_pairForm mem _ 0 (i + 2) (j + 2))
        (sat_pairForm mem _ (c + 2) 1 0))

def appForm (r i j : Nat) : Form :=
  fEx (fAnd (fMem 0 (r + 1)) (orderedPairForm (i + 1) (j + 1) 0))

def bisimForm (r : Nat) : Form :=
  fAll (fAll (fImp (appForm (r + 2) 1 0) (fAnd
    (fAll (fImp (fMem 0 2)
      (fEx (fAnd (fMem 0 2) (appForm (r + 4) 1 0)))))
    (fAll (fImp (fMem 0 1)
      (fEx (fAnd (fMem 0 3) (appForm (r + 4) 0 1))))))))

def eqvForm (i j : Nat) : Form :=
  fEx (fAnd (bisimForm 0) (appForm 0 (i + 1) (j + 1)))

theorem sat_appForm (mem : V → V → Prop) (env : Nat → V) (r i j : Nat) :
    Sat mem env (appForm r i j) ↔ App mem (env r) (env i) (env j) :=
  exists_congr fun c => and_congr Iff.rfl
    (sat_orderedPairForm mem (scons c env) (i + 1) (j + 1) 0)

theorem sat_bisimForm (mem : V → V → Prop) (env : Nat → V) (r : Nat) :
    Sat mem env (bisimForm r) ↔ Bisim mem (env r) :=
  forall_congr' fun x => forall_congr' fun y =>
    imp_congr (sat_appForm mem (scons y (scons x env)) (r + 2) 1 0) (and_congr
      (forall_congr' fun a => imp_congr_right fun _ =>
        exists_congr fun b => and_congr Iff.rfl
          (sat_appForm mem (scons b (scons a (scons y (scons x env)))) (r + 4) 1 0))
      (forall_congr' fun b => imp_congr_right fun _ =>
        exists_congr fun a => and_congr Iff.rfl
          (sat_appForm mem (scons a (scons b (scons y (scons x env)))) (r + 4) 0 1)))

theorem sat_eqvForm (mem : V → V → Prop) (env : Nat → V) (i j : Nat) :
    Sat mem env (eqvForm i j) ↔ Eqv mem (env i) (env j) :=
  exists_congr fun r => and_congr (sat_bisimForm mem (scons r env) 0)
    (sat_appForm mem _ 0 (i + 1) (j + 1))

/-- GIC's support and selected-image coverage, with universally closed parameters. -/
def gicForm (phi : Form) : Form :=
  fAll (fEx (fAnd
    (fAll (fImp (fMem 0 1) (fEx (rename supportRename phi))))
    (fAll (fImp (fMem 0 2)
      (fImp (fEx (rename forwardRename phi))
        (fEx (fAnd (fMem 0 2) (rename forwardRename phi))))))))

theorem sat_gicForm (mem : V → V → Prop) (phi : Form) (env : Nat → V) :
    Sat mem env (gicForm phi) ↔ CollectionInstance mem (MatrixRelation mem phi env) :=
  forall_congr' fun a => exists_congr fun b => and_congr
    (forall_congr' fun y => imp_congr_right fun _ =>
      exists_congr fun x => sat_support_matrix mem phi env a b y x)
    (forall_congr' fun x => imp_congr_right fun _ => imp_congr
      (exists_congr fun y => sat_forward_matrix mem phi env a b x y)
      (exists_congr fun y => and_congr Iff.rfl (sat_forward_matrix mem phi env a b x y)))

theorem equalityFree_sameForm (i j : Nat) : EqualityFree (sameForm i j) :=
  ⟨⟨True.intro, True.intro⟩, ⟨True.intro, True.intro⟩⟩

theorem equalityFree_classMemberForm (i j : Nat) : EqualityFree (classMemberForm i j) :=
  ⟨True.intro, equalityFree_sameForm (i + 1) 0⟩

theorem equalityFree_singletonForm (i j : Nat) : EqualityFree (singletonForm i j) :=
  ⟨⟨equalityFree_classMemberForm 0 (i + 1), equalityFree_sameForm 0 (j + 1)⟩,
    ⟨equalityFree_sameForm 0 (j + 1), equalityFree_classMemberForm 0 (i + 1)⟩⟩

theorem equalityFree_pairForm (p i j : Nat) : EqualityFree (pairForm p i j) := by
  have hRight := And.intro (equalityFree_sameForm 0 (i + 1)) (equalityFree_sameForm 0 (j + 1))
  exact ⟨⟨equalityFree_classMemberForm 0 (p + 1), hRight⟩,
    ⟨hRight, equalityFree_classMemberForm 0 (p + 1)⟩⟩

theorem equalityFree_orderedPairForm (i j c : Nat) : EqualityFree (orderedPairForm i j c) :=
  ⟨equalityFree_singletonForm 1 (i + 2),
    ⟨equalityFree_pairForm 0 (i + 2) (j + 2), equalityFree_pairForm (c + 2) 1 0⟩⟩

theorem equalityFree_appForm (r i j : Nat) : EqualityFree (appForm r i j) :=
  ⟨True.intro, equalityFree_orderedPairForm (i + 1) (j + 1) 0⟩

theorem equalityFree_bisimForm (r : Nat) : EqualityFree (bisimForm r) :=
  ⟨equalityFree_appForm (r + 2) 1 0,
    ⟨⟨True.intro, ⟨True.intro, equalityFree_appForm (r + 4) 1 0⟩⟩,
      ⟨True.intro, ⟨True.intro, equalityFree_appForm (r + 4) 0 1⟩⟩⟩⟩

theorem equalityFree_eqvForm (i j : Nat) : EqualityFree (eqvForm i j) :=
  ⟨equalityFree_bisimForm 0, equalityFree_appForm 0 (i + 1) (j + 1)⟩

theorem equalityFree_gicForm (phi : Form) (h : EqualityFree phi) :
    EqualityFree (gicForm phi) :=
  ⟨⟨True.intro, equalityFree_rename phi supportRename h⟩,
    ⟨True.intro, ⟨equalityFree_rename phi forwardRename h,
      ⟨True.intro, equalityFree_rename phi forwardRename h⟩⟩⟩⟩

#print axioms sat_orderedPairForm
#print axioms sat_gicForm
#print axioms equalityFree_orderedPairForm

end SetTheory.BusyBeaver.ZFC.ProfileSyntax
