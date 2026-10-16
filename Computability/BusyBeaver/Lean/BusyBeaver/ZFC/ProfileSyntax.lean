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
    Sat mem env (classMemberForm i j) ↔ ClassMember mem (env i) (env j) := by
  constructor
  · rintro ⟨z, hz, hSame⟩
    exact ⟨z, hz, (sat_sameForm mem (scons z env) (i + 1) 0).mp hSame⟩
  · rintro ⟨z, hz, hSame⟩
    exact ⟨z, hz, (sat_sameForm mem (scons z env) (i + 1) 0).mpr hSame⟩

theorem sat_singletonForm (mem : V → V → Prop) (env : Nat → V) (i j : Nat) :
    Sat mem env (singletonForm i j) ↔ Singleton mem (env i) (env j) := by
  constructor
  · intro h z
    exact (sat_classMemberForm mem (scons z env) 0 (i + 1)).symm.trans
      ((Sat_fIff.mp (h z)).trans (sat_sameForm mem (scons z env) 0 (j + 1)))
  · intro h z
    apply Sat_fIff.mpr
    exact (sat_classMemberForm mem (scons z env) 0 (i + 1)).trans
      ((h z).trans (sat_sameForm mem (scons z env) 0 (j + 1)).symm)

theorem sat_pairForm (mem : V → V → Prop) (env : Nat → V) (p i j : Nat) :
    Sat mem env (pairForm p i j) ↔ Pair mem (env p) (env i) (env j) := by
  have hRight (z : V) := or_congr
    (sat_sameForm mem (scons z env) 0 (i + 1))
    (sat_sameForm mem (scons z env) 0 (j + 1))
  constructor
  · intro h z
    exact (sat_classMemberForm mem (scons z env) 0 (p + 1)).symm.trans
      ((Sat_fIff.mp (h z)).trans (hRight z))
  · intro h z
    apply Sat_fIff.mpr
    exact (sat_classMemberForm mem (scons z env) 0 (p + 1)).trans
      ((h z).trans (hRight z).symm)

theorem sat_orderedPairForm (mem : V → V → Prop) (env : Nat → V) (i j c : Nat) :
    Sat mem env (orderedPairForm i j c) ↔
      OrderedPair mem (env i) (env j) (env c) := by
  constructor
  · rintro ⟨s, p, hs, hp, hc⟩
    exact ⟨s, p, (sat_singletonForm mem _ 1 (i + 2)).mp hs,
      (sat_pairForm mem _ 0 (i + 2) (j + 2)).mp hp,
      (sat_pairForm mem _ (c + 2) 1 0).mp hc⟩
  · rintro ⟨s, p, hs, hp, hc⟩
    exact ⟨s, p, (sat_singletonForm mem _ 1 (i + 2)).mpr hs,
      (sat_pairForm mem _ 0 (i + 2) (j + 2)).mpr hp,
      (sat_pairForm mem _ (c + 2) 1 0).mpr hc⟩

/-- GIC's support and selected-image coverage, with universally closed parameters. -/
def gicForm (phi : Form) : Form :=
  fAll (fEx (fAnd
    (fAll (fImp (fMem 0 1) (fEx (rename supportRename phi))))
    (fAll (fImp (fMem 0 2)
      (fImp (fEx (rename forwardRename phi))
        (fEx (fAnd (fMem 0 2) (rename forwardRename phi))))))))

theorem sat_gicForm (mem : V → V → Prop) (phi : Form) (env : Nat → V) :
    Sat mem env (gicForm phi) ↔ CollectionInstance mem (MatrixRelation mem phi env) := by
  constructor
  · intro h a
    obtain ⟨b, hSupport, hCover⟩ := h a
    refine ⟨b, ?_, ?_⟩
    · intro y hy
      obtain ⟨x, hxy⟩ := hSupport y hy
      exact ⟨x, (sat_support_matrix mem phi env a b y x).mp hxy⟩
    · intro x hx hOutput
      have hSome : Sat mem (scons x (scons b (scons a env)))
          (fEx (rename forwardRename phi)) := by
        obtain ⟨y, hxy⟩ := hOutput
        exact ⟨y, (sat_forward_matrix mem phi env a b x y).mpr hxy⟩
      obtain ⟨y, hy, hxy⟩ := hCover x hx hSome
      exact ⟨y, hy, (sat_forward_matrix mem phi env a b x y).mp hxy⟩
  · intro h a
    obtain ⟨b, hSupport, hCover⟩ := h a
    refine ⟨b, ?_, ?_⟩
    · intro y hy
      obtain ⟨x, hxy⟩ := hSupport y hy
      exact ⟨x, (sat_support_matrix mem phi env a b y x).mpr hxy⟩
    · intro x hx hOutput
      have hSome : ∃ y, MatrixRelation mem phi env x y := by
        obtain ⟨y, hxy⟩ := hOutput
        exact ⟨y, (sat_forward_matrix mem phi env a b x y).mp hxy⟩
      obtain ⟨y, hy, hxy⟩ := hCover x hx hSome
      exact ⟨y, hy, (sat_forward_matrix mem phi env a b x y).mpr hxy⟩

theorem equalityFree_sameForm (i j : Nat) : EqualityFree (sameForm i j) := by
  exact ⟨⟨True.intro, True.intro⟩, ⟨True.intro, True.intro⟩⟩

theorem equalityFree_classMemberForm (i j : Nat) : EqualityFree (classMemberForm i j) := by
  exact ⟨True.intro, equalityFree_sameForm (i + 1) 0⟩

theorem equalityFree_singletonForm (i j : Nat) : EqualityFree (singletonForm i j) := by
  exact ⟨⟨equalityFree_classMemberForm 0 (i + 1), equalityFree_sameForm 0 (j + 1)⟩,
    ⟨equalityFree_sameForm 0 (j + 1), equalityFree_classMemberForm 0 (i + 1)⟩⟩

theorem equalityFree_pairForm (p i j : Nat) : EqualityFree (pairForm p i j) := by
  have hRight := And.intro (equalityFree_sameForm 0 (i + 1)) (equalityFree_sameForm 0 (j + 1))
  exact ⟨⟨equalityFree_classMemberForm 0 (p + 1), hRight⟩,
    ⟨hRight, equalityFree_classMemberForm 0 (p + 1)⟩⟩

theorem equalityFree_orderedPairForm (i j c : Nat) : EqualityFree (orderedPairForm i j c) := by
  exact ⟨equalityFree_singletonForm 1 (i + 2),
    ⟨equalityFree_pairForm 0 (i + 2) (j + 2), equalityFree_pairForm (c + 2) 1 0⟩⟩

theorem equalityFree_gicForm (phi : Form) (h : EqualityFree phi) :
    EqualityFree (gicForm phi) := by
  exact ⟨⟨True.intro, equalityFree_rename phi supportRename h⟩,
    ⟨True.intro, ⟨equalityFree_rename phi forwardRename h,
      ⟨True.intro, equalityFree_rename phi forwardRename h⟩⟩⟩⟩

#print axioms sat_orderedPairForm
#print axioms sat_gicForm
#print axioms equalityFree_orderedPairForm

end SetTheory.BusyBeaver.ZFC.ProfileSyntax
