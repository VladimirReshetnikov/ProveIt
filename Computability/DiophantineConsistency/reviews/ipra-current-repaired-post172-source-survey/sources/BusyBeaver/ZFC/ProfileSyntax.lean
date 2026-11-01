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
    Sat mem env (classMemberForm i j) ↔ ClassMember mem (env i) (env j) :=
  ⟨fun ⟨z, hz, hSame⟩ => ⟨z, hz, (sat_sameForm mem (scons z env) (i + 1) 0).mp hSame⟩,
    fun ⟨z, hz, hSame⟩ => ⟨z, hz, (sat_sameForm mem (scons z env) (i + 1) 0).mpr hSame⟩⟩

theorem sat_singletonForm (mem : V → V → Prop) (env : Nat → V) (i j : Nat) :
    Sat mem env (singletonForm i j) ↔ Singleton mem (env i) (env j) :=
  ⟨fun h z => (sat_classMemberForm mem (scons z env) 0 (i + 1)).symm.trans
      ((Sat_fIff.mp (h z)).trans (sat_sameForm mem (scons z env) 0 (j + 1))),
    fun h z => Sat_fIff.mpr ((sat_classMemberForm mem (scons z env) 0 (i + 1)).trans
      ((h z).trans (sat_sameForm mem (scons z env) 0 (j + 1)).symm))⟩

theorem sat_pairForm (mem : V → V → Prop) (env : Nat → V) (p i j : Nat) :
    Sat mem env (pairForm p i j) ↔ Pair mem (env p) (env i) (env j) := by
  have hRight (z : V) := or_congr
    (sat_sameForm mem (scons z env) 0 (i + 1))
    (sat_sameForm mem (scons z env) 0 (j + 1))
  exact ⟨fun h z => (sat_classMemberForm mem (scons z env) 0 (p + 1)).symm.trans
      ((Sat_fIff.mp (h z)).trans (hRight z)),
    fun h z => Sat_fIff.mpr ((sat_classMemberForm mem (scons z env) 0 (p + 1)).trans
      ((h z).trans (hRight z).symm))⟩

theorem sat_orderedPairForm (mem : V → V → Prop) (env : Nat → V) (i j c : Nat) :
    Sat mem env (orderedPairForm i j c) ↔
      OrderedPair mem (env i) (env j) (env c) :=
  ⟨fun ⟨s, p, hs, hp, hc⟩ => ⟨s, p, (sat_singletonForm mem _ 1 (i + 2)).mp hs,
      (sat_pairForm mem _ 0 (i + 2) (j + 2)).mp hp, (sat_pairForm mem _ (c + 2) 1 0).mp hc⟩,
    fun ⟨s, p, hs, hp, hc⟩ => ⟨s, p, (sat_singletonForm mem _ 1 (i + 2)).mpr hs,
      (sat_pairForm mem _ 0 (i + 2) (j + 2)).mpr hp, (sat_pairForm mem _ (c + 2) 1 0).mpr hc⟩⟩

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
  ⟨fun ⟨c, hc, hPair⟩ => ⟨c, hc, (sat_orderedPairForm mem _ (i + 1) (j + 1) 0).mp hPair⟩,
    fun ⟨c, hc, hPair⟩ => ⟨c, hc, (sat_orderedPairForm mem _ (i + 1) (j + 1) 0).mpr hPair⟩⟩

theorem sat_bisimForm (mem : V → V → Prop) (env : Nat → V) (r : Nat) :
    Sat mem env (bisimForm r) ↔ Bisim mem (env r) := by
  constructor
  · intro h x y hxy
    obtain ⟨hForth, hBack⟩ := h x y ((sat_appForm mem _ (r + 2) 1 0).mpr hxy)
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · obtain ⟨b, hb, hEdge⟩ := hForth a ha
      exact ⟨b, hb, (sat_appForm mem _ (r + 4) 1 0).mp hEdge⟩
    · obtain ⟨a, ha, hEdge⟩ := hBack b hb
      exact ⟨a, ha, (sat_appForm mem _ (r + 4) 0 1).mp hEdge⟩
  · intro h x y hxy
    obtain ⟨hForth, hBack⟩ := h x y ((sat_appForm mem _ (r + 2) 1 0).mp hxy)
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · obtain ⟨b, hb, hEdge⟩ := hForth a ha
      exact ⟨b, hb, (sat_appForm mem _ (r + 4) 1 0).mpr hEdge⟩
    · obtain ⟨a, ha, hEdge⟩ := hBack b hb
      exact ⟨a, ha, (sat_appForm mem _ (r + 4) 0 1).mpr hEdge⟩

theorem sat_eqvForm (mem : V → V → Prop) (env : Nat → V) (i j : Nat) :
    Sat mem env (eqvForm i j) ↔ Eqv mem (env i) (env j) :=
  ⟨fun ⟨r, hr, hEdge⟩ => ⟨r, (sat_bisimForm mem _ 0).mp hr,
      (sat_appForm mem _ 0 (i + 1) (j + 1)).mp hEdge⟩,
    fun ⟨r, hr, hEdge⟩ => ⟨r, (sat_bisimForm mem _ 0).mpr hr,
      (sat_appForm mem _ 0 (i + 1) (j + 1)).mpr hEdge⟩⟩

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
    refine ⟨b, fun y hy => ?_, fun x hx hOutput => ?_⟩
    · obtain ⟨x, hxy⟩ := hSupport y hy
      exact ⟨x, (sat_support_matrix mem phi env a b y x).mp hxy⟩
    · have hSome : Sat mem (scons x (scons b (scons a env)))
          (fEx (rename forwardRename phi)) := by
        obtain ⟨y, hxy⟩ := hOutput
        exact ⟨y, (sat_forward_matrix mem phi env a b x y).mpr hxy⟩
      obtain ⟨y, hy, hxy⟩ := hCover x hx hSome
      exact ⟨y, hy, (sat_forward_matrix mem phi env a b x y).mp hxy⟩
  · intro h a
    obtain ⟨b, hSupport, hCover⟩ := h a
    refine ⟨b, fun y hy => ?_, fun x hx hOutput => ?_⟩
    · obtain ⟨x, hxy⟩ := hSupport y hy
      exact ⟨x, (sat_support_matrix mem phi env a b y x).mpr hxy⟩
    · have hSome : ∃ y, MatrixRelation mem phi env x y := by
        obtain ⟨y, hxy⟩ := hOutput
        exact ⟨y, (sat_forward_matrix mem phi env a b x y).mp hxy⟩
      obtain ⟨y, hy, hxy⟩ := hCover x hx hSome
      exact ⟨y, hy, (sat_forward_matrix mem phi env a b x y).mpr hxy⟩

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
