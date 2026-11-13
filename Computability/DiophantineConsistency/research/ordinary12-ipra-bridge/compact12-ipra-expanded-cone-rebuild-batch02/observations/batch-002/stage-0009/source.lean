import FirstOrder.Fol
import BusyBeaver.ZFC.PositiveClosure

/-!
The subset-only subset-seeded positive closure wrapper in actual `SetTheory.Form`.

Matrix slots are 0=input, 1=output, 2+k=parameter k. The three explicit renamings
place the matrix under the bound/forward/support binders without capturing its
parameters, including beneath any binders internal to the matrix itself.

This file connects one definable first-order schema instance to the previously
proved shallow semantic interface. It does not prove deductive equivalence of
whole theories, an internal ZFC proof-code theorem, or a Turing-machine endpoint.
The bridge works for arbitrary matrices. If the matrix is equality-free, the
wrapper remains equality-free; no equality is introduced by the wrapper.
-/

namespace SetTheory.BusyBeaver.ZFC.DeepPositiveClosure

open Form

universe u
variable {V : Type u}

/-- The binary relation named by the actual matrix, with input first. -/
def MatrixRelation (mem : V → V → Prop) (phi : Form) (env : Nat → V)
    (x y : V) : Prop :=
  Sat mem (scons x (scons y env)) phi

/-- A subset test at the current De Bruijn slots i,j, with its own fresh binder. -/
def subsetForm (i j : Nat) : Form :=
  fAll (fImp (fMem 0 (i + 1)) (fMem 0 (j + 1)))

/-- Under forall x, exists b, forall y: y=0,b=1,x=2,parameters=3+k. -/
def boundRename : Nat → Nat
  | 0 => 2
  | 1 => 0
  | k + 2 => k + 3

/-- Under forall A, exists C, forall x, forall y:
y=0,x=1,C=2,A=3,parameters=4+k. -/
def forwardRename : Nat → Nat
  | 0 => 1
  | 1 => 0
  | k + 2 => k + 4

/-- Under forall A, exists C, forall y, exists x:
x=0,y=1,C=2,A=3,parameters=4+k. -/
def supportRename : Nat → Nat
  | 0 => 0
  | 1 => 1
  | k + 2 => k + 4

/-- The local subset-boundedness antecedent. -/
def subsetBoundForm (phi : Form) : Form :=
  fAll (fEx (fAll (fImp (rename boundRename phi) (subsetForm 0 1))))

/-- The positive hull conclusion, without the local boundedness antecedent. -/
def positiveBodyForm (phi : Form) : Form :=
  fAll (fEx (fAnd
    (fAll (fAll (fImp
      (fAnd (fOr (subsetForm 1 3) (fMem 1 2)) (rename forwardRename phi))
      (fMem 0 2))))
    (fAll (fImp (fMem 0 1) (fEx (rename supportRename phi))))))

/-- One subset-only subset-seeded positive closure schema instance. -/
def pscForm (phi : Form) : Form :=
  fImp (subsetBoundForm phi) (positiveBodyForm phi)

theorem sat_subsetForm (mem : V → V → Prop) (env : Nat → V) (i j : Nat) :
    Sat mem env (subsetForm i j) ↔ PositiveClosure.Sub mem (env i) (env j) :=
  Iff.rfl

theorem bound_env (x b y : V) (env : Nat → V) :
    ∀ n, scons y (scons b (scons x env)) (boundRename n) =
      scons x (scons y env) n :=
  fun n => match n with | 0 => rfl | 1 => rfl | _ + 2 => rfl

theorem forward_env (a c x y : V) (env : Nat → V) :
    ∀ n, scons y (scons x (scons c (scons a env))) (forwardRename n) =
      scons x (scons y env) n :=
  fun n => match n with | 0 => rfl | 1 => rfl | _ + 2 => rfl

theorem support_env (a c y x : V) (env : Nat → V) :
    ∀ n, scons x (scons y (scons c (scons a env))) (supportRename n) =
      scons x (scons y env) n :=
  fun n => match n with | 0 => rfl | 1 => rfl | _ + 2 => rfl

theorem sat_bound_matrix (mem : V → V → Prop) (phi : Form) (env : Nat → V)
    (x b y : V) :
    Sat mem (scons y (scons b (scons x env))) (rename boundRename phi) ↔
      MatrixRelation mem phi env x y :=
  Sat_rename_ext phi boundRename _ _ (bound_env x b y env)

theorem sat_forward_matrix (mem : V → V → Prop) (phi : Form) (env : Nat → V)
    (a c x y : V) :
    Sat mem (scons y (scons x (scons c (scons a env)))) (rename forwardRename phi) ↔
      MatrixRelation mem phi env x y :=
  Sat_rename_ext phi forwardRename _ _ (forward_env a c x y env)

theorem sat_support_matrix (mem : V → V → Prop) (phi : Form) (env : Nat → V)
    (a c y x : V) :
    Sat mem (scons x (scons y (scons c (scons a env)))) (rename supportRename phi) ↔
      MatrixRelation mem phi env x y :=
  Sat_rename_ext phi supportRename _ _ (support_env a c y x env)

/-- The actual antecedent is exactly the shallow local bound on this matrix. -/
theorem sat_subsetBoundForm (mem : V → V → Prop) (phi : Form) (env : Nat → V) :
    Sat mem env (subsetBoundForm phi) ↔
      PositiveClosure.SubsetBounded mem (MatrixRelation mem phi env) :=
  forall_congr' fun x => exists_congr fun b => forall_congr' fun y =>
    imp_congr (sat_bound_matrix mem phi env x b y) (sat_subsetForm mem _ 0 1)

/-- No arbitrary semantic relation is substituted: this is the given Form's relation. -/
theorem sat_positiveBodyForm (mem : V → V → Prop) (phi : Form) (env : Nat → V) :
    Sat mem env (positiveBodyForm phi) ↔
      ∀ a, ∃ c, PositiveClosure.PositiveHull mem (PositiveClosure.Sub mem) (MatrixRelation mem phi env) a c := by
  constructor
  · intro h a
    obtain ⟨c, hClosed, hSupport⟩ := h a
    refine ⟨c, fun x y hActive hxy => ?_, fun y hy => ?_⟩
    · have hStart : Sat mem (scons y (scons x (scons c (scons a env))))
          (subsetForm 1 3) ∨ mem x c := by
        rcases hActive with hSub | hMem
        · exact Or.inl ((sat_subsetForm mem _ 1 3).mpr hSub)
        · exact Or.inr hMem
      exact hClosed x y ⟨hStart, (sat_forward_matrix mem phi env a c x y).mpr hxy⟩
    · obtain ⟨x, hxy⟩ := hSupport y hy
      exact ⟨x, (sat_support_matrix mem phi env a c y x).mp hxy⟩
  · intro h a
    obtain ⟨c, hClosed, hSupport⟩ := h a
    refine ⟨c, fun x y hxy => ?_, fun y hy => ?_⟩
    · have hActive : PositiveClosure.Sub mem x a ∨ mem x c := by
        rcases hxy.1 with hSub | hMem
        · exact Or.inl ((sat_subsetForm mem _ 1 3).mp hSub)
        · exact Or.inr hMem
      exact hClosed x y hActive ((sat_forward_matrix mem phi env a c x y).mp hxy.2)
    · obtain ⟨x, hxy⟩ := hSupport y hy
      exact ⟨x, (sat_support_matrix mem phi env a c y x).mpr hxy⟩

/-- The concrete first-order wrapper has exactly the intended closure semantics. -/
theorem sat_pscForm (mem : V → V → Prop) (phi : Form) (env : Nat → V) :
    Sat mem env (pscForm phi) ↔
      PositiveClosure.ClosureInstance mem (PositiveClosure.Sub mem) (MatrixRelation mem phi env) :=
  imp_congr (sat_subsetBoundForm mem phi env) (sat_positiveBodyForm mem phi env)

/-- A syntactic check, independent of the semantics. -/
def EqualityFree : Form → Prop
  | fMem _ _ => True
  | fEq _ _ => False
  | fBot => True
  | fImp a b => EqualityFree a ∧ EqualityFree b
  | fAnd a b => EqualityFree a ∧ EqualityFree b
  | fOr a b => EqualityFree a ∧ EqualityFree b
  | fAll a => EqualityFree a
  | fEx a => EqualityFree a

theorem equalityFree_rename (phi : Form) (r : Nat → Nat)
    (h : EqualityFree phi) : EqualityFree (rename r phi) := by
  induction phi generalizing r with
  | fMem i j | fBot => trivial
  | fEq i j => exact False.elim h
  | fImp a b iha ihb | fAnd a b iha ihb | fOr a b iha ihb => exact ⟨iha r h.1, ihb r h.2⟩
  | fAll a ih | fEx a ih => exact ih (up r) h

theorem equalityFree_subsetForm (i j : Nat) : EqualityFree (subsetForm i j) :=
  ⟨True.intro, True.intro⟩

theorem equalityFree_pscForm (phi : Form) (h : EqualityFree phi) :
    EqualityFree (pscForm phi) :=
  ⟨⟨equalityFree_rename phi boundRename h, equalityFree_subsetForm 0 1⟩,
    ⟨⟨⟨⟨equalityFree_subsetForm 1 3, True.intro⟩, equalityFree_rename phi forwardRename h⟩,
      True.intro⟩, ⟨True.intro, equalityFree_rename phi supportRename h⟩⟩⟩

#print axioms sat_pscForm
#print axioms equalityFree_pscForm

end SetTheory.BusyBeaver.ZFC.DeepPositiveClosure
