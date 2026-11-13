import BusyBeaver.ZFC.ProfileSyntax

/-!
The actual equality-free CP/GIC model and its first collection instances.

The schema ranges only over equality-free `SetTheory.Form` matrices and their
parameter environments. This file exhibits the particular matrices used for
empty sets, profile pairs, diagonal codes and reversed codes, connecting those
semantic lemmas to literal first-order instances. No profile congruence or
actual-equality axiom is assumed. The full interpretation remains unfinished.
-/

namespace SetTheory.BusyBeaver.ZFC.ProfileModel

open Form Profile ProfilePairs ProfileCollection ProfileSyntax DeepPositiveClosure

universe u
variable {V : Type u}

def containerForm : Form :=
  fAll (fEx (fAnd (fMem 1 0)
    (fAll (fImp (fMem 0 1) (fAnd (subsetForm 0 1)
      (fEx (fAnd (fMem 0 2)
        (fAll (fImp (subsetForm 0 2) (fMem 0 1))))))))))

def ModelsGIC (mem : V → V → Prop) : Prop :=
  ∀ phi, EqualityFree phi → ∀ env, Sat mem env (gicForm phi)

def ModelsCPGIC (mem : V → V → Prop) : Prop :=
  (∀ env, Sat mem env containerForm) ∧ ModelsGIC mem

theorem sat_containerForm (mem : V → V → Prop) (env : Nat → V) :
    Sat mem env containerForm ↔ Containers mem := by
  constructor
  · intro h a
    obtain ⟨v, hav, hClosure⟩ := h a
    refine ⟨v, hav, fun x hx => (sat_subsetForm mem _ 0 1).mp (hClosure x hx).1, fun x hx => ?_⟩
    obtain ⟨p, hpv, hBound⟩ := (hClosure x hx).2
    exact ⟨p, hpv, fun z hz => hBound z ((sat_subsetForm mem _ 0 2).mpr hz)⟩
  · intro h a
    obtain ⟨v, hav, hTrans, hPower⟩ := h a
    refine ⟨v, hav, fun x hx => ?_⟩
    obtain ⟨p, hpv, hBound⟩ := hPower x hx
    exact ⟨(sat_subsetForm mem _ 0 1).mpr (hTrans x hx), p, hpv,
      fun z hz => hBound z ((sat_subsetForm mem _ 0 2).mp hz)⟩

theorem equalityFree_containerForm : EqualityFree containerForm :=
  ⟨True.intro, ⟨True.intro, ⟨equalityFree_subsetForm 0 1,
    ⟨True.intro, ⟨equalityFree_subsetForm 0 2, True.intro⟩⟩⟩⟩⟩

theorem collectionInstance_congr (mem : V → V → Prop) (r s : V → V → Prop)
    (h : ∀ x y, r x y ↔ s x y) (hr : CollectionInstance mem r) :
    CollectionInstance mem s := by
  intro a
  obtain ⟨b, hSupport, hCover⟩ := hr a
  exact ⟨b, fun y hy => (hSupport y hy).imp fun x => (h x y).mp, fun x hx ⟨y, hxy⟩ =>
    (hCover x hx ⟨y, (h x y).mpr hxy⟩).imp fun z hz => ⟨hz.1, (h x z).mp hz.2⟩⟩

/-- Transfer only the supplied, equality-free definable relation instance. -/
theorem instance_of_matrix (mem : V → V → Prop) (hModel : ModelsGIC mem)
    (phi : Form) (hFree : EqualityFree phi) (env : Nat → V) (r : V → V → Prop)
    (hRep : ∀ x y, MatrixRelation mem phi env x y ↔ r x y) :
    CollectionInstance mem r :=
  collectionInstance_congr mem _ r hRep
    ((sat_gicForm mem phi env).mp (hModel phi hFree env))

theorem false_instance (mem : V → V → Prop) (witness : V) (hModel : ModelsGIC mem) :
    CollectionInstance mem (fun _ _ => False) :=
  instance_of_matrix mem hModel fBot True.intro (fun _ => witness) _
    (fun _ _ => Iff.rfl)

def pairChoiceForm : Form :=
  fOr (fAnd (sameForm 0 2) (sameForm 1 4))
    (fAnd (sameForm 0 3) (sameForm 1 5))

theorem equalityFree_pairChoiceForm : EqualityFree pairChoiceForm :=
  ⟨⟨equalityFree_sameForm 0 2, equalityFree_sameForm 1 4⟩,
    ⟨equalityFree_sameForm 0 3, equalityFree_sameForm 1 5⟩⟩

theorem pairChoice_instance (mem : V → V → Prop) (hModel : ModelsGIC mem) (i j a b : V) :
    CollectionInstance mem (PairChoice mem i j a b) :=
  instance_of_matrix mem hModel pairChoiceForm equalityFree_pairChoiceForm
    (scons i (scons j (scons a (fun _ => b)))) _ fun _ _ => or_congr
      (and_congr (sat_sameForm mem _ 0 2) (sat_sameForm mem _ 1 4))
      (and_congr (sat_sameForm mem _ 0 3) (sat_sameForm mem _ 1 5))

def diagonalChoiceForm : Form :=
  fAnd (fMem 0 2) (orderedPairForm 0 0 1)

theorem equalityFree_diagonalChoiceForm : EqualityFree diagonalChoiceForm :=
  ⟨True.intro, equalityFree_orderedPairForm 0 0 1⟩

theorem diagonal_instance (mem : V → V → Prop) (hModel : ModelsGIC mem) (domain : V) :
    CollectionInstance mem (DiagonalChoice mem domain) :=
  instance_of_matrix mem hModel diagonalChoiceForm equalityFree_diagonalChoiceForm
    (fun _ => domain) _ fun _ _ => and_congr Iff.rfl (sat_orderedPairForm mem _ 0 0 1)

def reverseChoiceForm : Form :=
  fAnd (fMem 0 2) (fEx (fEx (fAnd
    (orderedPairForm 1 0 2) (orderedPairForm 0 1 3))))

theorem equalityFree_reverseChoiceForm : EqualityFree reverseChoiceForm :=
  ⟨True.intro, ⟨equalityFree_orderedPairForm 1 0 2,
    equalityFree_orderedPairForm 0 1 3⟩⟩

theorem reverse_instance (mem : V → V → Prop) (hModel : ModelsGIC mem) (r : V) :
    CollectionInstance mem (ReverseChoice mem r) :=
  instance_of_matrix mem hModel reverseChoiceForm equalityFree_reverseChoiceForm
    (fun _ => r) _ fun _ _ =>
      ⟨fun ⟨hd, x, y, hxy, hyx⟩ => ⟨hd, x, y, (sat_orderedPairForm mem _ 1 0 2).mp hxy,
        (sat_orderedPairForm mem _ 0 1 3).mp hyx⟩,
      fun ⟨hd, x, y, hxy, hyx⟩ => ⟨hd, x, y, (sat_orderedPairForm mem _ 1 0 2).mpr hxy,
        (sat_orderedPairForm mem _ 0 1 3).mpr hyx⟩⟩

/-- Actual first-order CP/GIC instances give the profile-pair resource. -/
theorem pairs_of_model (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem) :
    ∀ a b, ∃ p, Pair mem p a b :=
  pairs_of_instances mem witness
    ((sat_containerForm mem (fun _ => witness)).mp (h.1 _))
    (false_instance mem witness h.2) (pairChoice_instance mem h.2)

theorem orderedPairs_of_model (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem) :
    ∀ a b, ∃ c, OrderedPair mem a b c :=
  orderedPairs_of_pairs mem (pairs_of_model mem witness h)

theorem eqv_refl_of_model (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem) :
    ∀ a, Eqv mem a a := by
  intro a
  obtain ⟨domain, ha, hTrans, _⟩ :=
    ((sat_containerForm mem (fun _ => witness)).mp (h.1 _)) a
  exact bisim_refl_of_collection mem a domain ha hTrans
    (orderedPairs_of_model mem witness h) (diagonal_instance mem h.2 domain)

theorem eqv_symm_of_model (mem : V → V → Prop) (witness : V) (h : ModelsCPGIC mem)
    {x y : V} (hxy : Eqv mem x y) : Eqv mem y x :=
  eqv_symm_of_instances mem (orderedPairs_of_model mem witness h)
    (reverse_instance mem h.2) hxy

#print axioms pairs_of_model
#print axioms eqv_refl_of_model
#print axioms eqv_symm_of_model

end SetTheory.BusyBeaver.ZFC.ProfileModel
