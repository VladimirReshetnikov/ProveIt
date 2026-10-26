import DiophantineConsistency.ObjectOmegaSemiring
import Mathlib.Order.RelClasses
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Monoid.Defs

/-! # Natural order and subtraction witnesses throughout internal omega -/

namespace DiophantineConsistency.ObjectNaturalOrder
open SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency ObjectArithmetic ObjectMultiplication
open ObjectAdditionLaws ObjectOmegaSemiring

set_option maxRecDepth 16000
universe u
variable {V : Type u} {mem : V → V → Prop}

def LeRel (_H : ZFAxioms mem) (x y : V) : Prop := mem x y ∨ x=y

private def additionBoundStage : Form :=
  fAll (fImp (addForm 0 2 1) (fOr (fMem 2 0) (fEq 2 0)))

private theorem additionBoundStage_spec (H : ZFAxioms mem) (n x : V) (ee : Nat → V) :
    Sat mem (scons n (scons x ee)) additionBoundStage ↔
      ∀ y, AddRel H x n y → LeRel H x y := by
  constructor
  · intro h y hy
    exact h y ((addForm_spec H _ 0 2 1).mpr hy)
  · intro h y hy
    exact h y ((addForm_spec H _ 0 2 1).mp hy)

theorem addRel_le_left (H : ZFAxioms mem) {x n y : V} (hxy : AddRel H x n y) :
    LeRel H x y := by
  let ee : Nat → V := fun _ => vempty H
  have h : ∀ k, mem k (omegaV H) →
      Sat mem (scons k (scons x ee)) additionBoundStage := by
    apply omega_ind H additionBoundStage (scons x ee)
    · apply (additionBoundStage_spec H _ x ee).mpr
      intro a ha
      exact Or.inr (addRel_unique H ha (addRel_zero H hxy.1)).symm
    · intro k hk ih
      apply (additionBoundStage_spec H _ x ee).mpr
      intro a ha
      obtain ⟨b,hb⟩ := addRel_total H hxy.1 hk
      have hle := (additionBoundStage_spec H k x ee).mp ih b hb
      have he : a=vsucc H b := addRel_unique H ha (addRel_succ H hb)
      rw [he]
      exact Or.inl ((vsucc_spec H b x).mpr hle)
  exact (additionBoundStage_spec H n x ee).mp (h n hxy.2.1) y hxy

theorem addRel_le_right (H : ZFAxioms mem) {x n y : V} (hxy : AddRel H x n y) :
    LeRel H n y := addRel_le_left H (addRel_comm H hxy)

private def differenceStage : Form :=
  fAll (fImp (fNatF 0)
    (fImp (fOr (fMem 0 1) (fEq 0 1)) (fEx (addForm 2 1 0))))

private theorem differenceStage_spec (H : ZFAxioms mem) (n : V) (ee : Nat → V) :
    Sat mem (scons n ee) differenceStage ↔
      ∀ x, mem x (omegaV H) → LeRel H x n → ∃ z, AddRel H x z n := by
  constructor
  · intro h x hx hle
    obtain ⟨z,hz⟩ := h x ((fNatF_spec H _ 0).mpr hx) hle
    exact ⟨z,(addForm_spec H _ 2 1 0).mp hz⟩
  · intro h x hx hle
    obtain ⟨z,hz⟩ := h x ((fNatF_spec H _ 0).mp hx) hle
    exact ⟨z,(addForm_spec H _ 2 1 0).mpr hz⟩

theorem leRel_exists_add (H : ZFAxioms mem) {x y : V}
    (hx : mem x (omegaV H)) (hy : mem y (omegaV H)) (hxy : LeRel H x y) :
    ∃ z, AddRel H x z y := by
  let ee : Nat → V := fun _ => vempty H
  have h : ∀ k, mem k (omegaV H) → Sat mem (scons k ee) differenceStage := by
    apply omega_ind H differenceStage ee
    · apply (differenceStage_spec H _ ee).mpr
      intro a ha hle
      rcases hle with hm | he
      · exact False.elim (vempty_spec H a hm)
      · subst a
        exact ⟨vempty H,addRel_zero H (vempty_in_omega H)⟩
    · intro k hk ih
      apply (differenceStage_spec H _ ee).mpr
      intro a ha hle
      rcases hle with hm | he
      · obtain ⟨z,hz⟩ := (differenceStage_spec H k ee).mp ih a ha ((vsucc_spec H k a).mp hm)
        exact ⟨vsucc H z,addRel_succ H hz⟩
      · subst a
        exact ⟨vempty H,addRel_zero H (omega_succ H k hk)⟩
  exact (differenceStage_spec H y ee).mp (h y hy) x hx hxy

theorem leRel_iff_exists_add (H : ZFAxioms mem) {x y : V}
    (hx : mem x (omegaV H)) (hy : mem y (omegaV H)) :
    LeRel H x y ↔ ∃ z, AddRel H x z y :=
  ⟨leRel_exists_add H hx hy,fun ⟨_,h⟩ => addRel_le_left H h⟩

namespace Natural
variable (H : ZFAxioms mem)

noncomputable instance : LinearOrder (ObjectOmegaSemiring.Natural H) := by
  classical
  let r : ObjectOmegaSemiring.Natural H → ObjectOmegaSemiring.Natural H → Prop :=
    fun x y => mem x.val y.val
  letI : IsStrictTotalOrder (ObjectOmegaSemiring.Natural H) r := {
    irrefl := fun x => nat_no_self H x.val x.property
    trans := fun x y z hxy hyz => nat_transitive H z.val z.property y.val hyz x.val hxy
    trichotomous := fun x y hxy hyx =>
      Subtype.ext (((nat_linear H x.val x.property y.val y.property).resolve_left hxy).resolve_right hyx)
  }
  exact linearOrderOfSTO r

/-- Bridge to the unchanged model-level nonstrict relation. -/
theorem le_iff_LeRel (x y : ObjectOmegaSemiring.Natural H) : x≤y ↔ LeRel H x.val y.val := by
  change (x=y ∨ mem x.val y.val) ↔ mem x.val y.val ∨ x.val=y.val
  simp only [Subtype.ext_iff,or_comm]

theorem le_iff_exists_add (x y : ObjectOmegaSemiring.Natural H) :
    x≤y ↔ ∃ z : ObjectOmegaSemiring.Natural H, x+z=y := by
  constructor
  · intro h
    obtain ⟨z,hz⟩ := leRel_exists_add H x.property y.property ((le_iff_LeRel H x y).mp h)
    exact ⟨⟨z,hz.2.1⟩,(ObjectOmegaSemiring.Natural.addRel_iff H x _ y).mp hz⟩
  · rintro ⟨z,hz⟩
    exact (le_iff_LeRel H x y).mpr
      (addRel_le_left H ((ObjectOmegaSemiring.Natural.addRel_iff H x z y).mpr hz))

theorem zero_le (x : ObjectOmegaSemiring.Natural H) : 0≤x :=
  (le_iff_LeRel H 0 x).mpr (vempty_le_nat H x.val x.property)

noncomputable instance : AddCancelCommMonoid (ObjectOmegaSemiring.Natural H) where
  __ := (inferInstance : AddCommMonoid (ObjectOmegaSemiring.Natural H))
  add_left_cancel a b c h := by
    apply Subtype.ext
    have he := congrArg Subtype.val h
    exact ObjectAdditionCancellation.addRel_cancel_left H
      (ObjectOmegaSemiring.Natural.add_graph H a b)
      (he.symm ▸ ObjectOmegaSemiring.Natural.add_graph H a c)

instance : CanonicallyOrderedAdd (ObjectOmegaSemiring.Natural H) where
  exists_add_of_le h := by
    obtain ⟨d,hd⟩ := (le_iff_exists_add H _ _).mp h
    exact ⟨d,hd.symm⟩
  le_add_self a b := (le_iff_LeRel H a (b+a)).mpr
    (addRel_le_right H (ObjectOmegaSemiring.Natural.add_graph H b a))
  le_self_add a b := (le_iff_LeRel H a (a+b)).mpr
    (addRel_le_left H (ObjectOmegaSemiring.Natural.add_graph H a b))

instance : IsOrderedCancelAddMonoid (ObjectOmegaSemiring.Natural H) where
  add_le_add_left a b hab c := by
    obtain ⟨d,hd⟩ := (le_iff_exists_add H a b).mp hab
    apply (le_iff_exists_add H _ _).mpr
    refine ⟨d,?_⟩
    rw [add_assoc,add_comm c d,← add_assoc,hd]
  le_of_add_le_add_left a b c habc := by
    obtain ⟨d,hd⟩ := (le_iff_exists_add H _ _).mp habc
    apply (le_iff_exists_add H b c).mpr
    refine ⟨d,?_⟩
    have he : a+(b+d)=a+c := by simpa only [add_assoc] using hd
    exact add_left_cancel he

end Natural
end DiophantineConsistency.ObjectNaturalOrder
