import IPRADerivations.Foundations.FiniteFiberGrouping
import IPRADerivations.Analysis.RationalArithmetic.Representations.GaussianRationalValueEquality
import IPRADerivations.Core.CongruenceTactic

/-!
# Grouping original point positions by their exact Gaussian-rational x value

Source05 requires finite groups by abscissa while retaining all ordinates.
The key reader canonically recodes the x projection of an actual point-list
entry. Equal field values with different raw rational encodings therefore
have the same group. All original positions are retained. This adapter does
not assert curve evaluation, ordinate distinctness, norm multiplicity or the
final zero-count theorem; those require their own source hypotheses/proofs.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalFiberGrouping

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open LeanProofs.IPRA.Analysis.GaussianTranslatedNonconstant (recode subst_recode recode_canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalValueEquality (valueEqual recode_equal_iff)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def abscissa (L i : PTm n) : PTm n := fstT (entry L i)
def ordinate (L i : PTm n) : PTm n := sndT (entry L i)
def xKeyF : PR 2 := PTm.toPR (recode (fstT (var 0)) : PTm 2)
abbrev groupCount (L p : PTm n) : PTm n := Foundations.FiniteFiberGrouping.groupCount xKeyF L p
abbrev representatives (L p : PTm n) : PTm n := Foundations.FiniteFiberGrouping.representatives xKeyF L p
abbrev representative (L p g : PTm n) : PTm n := Foundations.FiniteFiberGrouping.representative xKeyF L p g
abbrev fiber (L p g : PTm n) : PTm n := Foundations.FiniteFiberGrouping.fiber xKeyF L p g
abbrev fiberCount (L p g : PTm n) : PTm n := Foundations.FiniteFiberGrouping.fiberCount xKeyF L p g
abbrev groupOf (L p i : PTm n) : PTm n := Foundations.FiniteFiberGrouping.groupOf xKeyF L p i
abbrev slotOf (L p i : PTm n) : PTm n := Foundations.FiniteFiberGrouping.slotOf xKeyF L p i
abbrev partitionTotal (L p : PTm n) : PTm n := Foundations.FiniteFiberGrouping.partitionTotal xKeyF L p
def outputF : PR 2 := Foundations.FiniteFiberGrouping.outputF xKeyF
def run (L p : PTm n) : PTm n := ap2 outputF L p

@[simp] theorem subst_abscissa {m : ℕ} (σ : Fin n → PTm m) (L i : PTm n) :
    Syn.subst σ (abscissa L i) = abscissa (Syn.subst σ L) (Syn.subst σ i) := by simp [abscissa]
@[simp] theorem subst_ordinate {m : ℕ} (σ : Fin n → PTm m) (L i : PTm n) :
    Syn.subst σ (ordinate L i) = ordinate (Syn.subst σ L) (Syn.subst σ i) := by simp [ordinate]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (L p : PTm n) :
    Syn.subst σ (run L p) = run (Syn.subst σ L) (Syn.subst σ p) := by simp [run]
theorem recode_congr {q r : PTm n} (h : Γ ⊢[PRAAx] q ≐ r) : Γ ⊢[PRAAx] recode q ≐ recode r := by
  ipra_congr (recode (var 0) : PTm 1) with [h]
theorem reader_at (point p : PTm n) : Γ ⊢[PRAAx] ap2 xKeyF point p ≐ recode (fstT point) := by
  simpa [xKeyF,ap2] using toPR_eq (Γ := Γ) (recode (fstT (var 0)) : PTm 2) ![point,p]
theorem pair_reader_at (x y p : PTm n) : Γ ⊢[PRAAx] ap2 xKeyF (pairT x y) p ≐ recode x :=
  (reader_at _ p).eqTrans (recode_congr (fst_pair x y))
theorem key_at (L p i : PTm n) : Γ ⊢[PRAAx]
    Foundations.FiniteFiberGrouping.key xKeyF L p i ≐ recode (abscissa L i) := reader_at _ _
theorem key_canonical (L p i : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (Foundations.FiniteFiberGrouping.key xKeyF L p i) :=
  GaussianRationalHorner.canonical_congr (key_at L p i) (recode_canonical _)
theorem same_abscissa_group (L p i j : PTm n)
    (hi : Γ ⊢[PRAAx] lt i (length L)) (hj : Γ ⊢[PRAAx] lt j (length L)) : Γ ⊢[PRAAx]
    Fm.iff (valueEqual (abscissa L i) (abscissa L j)) (groupOf L p i ≐ groupOf L p j) := by
  refine .andI (.impI ?_) (.impI ?_)
  · have keys : valueEqual (abscissa L i) (abscissa L j) :: Γ ⊢[PRAAx]
        Foundations.FiniteFiberGrouping.key xKeyF L p i ≐ Foundations.FiniteFiberGrouping.key xKeyF L p j :=
      (key_at L p i).wk.eqTrans
      (((recode_equal_iff (abscissa L i) (abscissa L j)).wk.iffMpr Prf.hyp0).eqTrans (key_at L p j).wk.eqSymm)
    exact (Foundations.FiniteFiberGrouping.same_key_group xKeyF L p i j hi hj).wk.iffMp keys
  · apply (recode_equal_iff (abscissa L i) (abscissa L j)).wk.iffMp
    exact (key_at L p i).wk.eqSymm.eqTrans
      (((Foundations.FiniteFiberGrouping.same_key_group xKeyF L p i j hi hj).wk.iffMpr Prf.hyp0).eqTrans (key_at L p j).wk)
theorem member_abscissa (L p g r : PTm n) (hr : Γ ⊢[PRAAx] lt r (fiberCount L p g)) : Γ ⊢[PRAAx]
    valueEqual (abscissa L (entry (fiber L p g) r)) (abscissa L (representative L p g)) := by
  apply (recode_equal_iff _ _).iffMp
  exact (key_at L p _).eqSymm.eqTrans
    ((Foundations.FiniteFiberGrouping.fiber_key xKeyF L p g r hr).eqTrans (key_at L p _))
theorem distinct_group_abscissae (L p g h : PTm n)
    (hg : Γ ⊢[PRAAx] lt g (groupCount L p)) (hh : Γ ⊢[PRAAx] lt h (groupCount L p))
    (hneq : Γ ⊢[PRAAx] neg (g ≐ h)) : Γ ⊢[PRAAx]
    neg (valueEqual (abscissa L (representative L p g)) (abscissa L (representative L p h))) := by
  refine .impI (.impE hneq.wk ?_)
  have eq : valueEqual (abscissa L (representative L p g)) (abscissa L (representative L p h)) :: Γ ⊢[PRAAx]
      recode (abscissa L (representative L p g)) ≐ recode (abscissa L (representative L p h)) :=
    (recode_equal_iff _ _).wk.iffMpr Prf.hyp0
  exact Foundations.FiniteFiberGrouping.unique_group xKeyF L p g h hg.wk hh.wk
    ((key_at L p _).wk.eqTrans (eq.eqTrans (key_at L p _).wk.eqSymm))
theorem coverage (L p i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length L)) : Γ ⊢[PRAAx]
    lt (groupOf L p i) (groupCount L p) ⋏
      (lt (slotOf L p i) (fiberCount L p (groupOf L p i)) ⋏
        (entry (fiber L p (groupOf L p i)) (slotOf L p i) ≐ i)) :=
  Foundations.FiniteFiberGrouping.coverage xKeyF L p i hi
theorem cardinal_partition (L p : PTm n) : Γ ⊢[PRAAx] partitionTotal L p ≐ length L :=
  Foundations.FiniteFiberGrouping.cardinal_partition xKeyF L p
theorem fiber_nonempty (L p g : PTm n) (hg : Γ ⊢[PRAAx] lt g (groupCount L p)) : Γ ⊢[PRAAx]
    le one (fiberCount L p g) := Foundations.FiniteFiberGrouping.fiber_nonempty xKeyF L p g hg
theorem returned_representatives (L p : PTm n) : Γ ⊢[PRAAx] fstT (run L p) ≐ representatives L p :=
  Foundations.FiniteFiberGrouping.returned_representatives xKeyF L p
theorem returned_fiber (L p g : PTm n) (hg : Γ ⊢[PRAAx] lt g (groupCount L p)) : Γ ⊢[PRAAx]
    entry (fstT (sndT (run L p))) g ≐ fiber L p g := Foundations.FiniteFiberGrouping.returned_fiber_lookup xKeyF L p g hg
theorem returned_size (L p g : PTm n) (hg : Γ ⊢[PRAAx] lt g (groupCount L p)) : Γ ⊢[PRAAx]
    entry (fstT (sndT (sndT (run L p)))) g ≐ length (fiber L p g) :=
  Foundations.FiniteFiberGrouping.returned_size_lookup xKeyF L p g hg
theorem returned_total (L p : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (run L p))) ≐ partitionTotal L p := Foundations.FiniteFiberGrouping.returned_total xKeyF L p
theorem returned_cardinal_partition (L p : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (run L p))) ≐ length L := Foundations.FiniteFiberGrouping.returned_cardinal_partition xKeyF L p

theorem gaussian_x_reader_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap2 xKeyF (pairT (var 0) (var 1)) (var 2) ≐ recode (var 0)) := closeUniv 3 (pair_reader_at _ _ _)
theorem gaussian_abscissa_group_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 2) (length (var 0)) ⟶ lt (var 3) (length (var 0)) ⟶
      Fm.iff (valueEqual (abscissa (var 0) (var 2)) (abscissa (var 0) (var 3)))
        (groupOf (var 0) (var 1) (var 2) ≐ groupOf (var 0) (var 1) (var 3))) :=
  closeUniv 4 (.impI (.impI (same_abscissa_group _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem gaussian_fiber_abscissa_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (fiberCount (var 0) (var 1) (var 2)) ⟶
      valueEqual (abscissa (var 0) (entry (fiber (var 0) (var 1) (var 2)) (var 3)))
        (abscissa (var 0) (representative (var 0) (var 1) (var 2)))) :=
  closeUniv 4 (.impI (member_abscissa _ _ _ _ Prf.hyp0))
theorem gaussian_grouping_partition_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((partitionTotal (var 0) (var 1) ≐ length (var 0)) ⋏
      (sndT (sndT (sndT (run (var 0) (var 1)))) ≐ length (var 0))) :=
  closeUniv 2 (.andI (cardinal_partition _ _) (returned_cardinal_partition _ _))
theorem gaussian_grouping_returned_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (groupCount (var 0) (var 1)) ⟶
      ((entry (fstT (sndT (run (var 0) (var 1)))) (var 2) ≐ fiber (var 0) (var 1) (var 2)) ⋏
        (entry (fstT (sndT (sndT (run (var 0) (var 1))))) (var 2) ≐ length (fiber (var 0) (var 1) (var 2))))) :=
  closeUniv 3 (.impI (.andI (returned_fiber _ _ _ Prf.hyp0) (returned_size _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRationalFiberGrouping
