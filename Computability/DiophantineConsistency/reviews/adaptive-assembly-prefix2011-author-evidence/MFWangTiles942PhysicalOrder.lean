import DiophantineConsistency.MFWangTiles942PhysicalData
import Mathlib.Data.Finset.Sort

/-! Matrix-free physical-order proof. The ordinary physical-order module
reuses these independently maintained results. -/
/-! Exact binding of the checked physical-order data to the printed floor rank.
Only adjacent numerical inequalities are checked; all pairwise and coverage
conclusions below are proved generically. -/
namespace DiophantineConsistency.MF.WangTiles942PhysicalOrder

open DiophantineConsistency.MF.WangTiles942 DiophantineConsistency.WangTiles942
  DiophantineConsistency.MF.WangTiles942PhysicalData
open scoped BigOperators
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-- The j-th non-Start certificate pair. -/
def row (j : Fin 941) : ℕ × ℕ := rows[j.val]'(by rw [rows_length]; exact j.isLt)

theorem row_good (j : Fin 941) : rowGood (row j) :=
  rows_good _ (List.getElem_mem _)

def abstractIndex (j : Fin 941) : Fin 942 := Fin.ofNat 942 (row j).1
def value (j : Fin 941) : ℕ := (row j).2

theorem abstractIndex_val (j : Fin 941) : (abstractIndex j).val = (row j).1 := by
  exact Nat.mod_eq_of_lt (row_good j).2.1

theorem abstractIndex_ne_zero (j : Fin 941) : abstractIndex j ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  rw [abstractIndex_val] at hv
  have := (row_good j).1
  omega

theorem weight_eq (j : Fin 941) : selectorWeight (tile (abstractIndex j)) = value j :=
  (row_good j).2.2

theorem value_strictAnti : StrictAnti value := by
  apply Fin.strictAnti_iff_succ_lt.mpr
  intro j
  exact (List.isChain_iff_getElem.mp rows_descending) j.val (by rw [rows_length]; omega)

def nonStartIndex (j : Fin 941) : Fin 941 :=
  ⟨(abstractIndex j).val-1, by
    have := (abstractIndex j).isLt
    have := abstractIndex_ne_zero j
    have hp : 0 < (abstractIndex j).val := Fin.pos_iff_ne_zero.mpr this
    omega⟩

theorem nonStartIndex_succ (j : Fin 941) : (nonStartIndex j).succ = abstractIndex j := by
  apply Fin.ext
  have hp := Fin.pos_iff_ne_zero.mpr (abstractIndex_ne_zero j)
  change (abstractIndex j).val-1+1=(abstractIndex j).val
  omega

theorem nonStartWeight_eq (j : Fin 941) : nonStartWeight (nonStartIndex j) = value j := by
  unfold nonStartWeight
  rw [nonStartIndex_succ]
  exact weight_eq j

theorem nonStartIndex_injective : Function.Injective nonStartIndex := by
  intro i j h
  apply value_strictAnti.injective
  rw [← nonStartWeight_eq i, ← nonStartWeight_eq j, h]

theorem nonStartIndex_bijective : Function.Bijective nonStartIndex :=
  ⟨nonStartIndex_injective, Finite.surjective_of_injective nonStartIndex_injective⟩

/-- A strictly increasing self-map of a finite ordinal fixes every point. -/
theorem strictMono_fin_eq_self {n : ℕ} (f : Fin n → Fin n) (hf : StrictMono f)
    (i : Fin n) : f i = i := by
  exact DFunLike.congr_fun
    (OrderHom.eq_id_of_injective (⟨f, hf.monotone⟩ : Fin n →o Fin n) hf.injective) i

def rankMap (j : Fin 941) : Fin 941 :=
  ⟨strictRank nonStartWeight (nonStartIndex j), strictRank_lt_card _ _⟩

theorem rankMap_strictMono : StrictMono rankMap := by
  intro i j hij
  have hw := value_strictAnti hij
  rw [← nonStartWeight_eq j, ← nonStartWeight_eq i] at hw
  exact strictRank_antitone hw

theorem rankMap_eq (j : Fin 941) : rankMap j = j :=
  strictMono_fin_eq_self rankMap rankMap_strictMono j

theorem position_eq (j : Fin 941) : physicalPosition (abstractIndex j) = j.val+1 := by
  rw [← nonStartIndex_succ, physicalPosition_succ]
  have h := congrArg Fin.val (rankMap_eq j)
  change strictRank nonStartWeight (nonStartIndex j)=j.val at h
  omega

/-- Physical position zero is explicitly reserved for Start. -/
def abstractAt (p : Fin 942) : Fin 942 := Fin.cases 0 abstractIndex p

theorem abstractAt_zero : abstractAt 0 = 0 := rfl
theorem abstractAt_succ (j : Fin 941) : abstractAt j.succ = abstractIndex j := rfl

theorem physicalMap_abstractAt (p : Fin 942) : physicalMap (abstractAt p) = p := by
  cases p using Fin.cases with
  | zero => exact physicalMap_zero
  | succ j =>
      apply Fin.ext
      exact position_eq j

theorem abstractAt_physicalMap (i : Fin 942) : abstractAt (physicalMap i) = i :=
  physicalMap_injective (physicalMap_abstractAt (physicalMap i))

theorem abstractAt_bijective : Function.Bijective abstractAt := by
  constructor
  · intro i j h
    have hh := congrArg physicalMap h
    simpa only [physicalMap_abstractAt] using hh
  · intro i
    exact ⟨physicalMap i, abstractAt_physicalMap i⟩

theorem abstractAt_eq_inverse (p : Fin 942) : abstractAt p = physicalEquiv.symm p := by
  apply physicalEquiv.injective
  exact (physicalMap_abstractAt p).trans (physicalEquiv.apply_symm_apply p).symm

theorem full_coverage (i : Fin 942) : ∃ p : Fin 942, abstractAt p = i :=
  abstractAt_bijective.surjective i

/-- The cache coefficients are the actual descending physical weights. -/
theorem value_eq_physicalWeight (j : Fin 941) : value j = physicalWeight j.succ := by
  rw [← weight_eq, ← abstractAt_succ, abstractAt_eq_inverse]
  rfl

def weightAt (p : Fin 942) : ℕ := Fin.cases (selectorWeight start) value p

theorem weight_abstractAt (p : Fin 942) :
    selectorWeight (tile (abstractAt p)) = weightAt p := by
  cases p using Fin.cases with
  | zero => exact congrArg selectorWeight start_zero
  | succ j => exact weight_eq j

noncomputable def enumerationEquiv : Fin 942 ≃ Fin 942 :=
  Equiv.ofBijective abstractAt abstractAt_bijective

/-- A reusable exact reindexing for later modular evaluation of the kernel. -/
theorem selector_sum_reindex {R : Type*} [AddCommMonoid R] (f : ℕ → ℕ → R) :
    (∑ i : Fin 942, f (physicalPosition i) (selectorWeight (tile i))) =
      ∑ p : Fin 942, f p.val (weightAt p) := by
  have he := Equiv.sum_comp enumerationEquiv
    (fun i : Fin 942 => f (physicalPosition i) (selectorWeight (tile i)))
  calc
    _ = ∑ p : Fin 942, f (physicalPosition (abstractAt p))
        (selectorWeight (tile (abstractAt p))) := he.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      have hp := congrArg Fin.val (physicalMap_abstractAt p)
      change physicalPosition (abstractAt p)=p.val at hp
      rw [hp,weight_abstractAt]

end DiophantineConsistency.MF.WangTiles942PhysicalOrder
