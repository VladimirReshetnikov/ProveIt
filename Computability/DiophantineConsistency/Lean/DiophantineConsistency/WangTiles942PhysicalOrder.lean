import DiophantineConsistency.MFWangTiles942PhysicalOrder
import DiophantineConsistency.WangTiles942PhysicalData
import Mathlib.Data.Finset.Sort

/-! Exact binding of the checked physical-order data to the printed floor rank.
Only adjacent numerical inequalities are checked; all pairwise and coverage
conclusions below are proved generically. -/
namespace DiophantineConsistency.WangTiles942PhysicalOrder

open WangTiles942 WangTiles942PhysicalData
open scoped BigOperators
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-- The j-th non-Start certificate pair. -/
def row (j : Fin 941) : ℕ × ℕ := rows[j.val]'(by rw [rows_length]; exact j.isLt)

theorem row_good (j : Fin 941) : rowGood (row j) :=
  MF.WangTiles942PhysicalOrder.row_good j

def abstractIndex (j : Fin 941) : Fin 942 := Fin.ofNat 942 (row j).1
def value (j : Fin 941) : ℕ := (row j).2

theorem abstractIndex_val (j : Fin 941) : (abstractIndex j).val = (row j).1 :=
  MF.WangTiles942PhysicalOrder.abstractIndex_val j

theorem abstractIndex_ne_zero (j : Fin 941) : abstractIndex j ≠ 0 :=
  MF.WangTiles942PhysicalOrder.abstractIndex_ne_zero j

theorem weight_eq (j : Fin 941) : selectorWeight (tile (abstractIndex j)) = value j :=
  MF.WangTiles942PhysicalOrder.weight_eq j

theorem value_strictAnti : StrictAnti value :=
  MF.WangTiles942PhysicalOrder.value_strictAnti

def nonStartIndex (j : Fin 941) : Fin 941 :=
  (abstractIndex j).pred (abstractIndex_ne_zero j)

theorem nonStartIndex_succ (j : Fin 941) : (nonStartIndex j).succ = abstractIndex j :=
  MF.WangTiles942PhysicalOrder.nonStartIndex_succ j

theorem nonStartWeight_eq (j : Fin 941) : nonStartWeight (nonStartIndex j) = value j :=
  MF.WangTiles942PhysicalOrder.nonStartWeight_eq j

theorem nonStartIndex_injective : Function.Injective nonStartIndex :=
  MF.WangTiles942PhysicalOrder.nonStartIndex_injective

theorem nonStartIndex_bijective : Function.Bijective nonStartIndex :=
  MF.WangTiles942PhysicalOrder.nonStartIndex_bijective

/-- A strictly increasing self-map of a finite ordinal fixes every point. -/
theorem strictMono_fin_eq_self {n : ℕ} (f : Fin n → Fin n) (hf : StrictMono f)
    (i : Fin n) : f i = i :=
  MF.WangTiles942PhysicalOrder.strictMono_fin_eq_self f hf i

def rankMap (j : Fin 941) : Fin 941 :=
  ⟨strictRank nonStartWeight (nonStartIndex j), strictRank_lt_card _ _⟩

theorem rankMap_strictMono : StrictMono rankMap :=
  MF.WangTiles942PhysicalOrder.rankMap_strictMono

theorem rankMap_eq (j : Fin 941) : rankMap j = j :=
  MF.WangTiles942PhysicalOrder.rankMap_eq j

theorem position_eq (j : Fin 941) : physicalPosition (abstractIndex j) = j.val+1 :=
  MF.WangTiles942PhysicalOrder.position_eq j

/-- Physical position zero is explicitly reserved for Start. -/
def abstractAt (p : Fin 942) : Fin 942 := Fin.cases 0 abstractIndex p

theorem abstractAt_zero : abstractAt 0 = 0 :=
  MF.WangTiles942PhysicalOrder.abstractAt_zero

theorem abstractAt_succ (j : Fin 941) : abstractAt j.succ = abstractIndex j :=
  MF.WangTiles942PhysicalOrder.abstractAt_succ j

theorem physicalMap_abstractAt (p : Fin 942) : physicalMap (abstractAt p) = p :=
  MF.WangTiles942PhysicalOrder.physicalMap_abstractAt p

theorem abstractAt_physicalMap (i : Fin 942) : abstractAt (physicalMap i) = i :=
  MF.WangTiles942PhysicalOrder.abstractAt_physicalMap i

theorem abstractAt_bijective : Function.Bijective abstractAt :=
  MF.WangTiles942PhysicalOrder.abstractAt_bijective

theorem abstractAt_eq_inverse (p : Fin 942) : abstractAt p = physicalEquiv.symm p :=
  MF.WangTiles942PhysicalOrder.abstractAt_eq_inverse p

theorem full_coverage (i : Fin 942) : ∃ p : Fin 942, abstractAt p = i :=
  MF.WangTiles942PhysicalOrder.full_coverage i

/-- The cache coefficients are the actual descending physical weights. -/
theorem value_eq_physicalWeight (j : Fin 941) : value j = physicalWeight j.succ :=
  MF.WangTiles942PhysicalOrder.value_eq_physicalWeight j

def weightAt (p : Fin 942) : ℕ := Fin.cases (selectorWeight start) value p

theorem weight_abstractAt (p : Fin 942) :
    selectorWeight (tile (abstractAt p)) = weightAt p :=
  MF.WangTiles942PhysicalOrder.weight_abstractAt p

noncomputable def enumerationEquiv : Fin 942 ≃ Fin 942 :=
  Equiv.ofBijective abstractAt abstractAt_bijective

/-- A reusable exact reindexing for later modular evaluation of the kernel. -/
theorem selector_sum_reindex {R : Type*} [AddCommMonoid R] (f : ℕ → ℕ → R) :
    (∑ i : Fin 942, f (physicalPosition i) (selectorWeight (tile i))) =
      ∑ p : Fin 942, f p.val (weightAt p) :=
  MF.WangTiles942PhysicalOrder.selector_sum_reindex f

end DiophantineConsistency.WangTiles942PhysicalOrder
