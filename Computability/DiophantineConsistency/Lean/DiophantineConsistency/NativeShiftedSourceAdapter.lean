import DiophantineConsistency.NativeOrdinarySourceConstruction
import DiophantineConsistency.NativeQuadraticParent

/-! Exact old-z/new-z source transfer. The ring identities are unconditional.
The reverse positive map derives old z > 1 from the supplied source itself,
not from a canonical restoration. Only the coordinate numbered3 changes.
The current-port corollaries are external Lean equivalences; no small-front
polynomial transfer or internal HA consistency assertion is made here. -/

namespace DiophantineConsistency.NativeShiftedSourceAdapter

open NativeBinaryScale NativeSourceMask NativeOrdinarySourceConstruction

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

section Ring
variable {R : Type*} [CommRing R]

def toOld (x : Fin 31 → R) : Fin 31 → R := Function.update x 3 (x 3 + 1)
def toNew (x : Fin 31 → R) : Fin 31 → R := Function.update x 3 (x 3 - 1)

theorem toOld_three (x : Fin 31 → R) : toOld x 3 = x 3 + 1 := by
  simp [toOld]

theorem toNew_three (x : Fin 31 → R) : toNew x 3 = x 3 - 1 := by
  simp [toNew]

theorem toOld_other (x : Fin 31 → R) (i : Fin 31) (hi : i ≠ 3) :
    toOld x i = x i := by simp [toOld, hi]

theorem toNew_other (x : Fin 31 → R) (i : Fin 31) (hi : i ≠ 3) :
    toNew x i = x i := by simp [toNew, hi]

theorem toOld_toNew (x : Fin 31 → R) : toOld (toNew x) = x := by
  funext i
  by_cases hi : i = 3
  · subst i; simp [toOld, toNew]
  · simp [toOld, toNew, hi]

theorem toNew_toOld (x : Fin 31 → R) : toNew (toOld x) = x := by
  funext i
  by_cases hi : i = 3
  · subst i; simp [toOld, toNew]
  · simp [toOld, toNew, hi]

/-- All22 literal original-order rows, uniformly in all four ports. -/
theorem rows_toOld (p : Fin 4 → R) (x : Fin 31 → R) (j : Fin 22) :
    SplitCertificate59.sourceRows p (toOld x) j =
      NativeQuadraticParent.sourceRows p x j := by
  fin_cases j <;>
    norm_num [SplitCertificate59.sourceRows, NativeQuadraticParent.sourceRows,
      toOld, Function.update_apply, Fin.ext_iff] <;> ring

theorem rows_toNew (p : Fin 4 → R) (x : Fin 31 → R) (j : Fin 22) :
    NativeQuadraticParent.sourceRows p (toNew x) j =
      SplitCertificate59.sourceRows p x j := by
  rw [← rows_toOld, toOld_toNew]

end Ring

theorem toOld_positive (x : Fin 31 → ℤ) (hx : ∀ i, 0 < x i) :
    ∀ i, 0 < toOld x i := by
  intro i
  by_cases hi : i = 3
  · subst i; rw [toOld_three]; have := hx 3; omega
  · rw [toOld_other x i hi]; exact hx i

theorem toNew_positive (x : Fin 31 → ℤ) (hx : ∀ i, 0 < x i)
    (hz : 1 < x 3) : ∀ i, 0 < toNew x i := by
  intro i
  by_cases hi : i = 3
  · subst i; rw [toNew_three]; omega
  · rw [toNew_other x i hi]; exact hx i

/-- The strict reverse-domain bound is a consequence of every positive old
source under its mask interface. No MC mod4 or canonical-seed premise is used. -/
theorem source_old_z_gt_one (p : Fin 4 → ℤ) {d MC MF : ℕ}
    (hi : Interface p d MC MF) (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ j, SplitCertificate59.sourceRows p (fun i => (x i : ℤ)) j = 0) :
    1 < x 3 := by
  obtain ⟨hC, _, hF, _⟩ := source_gap_bounds p hi.portBox x hx hs
  have hw := ThirteenCarrierComplete.source_spatial_gt_base p hi x hx hs
  have ht := NativeSourceWindow.source_transport_identity p hi.portBox x hx hs
  have hmul : (p 1).toNat + x 10 ≤ ((p 1).toNat + x 10) * gap p x := by
    calc
      (p 1).toNat + x 10 = ((p 1).toNat + x 10) * 1 := by omega
      _ ≤ ((p 1).toNat + x 10) * gap p x := Nat.mul_le_mul_left _ hC
  have hp : 0 < (x 3 - 1) * (sourceQ p x - 1) := by omega
  exact Nat.sub_pos_iff_lt.mp (Nat.pos_of_mul_pos_right hp)

private theorem positive_nat_cast (x : Fin 31 → ℤ) (hx : ∀ i, 0 < x i) :
    ∃ n : Fin 31 → ℕ, (∀ i, 0 < n i) ∧ (fun i => (n i : ℤ)) = x := by
  refine ⟨fun i => (x i).toNat, ?_, ?_⟩
  · intro i; exact Int.pos_iff_toNat_pos.mp (hx i)
  · funext i; exact Int.toNat_of_nonneg (hx i).le

/-- Strict positivity is retained for all31 coordinates, not just a projected
set of free inputs. This uses the literal original-order shifted-z source. -/
def PositiveShiftedSource (p : Fin 4 → ℤ) : Prop :=
  ∃ x : Fin 31 → ℤ, (∀ i, 0 < x i) ∧
    ∀ j, NativeQuadraticParent.sourceRows p x j = 0

theorem shifted_to_old (p : Fin 4 → ℤ) (h : PositiveShiftedSource p) :
    PositiveSource p := by
  obtain ⟨x, hx, hs⟩ := h
  obtain ⟨n, hn, hcast⟩ := positive_nat_cast (toOld x) (toOld_positive x hx)
  refine ⟨n, hn, ?_⟩
  intro j
  rw [hcast, rows_toOld]
  exact hs j

theorem old_to_shifted (p : Fin 4 → ℤ) {d MC MF : ℕ}
    (hi : Interface p d MC MF) (h : PositiveSource p) :
    PositiveShiftedSource p := by
  obtain ⟨n, hn, hs⟩ := h
  have hz : (1 : ℤ) < n 3 := by exact_mod_cast source_old_z_gt_one p hi n hn hs
  refine ⟨toNew (fun i => (n i : ℤ)), toNew_positive _ ?_ hz, ?_⟩
  · intro i; exact_mod_cast hn i
  · intro j; rw [rows_toNew]; exact hs j

theorem positive_shifted_iff_source (p : Fin 4 → ℤ) {d MC MF : ℕ}
    (hi : Interface p d MC MF) : PositiveShiftedSource p ↔ PositiveSource p :=
  ⟨shifted_to_old p, old_to_shifted p hi⟩

def CurrentPositiveShiftedSource : Prop :=
  PositiveShiftedSource (CurrentMasks2011.ports (CurrentKernel2011.K : ℤ))

theorem current_shifted_iff_source :
    CurrentPositiveShiftedSource ↔ CurrentPositiveSource :=
  positive_shifted_iff_source _ CurrentWindowCarry2011.interface

theorem current_shifted_iff_positive_zero : CurrentPositiveShiftedSource ↔
    CurrentCarrierArithmetic2011.PositiveZero CurrentPolynomialWindow2011.polynomial :=
  current_shifted_iff_source.trans current_source_iff_positive_zero

theorem current_shifted_iff_not_conZFC :
    CurrentPositiveShiftedSource ↔ ¬ DiophantineConsistency.ConZFC :=
  current_shifted_iff_source.trans current_source_iff_not_conZFC

theorem no_current_shifted_iff_conZFC :
    (¬ CurrentPositiveShiftedSource) ↔ DiophantineConsistency.ConZFC :=
  (not_congr current_shifted_iff_source).trans no_current_source_iff_conZFC

end DiophantineConsistency.NativeShiftedSourceAdapter
