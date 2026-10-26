import DiophantineConsistency.WangTiles942PowerDimensions
import DiophantineConsistency.CurrentControllerData2011

/-!
# Actual halting words in the controller's dimension convention

The independent power width and height produce the same marked word on
the equal modulus auxiliary^(k+1). The exponent bounds needed by the
finite controller are derived, not supplied. No rank, orbit, dummy
mutation or equation solution is assumed or constructed here.
-/

namespace DiophantineConsistency.WangTiles942ControllerDimensions

open WangTiles942Periodic WangTiles942PowerDimensions CurrentControllerData2011

set_option Elab.async false
set_option maxRecDepth 10000

/-- Dependent transport of the supplied word along an equality of moduli. -/
def transportWord {M N : ℕ} (h : M = N) (a : ZMod M → Fin 942) :
    ZMod N → Fin 942 := h ▸ a

/-- The same word retains its two matching conditions and unique Start.
Both nonzero instances are explicit; equality eliminates their distinction. -/
theorem transport_marked_unique {M N : ℕ} [NeZero M] [NeZero N]
    (h : M = N) (s : ℤ) (a : ZMod M → Fin 942)
    (ha : MarkedWord M s a) (hu : ∀ z, a z = 0 ↔ z = 0) :
    MarkedWord N s (transportWord h a) ∧
      (∀ z, transportWord h a z = 0 ↔ z = 0) := by
  subst N
  exact ⟨ha,hu⟩

theorem height_exponent_ge_three {p rh : ℕ} (hp : 1 < p)
    (hh : p^2 < p^rh) : 3 ≤ rh := by
  by_contra h
  have hle : rh ≤ 2 := by omega
  have hpow := pow_le_pow_right' (by omega : 1 ≤ p) hle
  omega

/-- The product exponent minus one leaves a strict gap above the stride
exponent. Its orbit is larger than the complete fixed controller factor. -/
theorem controller_exponents {rw rh : ℕ} (hrw : 0 < rw) (hrh : 3 ≤ rh) :
    (rw+rh-1)+1 = rw+rh ∧ rw < rw+rh-1 ∧ 2 ≤ rw+rh-1 ∧
      d*auxiliary < auxiliary^(rw+rh-1) := by
  have hk : 2 ≤ rw+rh-1 := by omega
  have hsmall : d*auxiliary < auxiliary^2 := by
    rw [pow_two]
    exact Nat.mul_lt_mul_of_pos_right auxiliary_gt_d (NeZero.pos auxiliary)
  have hpow := pow_le_pow_right' (by decide : 1 ≤ auxiliary) hk
  exact ⟨by omega,by omega,hk,lt_of_lt_of_le hsmall hpow⟩

/-- A literal machine halt supplies all controller-size hypotheses and a
uniquely marked actual word. Width and height remain independently cofinal. -/
theorem exists_controller_dimensions (T wBound hBound : ℕ)
    (hh : (DecimalMachine215.machine.run T).state = none) :
    ∃ k rw rh : ℕ, 0 < rw ∧ 3 ≤ rh ∧ k+1 = rw+rh ∧ rw < k ∧
      d*auxiliary < auxiliary^k ∧ wBound < auxiliary^rw ∧
      hBound < auxiliary^rh ∧
      letI : NeZero (auxiliary^(k+1)) := ⟨pow_ne_zero _ (NeZero.ne auxiliary)⟩
      ∃ a : ZMod (auxiliary^(k+1)) → Fin 942,
        MarkedWord (auxiliary^(k+1)) ((auxiliary^rw : ℕ) : ℤ) a ∧
        (∀ z, a z = 0 ↔ z = 0) := by
  obtain ⟨rw,rh,hrw,_,hwb,hhb,hproduct,hword⟩ :=
    exists_power_marked_word auxiliary (by decide) T wBound
      (max hBound (auxiliary^2)) hh
  have hrh : 3 ≤ rh := height_exponent_ge_three (by decide : 1 < auxiliary)
    (lt_of_le_of_lt (Nat.le_max_right _ _) hhb)
  obtain ⟨hk,hrwk,_,hlarge⟩ := controller_exponents hrw hrh
  have hheight : hBound < auxiliary^rh :=
    lt_of_le_of_lt (Nat.le_max_left _ _) hhb
  letI : NeZero (auxiliary^rw*auxiliary^rh) := ⟨Nat.mul_ne_zero
    (pow_ne_zero _ (NeZero.ne auxiliary)) (pow_ne_zero _ (NeZero.ne auxiliary))⟩
  obtain ⟨a,ha,hu⟩ := hword
  have hmod : auxiliary^rw*auxiliary^rh = auxiliary^((rw+rh-1)+1) :=
    hproduct.trans (congrArg (fun n => auxiliary^n) hk.symm)
  refine ⟨rw+rh-1,rw,rh,hrw,hrh,hk,hrwk,hlarge,hwb,hheight,?_⟩
  letI : NeZero (auxiliary^((rw+rh-1)+1)) :=
    ⟨pow_ne_zero _ (NeZero.ne auxiliary)⟩
  exact ⟨transportWord hmod a,
    transport_marked_unique hmod ((auxiliary^rw : ℕ) : ℤ) a ha hu⟩

/-- The smaller interface directly consumed by a finite safe controller. -/
theorem exists_controller_marked_word (T wBound : ℕ)
    (hh : (DecimalMachine215.machine.run T).state = none) :
    ∃ k rw : ℕ, 0 < rw ∧ rw < k ∧ d*auxiliary < auxiliary^k ∧
      wBound < auxiliary^rw ∧
      letI : NeZero (auxiliary^(k+1)) := ⟨pow_ne_zero _ (NeZero.ne auxiliary)⟩
      ∃ a : ZMod (auxiliary^(k+1)) → Fin 942,
        MarkedWord (auxiliary^(k+1)) ((auxiliary^rw : ℕ) : ℤ) a ∧
        (∀ z, a z = 0 ↔ z = 0) := by
  obtain ⟨k,rw,_,hrw,_,_,hrwk,hlarge,hwb,_,hword⟩ :=
    exists_controller_dimensions T wBound 0 hh
  exact ⟨k,rw,hrw,hrwk,hlarge,hwb,hword⟩

end DiophantineConsistency.WangTiles942ControllerDimensions
