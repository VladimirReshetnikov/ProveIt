import DiophantineConsistency.WangTiles942Completeness
import DiophantineConsistency.WangTiles942BandMarker

/-!
# Choosing independent power dimensions for the actual marked word

The controller needs width and height to be large powers of its auxiliary
prime. Geometry only needs a base greater than one. This construction
retains unique Start for the same actual quotient word; it proves no
power-orbit, rank-controller or arithmetic-solution assertion.
-/

namespace DiophantineConsistency.WangTiles942PowerDimensions

open SetTheory.BusyBeaver.ZFC WangTiles942Periodic WangTiles942BandMarker

set_option Elab.async false
set_option maxRecDepth 10000

/-- Independent cofinal dimensions with unique Start, using the actual
canonical word rather than adding uniqueness as an assumption. -/
theorem cofinal_unique_marked_word (T w H : ℕ)
    (hh : (DecimalMachine215.machine.run T).state = none)
    (hw : 2*T+4 ≤ w) (hTH : T+2 ≤ H) (hH : 3 ≤ H) :
    letI : NeZero (w*H) := ⟨Nat.ne_of_gt (Nat.mul_pos (by omega) (by omega))⟩
    ∃ a : ZMod (w*H) → Fin 942,
      MarkedWord (w*H) (w : ℤ) a ∧ (∀ z, a z = 0 ↔ z = 0) := by
  letI : NeZero H := ⟨by omega⟩
  letI : NeZero (w*H) := ⟨Nat.ne_of_gt (Nat.mul_pos (by omega) (by omega))⟩
  obtain ⟨hwidth,hright⟩ := WangTiles942Completeness.width_split T w hw
  generalize w-(T+2) = R at hwidth hright
  subst w
  have hp := canonical_unique_word_of_halt T (T+2) R H
    hh (Nat.le_refl _) hright hTH hH
  exact ⟨canonicalWord T (T+2) R H hh hTH (by omega),hp.1,hp.2.1⟩

/-- Explicit positive exponents suffice for independently prescribed lower
bounds on width and height. No primality or coprimality is required. -/
theorem exists_power_dimensions (p : ℕ) (hp : 1 < p) (T wBound hBound : ℕ) :
    ∃ rw rh : ℕ, 0 < rw ∧ 0 < rh ∧
      2*T+4 ≤ p^rw ∧ T+2 ≤ p^rh ∧ 3 ≤ p^rh ∧
      wBound < p^rw ∧ hBound < p^rh := by
  refine ⟨2*T+wBound+5,T+hBound+5,by omega,by omega,?_⟩
  have hw : 2*T+wBound+5 < p^(2*T+wBound+5) := Nat.lt_pow_self hp
  have hh : T+hBound+5 < p^(T+hBound+5) := Nat.lt_pow_self hp
  omega

/-- A halt constructs a uniquely marked word at power width and height,
with independent arbitrary lower bounds and exact power-product modulus. -/
theorem exists_power_marked_word (p : ℕ) (hp : 1 < p) (T wBound hBound : ℕ)
    (hh : (DecimalMachine215.machine.run T).state = none) :
    ∃ rw rh : ℕ, 0 < rw ∧ 0 < rh ∧ wBound < p^rw ∧ hBound < p^rh ∧
      p^rw*p^rh = p^(rw+rh) ∧
      letI : NeZero (p^rw*p^rh) := ⟨Nat.mul_ne_zero
        (pow_ne_zero _ (by omega)) (pow_ne_zero _ (by omega))⟩
      ∃ a : ZMod (p^rw*p^rh) → Fin 942,
        MarkedWord (p^rw*p^rh) ((p^rw : ℕ) : ℤ) a ∧
        (∀ z, a z = 0 ↔ z = 0) := by
  obtain ⟨rw,rh,hrw,hrh,hw,hTH,hH,hwb,hhb⟩ :=
    exists_power_dimensions p hp T wBound hBound
  refine ⟨rw,rh,hrw,hrh,hwb,hhb,(pow_add p rw rh).symm,?_⟩
  exact cofinal_unique_marked_word T (p^rw) (p^rh) hh hw hTH hH

end DiophantineConsistency.WangTiles942PowerDimensions
