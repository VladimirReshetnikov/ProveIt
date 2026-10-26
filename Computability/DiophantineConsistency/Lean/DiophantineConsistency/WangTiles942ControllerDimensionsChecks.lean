import DiophantineConsistency.WangTiles942ControllerDimensions

namespace DiophantineConsistency.WangTiles942ControllerDimensionsChecks

open WangTiles942ControllerDimensions WangTiles942Periodic CurrentControllerData2011
set_option Elab.async false

-- Transport retains the supplied word, including its index-zero origin.
example {M N : ℕ} [NeZero M] [NeZero N] (h : M = N) (s : ℤ)
    (a : ZMod M → Fin 942) (ha : MarkedWord M s a)
    (hu : ∀ z, a z = 0 ↔ z = 0) :
    MarkedWord N s (transportWord h a) ∧
      (∀ z, transportWord h a z = 0 ↔ z = 0) :=
  transport_marked_unique h s a ha hu

example {N : ℕ} (a : ZMod N → Fin 942) : transportWord rfl a = a := rfl

example : 3 ≤ (3 : ℕ) := height_exponent_ge_three (by decide : 1 < 4) (by decide)
example : ¬ (4^2 < (4 : ℕ)^2) := by decide

-- The lower allowed exponent pair is a useful arithmetic boundary case;
-- this does not assert a machine halt or marked word for that pair.
example : (1+3-1)+1 = 1+3 ∧ 1 < 1+3-1 ∧ 2 ≤ 1+3-1 ∧
    d*auxiliary < auxiliary^(1+3-1) := controller_exponents (by decide) (by decide)

-- Full cofinality, actual word, and uniqueness remain conditional only
-- on the literal machine's halting time.
example (T wBound hBound : ℕ)
    (hh : (DecimalMachine215.machine.run T).state = none) :
    ∃ k rw rh : ℕ, 0 < rw ∧ 3 ≤ rh ∧ k+1 = rw+rh ∧ rw < k ∧
      d*auxiliary < auxiliary^k ∧ wBound < auxiliary^rw ∧
      hBound < auxiliary^rh ∧
      letI : NeZero (auxiliary^(k+1)) := ⟨pow_ne_zero _ (NeZero.ne auxiliary)⟩
      ∃ a : ZMod (auxiliary^(k+1)) → Fin 942,
        MarkedWord (auxiliary^(k+1)) ((auxiliary^rw : ℕ) : ℤ) a ∧
        (∀ z, a z = 0 ↔ z = 0) :=
  exists_controller_dimensions T wBound hBound hh

example (T wBound : ℕ)
    (hh : (DecimalMachine215.machine.run T).state = none) :
    ∃ k rw : ℕ, 0 < rw ∧ rw < k ∧ d*auxiliary < auxiliary^k ∧
      wBound < auxiliary^rw ∧
      letI : NeZero (auxiliary^(k+1)) := ⟨pow_ne_zero _ (NeZero.ne auxiliary)⟩
      ∃ a : ZMod (auxiliary^(k+1)) → Fin 942,
        MarkedWord (auxiliary^(k+1)) ((auxiliary^rw : ℕ) : ℤ) a ∧
        (∀ z, a z = 0 ↔ z = 0) :=
  exists_controller_marked_word T wBound hh

#print axioms transport_marked_unique
#print axioms height_exponent_ge_three
#print axioms controller_exponents
#print axioms exists_controller_dimensions
#print axioms exists_controller_marked_word

end DiophantineConsistency.WangTiles942ControllerDimensionsChecks
