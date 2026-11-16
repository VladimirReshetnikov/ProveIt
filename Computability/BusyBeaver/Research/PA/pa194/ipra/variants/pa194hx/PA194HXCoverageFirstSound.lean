import PA194HXCoverageFirst
import PA194HXContractSound
set_option autoImplicit false
namespace PA194HXCoverageFirstSound
open PA194HXCoverageFirst

theorem block_sound (base count i : Nat) (h : blockCheck base count = true)
    (lo : base ≤ i) (hi : i < base+count) : PA194HXContracts.checkAt i = true := by
  have hh := List.all_eq_true.mp h (i-base) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le lo] using hh

theorem allFirst (i : Nat) (hi : i < 32) : PA194HXContracts.checkAt i = true := by
  by_cases h0 : i < 8
  · exact block_sound 0 8 i block0 (by omega) h0
  by_cases h8 : i < 16
  · exact block_sound 8 8 i block8 (by omega) h8
  by_cases h16 : i < 24
  · exact block_sound 16 8 i block16 (by omega) h16
  exact block_sound 24 8 i block24 (by omega) (by omega)

theorem contractsFirst (i : Nat) (hi : i < 32) :
    ∃ code, M6.Source.resolveAt PA194SourceProgram.sites i = some code ∧
      PA194HXContractSound.Contracts i code :=
  PA194HXContractSound.atSite i (allFirst i hi)

#print axioms allFirst
#print axioms contractsFirst
end PA194HXCoverageFirstSound
