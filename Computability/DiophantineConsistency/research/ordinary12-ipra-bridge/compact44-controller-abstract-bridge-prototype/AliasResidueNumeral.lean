import KernelAliasExplicit

/-! Uncompiled explicit transport from the symbolic modulus abbreviation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactAliasResidueNumeral
open CompactSymbolicKernelResidue CompactSymbolicKernelAliasExplicit

theorem alias_residue_numeral : kernelAlias % 342946332593 = 284898815895 :=
  (congrArg (fun m : ℕ => kernelAlias % m = 284898815895)
    (show Modulus = 342946332593 from rfl)).mp kernelAlias_mod

#print axioms alias_residue_numeral
end CompactAliasResidueNumeral
