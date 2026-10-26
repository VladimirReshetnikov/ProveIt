import DiophantineConsistency.CurrentControllerUnits2011
import GammaCertificate

/-! Integration sketch. The arithmetic core is compiler checked, but this
adapter has not been rebuilt against the complete pinned repository graph.
It uses only the literal kernel's three already proved residue theorems.
-/

namespace ProofSimplification20261026.RepositoryAdapter

open DiophantineConsistency
open CurrentControllerData2011 CurrentControllerUnits2011

attribute [local irreducible] CurrentKernel2011.K

theorem current_units_reproved (rw n : ℕ) :
    Nat.Coprime (Gamma rw n) (d * dimension n) := by
  have h := gamma_current_from_kernel_residues CurrentKernel2011.K
    CurrentKernelResidues2011.K_cast_47
    CurrentKernelResidues2011.K_cast_2011
    CurrentKernelResidues2011.K_cast_auxiliary rw n
  simpa only [Gamma, q, A, dimension, gammaNatural, d_eq, B_eq,
    CurrentMasks2011.radix, auxiliary] using h

end ProofSimplification20261026.RepositoryAdapter
