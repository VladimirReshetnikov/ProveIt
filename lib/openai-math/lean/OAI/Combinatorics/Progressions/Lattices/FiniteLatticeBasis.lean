import Mathlib.Algebra.Module.ZLattice.Basic

namespace OAI

section

namespace Erdos3

noncomputable def finiteLatticeBasis {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    Module.Basis (Fin (Module.finrank ℝ E)) ℤ Λ :=
  (Module.Free.chooseBasis ℤ Λ).reindex (Fintype.equivOfCardEq
    (by rw [← Module.finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ, Fintype.card_fin]))

end Erdos3

end

end OAI
