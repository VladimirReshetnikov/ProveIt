import GowersSzemeredi.Proofs18PolyCubicDegree
import GowersSzemeredi.Proofs18TheoremOneDegreesSide

/-! Declarations of `Proofs18PolyCubicDegree` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- **Theorem 18.1 from a polynomial envelope** that fits `2^(d+10)`. -/
theorem theorem181At_of_polyEnvBound {d μ : Nat} (h : PolyEnvBound d μ)
    (hμ : μ + 1 ≤ 2 ^ (d + 10)) : Theorem181At d := by
  apply Theorem181At.of_function_discrepancy
  intro alpha ha ha2
  obtain ⟨b, s, T, hB, b0, -, s0, -, bi, si⟩ := h alpha ha ha2
  exact ⟨b, s, T, section18Exponent_le_of_inv_le ha ha2 b0 hμ bi,
    section18Exponent_le_of_inv_le ha ha2 s0 hμ si, hB⟩

/-- **Theorem 18.1 at degree three**, from a polynomial phase partition of
progressions with `K ≤ 2^p` and `p ≤ 2^(2^64)`. -/
theorem theorem_18_1_three_of_phase_partition {K : Real} {p : Nat}
    (hpp : ProgressionPhasePartition K p) (hp : 0 < p) (hK : K ≤ 2 ^ p)
    (hpB : (p : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64)) : Theorem181At 3 := by
  exact theorem181At_of_polyEnvBound
    (polyEnvBound_three_of_phase_partition hpp hp hK hpB) (by norm_num)

end LeanProofs.GowersSzemeredi
