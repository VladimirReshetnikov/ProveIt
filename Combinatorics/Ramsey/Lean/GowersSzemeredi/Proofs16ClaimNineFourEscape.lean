import GowersSzemeredi.Proofs16SpectrumPairSumset
import GowersSzemeredi.Proofs16BoundedSpanPhase

/-! The escape step of Milićević's Claim 9.4 (arXiv:2601.01682, printed
p. 66): a failed containment produces an escaping frequency.

Write `S = ⟨θ₁, …, θ_s⟩_{±1}` for the `{-1,0,1}`-span of the current values
(`boundedFrequencySpan θ 1`). For `sη ≤ 1/4`, the triangle inequality gives
`B(θ; η) ⊆ B(S; 1/4)` (`boundedFrequencySpan_phase_bound`). If the two
bounded spans `⟨K⟩, ⟨L⟩` of Theorem 27 lay inside `S`, then
`B(θ; η) ⊆ B(⟨K⟩ ∩ ⟨L⟩; 1/4) ⊆ B(K; ρ) + B(L; σ)`
(`bohr_sum_contains_span_intersection_quarter`).
* `escape_frequency`: if some `d ∈ B(θ; η)` is *not* in
  `B(K; ρ) + B(L; σ)`, then a frequency of `⟨K⟩ ∩ ⟨L⟩` escapes `S`.

With `K = Γ_{x+a} ∪ Γ_x` and `L = Γ_{y+a} ∪ Γ_y`, the escaping frequency
splits as `ξ₀ − ξ₁ = ξ₂ − ξ₃`, the input of `claim_9_4_core`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- **A failed containment gives an escaping frequency.** -/
theorem escape_frequency {N : Nat} [NeZero N] [Fact N.Prime]
    (K L : Finset (ZMod N)) {rho sigma : Real}
    (hrho : 0 < rho) (hrho1 : rho < 1) (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (hNK : 8 * (K.card + 1 : Real) / (2 * bohrSumThreshold K L rho sigma) ≤ (N : Real))
    (hNL : 8 * (L.card + 1 : Real) / (2 * bohrSumThreshold K L rho sigma) ≤ (N : Real))
    {s : Nat} (θ : Fin s → ZMod N) {η : Real} (hη : (s : Real) * η ≤ 1 / 4)
    {d : ZMod N} (hd : ∀ i, (centeredAbs (θ i * d) : Real) ≤ η * N)
    (hnot : ¬ ∃ x ∈ bohr K rho, ∃ y ∈ bohr L sigma, d = x + y) :
    ∃ ξ ∈ boundedFrequencySpan (fun k : K => (k : ZMod N))
          (polynomialSpectrumCutoff K.card (rho / 2) (2 * bohrSumThreshold K L rho sigma)) ∩
        boundedFrequencySpan (fun l : L => (l : ZMod N))
          (polynomialSpectrumCutoff L.card (sigma / 2) (2 * bohrSumThreshold K L rho sigma)),
      ξ ∉ boundedFrequencySpan θ 1 := by
  by_contra hall
  push Not at hall
  apply hnot
  apply bohr_sum_contains_span_intersection_quarter K L hrho hrho1 hsigma hsigma1 hNK hNL d
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun ξ hξ => ?_⟩
  have hb := boundedFrequencySpan_phase_bound θ 1 d hd (hall ξ hξ)
  have hN : (0 : Real) ≤ N := by positivity
  rw [Fintype.card_fin] at hb
  calc (centeredAbs (ξ * d) : Real) ≤ (s : Real) * (1 : Nat) * η * N := hb
    _ = ((s : Real) * η) * N := by push_cast; ring
    _ ≤ 1 / 4 * N := mul_le_mul_of_nonneg_right hη hN

end LeanProofs.GowersSzemeredi
