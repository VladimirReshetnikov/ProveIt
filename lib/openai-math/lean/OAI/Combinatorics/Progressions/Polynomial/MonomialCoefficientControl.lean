import OAI.Combinatorics.Progressions.Linear.KernelJetExtendedControl

namespace OAI

section

namespace Erdos3

theorem normalizedAffineMonomialJetMatrix_eq {α V O N : Type*} [DecidableEq α]
    [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    (root : V → ℤ) (difference : α → V → ℤ) (e : N → V →₀ ℕ) (rows : O → Finset α)
    (T : V → ℝ) {H : ℝ} (hH : H ≠ 0) :
    normalizedIntegerColumns
      (integerJetMatrix (fun n => MvPolynomial.monomial (e n) 1) (integerAffineCube root difference) rows)
      (fun n => H / monomialScale T (e n)) (fun _ => H) =
    realJetMatrix (fun n => MvPolynomial.monomial (e n) 1)
      (realAffineCube (fun v => (root v : ℝ) / T v) (fun i v => (difference i v : ℝ) / T v)) rows := by
  have hv : (fun t v => (integerAffineCube root difference t v : ℝ) / T v) =
      realAffineCube (fun v => (root v : ℝ) / T v) (fun i v => (difference i v : ℝ) / T v) := by
    funext t v
    exact (realAffineCube_normalized_integer root difference T t v).symm
  have he := normalizedIntegerMonomialJetMatrix_eq e (integerAffineCube root difference) rows T hH
  rwa [hv] at he

theorem normalizedAffineMonomialJetMatrix_bound {α V O N : Type*}
    [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    (root : V → ℤ) (difference : α → V → ℤ) (e : N → V →₀ ℕ) (rows : O → Finset α)
    (T : V → ℝ) {h : ℕ} (he : ∀ n, (e n).sum (fun _ d => d) ≤ h)
    (hroot : ∀ v, |(root v : ℝ) / T v| ≤ 1)
    (hdiff : ∀ i v, |(difference i v : ℝ) / T v| ≤ 1) {H : ℝ} (hH : H ≠ 0) :
    ∀ o n, |normalizedIntegerColumns
      (integerJetMatrix (fun n => MvPolynomial.monomial (e n) 1) (integerAffineCube root difference) rows)
      (fun n => H / monomialScale T (e n)) (fun _ => H) o n| ≤
        kernelJetEntryAllowance (Fintype.card α) h := by
  intro o n
  rw [normalizedAffineMonomialJetMatrix_eq root difference e rows T hH]
  exact boundedDegreeRealJetMatrix_entry_bound _ _ hroot hdiff h rows o ⟨e n, he n⟩

theorem goodScalarKernelTuple_monomial_control {I J O N V : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    {L B : ℕ} {κ : ℝ} (hL : 0 < L) (selection : I → J) (hκ : 0 < κ)
    (x : J → IntegerScalarCubeBox I L) (hx : GoodScalarKernelTuple selection κ B x)
    (h : ℕ) (rows : O → Finset I) (hr : Function.Injective rows) (hrows : ∀ o, (rows o).card ≤ h) :
    ∃ s : O ↪ BoundedIntegerExponent J h, ∀ (H : ℝ), 0 < H →
      ∀ (root : V → ℤ) (difference : I → V → ℤ) (e : N → V →₀ ℕ) (T : V → ℝ),
      (∀ v, 0 < T v) → (∀ v, T v ≤ (L : ℝ)) →
      (∀ n, (e n).sum (fun _ d => d) ≤ h) →
      (∀ v, |(root v : ℝ) / T v| ≤ 1) → (∀ i v, |(difference i v : ℝ) / T v| ≤ 1) →
      CoefficientFiberControl
        (Matrix.fromCols (scalarKernelIntegerJet x h rows)
          (integerJetMatrix (fun n => MvPolynomial.monomial (e n) 1) (integerAffineCube root difference) rows))
        (s.trans Function.Embedding.inl)
        (Sum.elim (kernelJetCoefficientScale J h L H) (fun n => H / monomialScale T (e n)))
        H L h (kernelJetEntryAllowance (Fintype.card I) h)
        (kernelJetInverseAllowance (Fintype.card I) (Fintype.card J) (Fintype.card O) h κ)
        (((B ^ h) ^ Fintype.card O : ℕ) : ℝ) := by
  obtain ⟨s, hs⟩ := goodScalarKernelTuple_extended_control (N := N) hL selection hκ x hx h rows hr hrows
  refine ⟨s, fun H hH root difference e T hT hTL he hroot hdiff => ?_⟩
  apply hs H hH
  · intro n
    exact kernelCoefficientScale_lower T hT hH.le (by exact_mod_cast hL) hTL (e n) (he n)
  · exact normalizedAffineMonomialJetMatrix_bound root difference e rows T he hroot hdiff hH.ne'

end Erdos3

end

end OAI
