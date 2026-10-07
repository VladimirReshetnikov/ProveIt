import OAI.Combinatorics.Progressions.Estimates.CoefficientRowReindex

namespace OAI

section

namespace Erdos3

theorem scalarKernelJet_normalized_entry {I J O : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [Fintype O] [DecidableEq O]
    {L : ℕ} (hL : 0 < L) (x : J → IntegerScalarCubeBox I L)
    (h : ℕ) (rows : O → Finset I) {H : ℝ} (hH : H ≠ 0)
    (o : O) (e : BoundedIntegerExponent J h) :
    |normalizedIntegerColumns (scalarKernelIntegerJet x h rows)
      (kernelJetCoefficientScale J h L H) (fun _ => H) o e| ≤
        kernelJetEntryAllowance (Fintype.card I) h := by
  have hc (j : J) (i : Option I) : |(x j i : ℝ) / L| ≤ 1 :=
    (norm_le_pi_norm (fun i => (x j i : ℝ) / L) i).trans
      (integerScalarCubeBox_normalized_norm_le hL (x j))
  have he := congrFun (congrFun (normalizedScalarKernelJet_eq x h rows hH) o) e
  change |normalizedIntegerColumns (scalarKernelIntegerJet x h rows)
    (fun e => H / monomialScale (fun _ => (L : ℝ)) e.val) (fun _ => H) o e| ≤ _
  rw [he]
  exact boundedDegreeRealJetMatrix_entry_bound _ _ (fun j => hc j none)
    (fun i j => hc j (some i)) h rows o e

theorem scalarKernelJet_integer_entry {I J O : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [Fintype O] [DecidableEq O]
    {L : ℕ} (hL : 0 < L) (x : J → IntegerScalarCubeBox I L)
    (h : ℕ) (rows : O → Finset I) (o : O) (e : BoundedIntegerExponent J h) :
    |(scalarKernelIntegerJet x h rows o e : ℝ)| ≤
      kernelJetEntryAllowance (Fintype.card I) h * (L : ℝ) ^ h := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hc (j : J) (i : Option I) : |(x j i : ℝ) / L| ≤ 1 :=
    (norm_le_pi_norm (fun i => (x j i : ℝ) / L) i).trans
      (integerScalarCubeBox_normalized_norm_le hL (x j))
  exact boundedDegreeIntegerJetMatrix_entry_bound _ _ (fun _ => (L : ℝ))
    (fun _ => hLr) (by exact_mod_cast hL) (fun _ => le_rfl)
    (fun j => hc j none) (fun i j => hc j (some i)) h rows o e

theorem goodScalarKernelTuple_extended_control {I J O N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    {L B : ℕ} {κ : ℝ} (hL : 0 < L) (selection : I → J) (hκ : 0 < κ)
    (x : J → IntegerScalarCubeBox I L) (hx : GoodScalarKernelTuple selection κ B x)
    (h : ℕ) (rows : O → Finset I) (hr : Function.Injective rows) (hrows : ∀ o, (rows o).card ≤ h) :
    ∃ s : O ↪ BoundedIntegerExponent J h, ∀ (H : ℝ), 0 < H →
      ∀ (C : Matrix O N ℤ) (T : N → ℝ),
      (∀ n, H / (L : ℝ) ^ h ≤ T n) →
      (∀ o n, |normalizedIntegerColumns C T (fun _ => H) o n| ≤ kernelJetEntryAllowance (Fintype.card I) h) →
      CoefficientFiberControl (Matrix.fromCols (scalarKernelIntegerJet x h rows) C)
        (s.trans Function.Embedding.inl) (Sum.elim (kernelJetCoefficientScale J h L H) T)
        H L h (kernelJetEntryAllowance (Fintype.card I) h)
        (kernelJetInverseAllowance (Fintype.card I) (Fintype.card J) (Fintype.card O) h κ)
        (((B ^ h) ^ Fintype.card O : ℕ) : ℝ) := by
  obtain ⟨s, hd, hn⟩ := goodScalarKernelTuple_fixed_jet_pivot hL selection hκ x hx h rows hr hrows
  refine ⟨s, fun H hH C T hscale hentry => ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [fromCols_left_pivot]
  · intro j
    cases j with
    | inl e => exact kernelJetCoefficientScale_lower J h (by exact_mod_cast hL) hH.le e
    | inr n => exact hscale n
  · intro o j
    exact scalarKernelJet_integer_entry hL x h rows o (s j)
  · intro o j
    rw [normalizedIntegerColumns_fromCols]
    cases j with
    | inl e =>
      simpa only [Matrix.fromCols_apply_inl, normalizedIntegerColumns_entry_div] using
        scalarKernelJet_normalized_entry hL x h rows hH.ne' o e
    | inr n => exact hentry o n
  · rw [fromCols_left_pivot]
    exact hn H hH.ne'
  · exact_mod_cast scalarKernelJet_extended_index selection x hx h rows hr hrows C

end Erdos3

end

end OAI
