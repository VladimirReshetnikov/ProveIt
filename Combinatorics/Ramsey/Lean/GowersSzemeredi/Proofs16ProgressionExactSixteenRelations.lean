import GowersSzemeredi.Proofs16SixteenTupleChains

/-! Exact sixteen-endpoint relations from exact quadruples on the parent.
All chain constraints are removed before stating the endpoint identity.
The radius cost has endpoint rank 16*d and anchor rank 8*d. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open scoped BigOperators

/-- Every additive sixteen-tuple on the smaller progression is respected
on its natural endpoint domain. The same normalized maps are used. -/
theorem progression_all_sixteen_exact_of_quad_compatible {N d : Nat} [NeZero N] [Fact N.Prime]
    (Q : CenteredProgression N) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) {rho : Real} (hr : 0 < rho)
    (hdata : ∀ x ∈ Q.carrier, (T x).card ≤ d ∧
      IsFreimanLinearOn (bohr (T x) rho) (L x) ∧ L x 0 = 0)
    (hquad : ∀ a b c e, a ∈ Q.carrier → b ∈ Q.carrier → c ∈ Q.carrier → e ∈ Q.carrier →
      a-b = c-e → ColumnPairCompatible T L rho (a,b) (c,e))
    (hKN : refinementKernelCap (16*d) (8*d) rho rho < N)
    (q : PairedSixteenTuple N)
    (hq : ∀ i, (q i).1 ∈ (centeredProgressionShrink Q 256).carrier ∧
      (q i).2 ∈ (centeredProgressionShrink Q 256).carrier)
    (hadd : pairedSixteenIndex q = 0) :
    ∀ y ∈ bohr (pairedSixteenSpectrum T q)
      (rho / (2 * refinementKernelCap (16*d) (8*d) rho rho)), pairedSixteenDefect L q y = 0 := by
  have hqQ : ∀ i, (q i).1 ∈ Q.carrier ∧ (q i).2 ∈ Q.carrier :=
    fun i => ⟨centered_progression_shrink_subset Q 256 (hq i).1,
      centered_progression_shrink_subset Q 256 (hq i).2⟩
  have hchain := paired_sixteen_chain_mem Q q hq
  let A := pairedSixteenSpectrum T q
  let U := Finset.univ.biUnion fun i : Fin 8 => T (pairedSixteenShift q i.castSucc)
  have hmem : ∀ y ∈ bohr (A ∪ U) rho,
      (∀ i, y ∈ bohr (T (q i).1) rho ∧ y ∈ bohr (T (q i).2) rho) ∧
      (∀ i : Fin 9, y ∈ bohr (T (pairedSixteenShift q i)) rho) := by
    intro y hy
    rw [bohr_union] at hy
    refine ⟨(mem_paired_sixteen_spectrum_bohr T q rho y).mp (Finset.mem_inter.mp hy).1, ?_⟩
    have hfirst : ∀ i : Fin 8, y ∈ bohr (T (pairedSixteenShift q i.castSucc)) rho := by
      intro i
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun t ht => ?_⟩
      exact (Finset.mem_filter.mp (Finset.mem_inter.mp hy).2).2 t
        (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,ht⟩)
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j,rfl⟩ | rfl
    · exact hfirst j
    · rw [paired_sixteen_chain_closed q hadd]
      exact hfirst 0
  have hzero : ∀ y ∈ bohr (A ∪ U) rho, pairedSixteenDefect L q y = 0 := by
    intro y hy
    have h := hmem y hy
    have hquads : ∀ i : Fin 8, columnQuadDefect L (q i).1 (q i).2
        (pairedSixteenShift q i.succ) (pairedSixteenShift q i.castSucc) y = 0 := by
      intro i
      have hc := hquad (q i).1 (q i).2 (pairedSixteenShift q i.succ) (pairedSixteenShift q i.castSucc)
        (hqQ i).1 (hqQ i).2 (hchain i.succ) (hchain i.castSucc) (paired_sixteen_chain_step q i)
      have hleft : y ∈ bohr (columnDifferenceSpectrum T ((q i).1,(q i).2)) rho := by
        simpa only [columnDifferenceSpectrum,bohr_union,Finset.mem_inter] using (h.1 i)
      have hright : y ∈ bohr (columnDifferenceSpectrum T
          (pairedSixteenShift q i.succ,pairedSixteenShift q i.castSucc)) rho := by
        simpa only [columnDifferenceSpectrum,bohr_union,Finset.mem_inter] using
          And.intro (h.2 i.succ) (h.2 i.castSucc)
      have he := hc y hleft hright
      dsimp only [columnDifferenceMap] at he
      dsimp only [columnQuadDefect]
      linear_combination he
    rw [← paired_sixteen_chain_defect L q hadd y]
    exact Finset.sum_eq_zero (fun i _ => hquads i)
  have hA : A.card ≤ 16*d := paired_sixteen_spectrum_card T q
    (fun i => ⟨(hdata _ (hqQ i).1).1,(hdata _ (hqQ i).2).1⟩)
  have hU : U.card ≤ 8*d := by
    apply Finset.card_biUnion_le.trans
    calc (∑ i : Fin 8, (T (pairedSixteenShift q i.castSucc)).card) ≤ ∑ _i : Fin 8, d :=
        Finset.sum_le_sum fun i _ => (hdata _ (hchain i.castSucc)).1
      _ = _ := by simp [Fintype.card_fin]
  have hf := paired_sixteen_defect_freiman T L q rho
    (fun i => ⟨(hdata _ (hqQ i).1).2.1,(hdata _ (hqQ i).2).2.1⟩)
  have hf0 : pairedSixteenDefect L q 0 = 0 := by
    simp [pairedSixteenDefect, fun i => (hdata _ (hqQ i).1).2.2,
      fun i => (hdata _ (hqQ i).2).2.2]
  have hout := freiman_zero_remove_frequencies A U (pairedSixteenDefect L q)
    hr hr le_rfl hA hU hf hf0 hzero hKN
  simpa only [refinementKernelRadius, div_div] using hout

end LeanProofs.GowersSzemeredi
