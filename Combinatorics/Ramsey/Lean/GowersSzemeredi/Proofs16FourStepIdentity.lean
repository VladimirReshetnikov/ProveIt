import GowersSzemeredi.Proofs16ColumnPairComposition

/-! Compose four local identities while removing all intermediate
frequencies in one step. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem ColumnPairIdentity.cross {N : Nat} [NeZero N]
    {T : ZMod N → Finset (ZMod N)} {L : ZMod N → ZMod N → ZMod N}
    {r : Real} {p q : ZMod N × ZMod N} (h : ColumnPairIdentity T L r p q) :
    ColumnPairIdentity T L r (p.1,q.1) (p.2,q.2) := by
  intro y hp1 hq1 hp2 hq2
  have heq := h y hp1 hp2 hq1 hq2
  change L p.1 y-L q.1 y = L p.2 y-L q.2 y
  linear_combination heq

/-- Four consecutive identities require only the six intermediate
column spectra to be removed; the conclusion uses the endpoint spectra. -/
theorem ColumnPairIdentity.four_step_shrink {N d : Nat} [NeZero N] [Fact N.Prime]
    (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) {rho r : Real}
    (hrho : 0 < rho) (hr : 0 < r) (hrle : r ≤ rho)
    (hT : ∀ x ∈ X, (T x).card ≤ d)
    (hL : ∀ x ∈ X, IsFreimanLinearOn (bohr (T x) rho) (L x))
    (hzero : ∀ x ∈ X, L x 0 = 0)
    (p : Fin 5 → ZMod N × ZMod N) (hp : ∀ i, (p i).1 ∈ X ∧ (p i).2 ∈ X)
    (h01 : ColumnPairIdentity T L r (p 0) (p 1))
    (h12 : ColumnPairIdentity T L r (p 1) (p 2))
    (h23 : ColumnPairIdentity T L r (p 2) (p 3))
    (h34 : ColumnPairIdentity T L r (p 3) (p 4))
    (hN : refinementKernelCap (4*d) (6*d) rho r < N) :
    ColumnPairIdentity T L (refinementKernelRadius (4*d) (6*d) rho r) (p 0) (p 4) := by
  let t := columnPairTuple (p 0) (p 4)
  let S := columnQuadrupleSpectrum T t
  let a : Fin 6 → ZMod N := ![(p 1).1,(p 1).2,(p 2).1,(p 2).2,(p 3).1,(p 3).2]
  let U := Finset.univ.biUnion (fun i => T (a i))
  let f := columnQuadrupleDefect L t
  have ht : ∀ i, t i ∈ X := by
    intro i; fin_cases i
    · exact (hp 0).1
    · exact (hp 4).2
    · exact (hp 0).2
    · exact (hp 4).1
  have ha : ∀ i, a i ∈ X := by
    intro i; fin_cases i
    · exact (hp 1).1
    · exact (hp 1).2
    · exact (hp 2).1
    · exact (hp 2).2
    · exact (hp 3).1
    · exact (hp 3).2
  have hS : S.card ≤ 4*d := by
    apply Finset.card_biUnion_le.trans
    calc (∑ i : Fin 4, (T (t i)).card) ≤ ∑ _i : Fin 4, d := Finset.sum_le_sum fun i _ => hT _ (ht i)
      _ = 4*d := by simp
  have hU : U.card ≤ 6*d := by
    apply Finset.card_biUnion_le.trans
    calc (∑ i : Fin 6, (T (a i)).card) ≤ ∑ _i : Fin 6, d := Finset.sum_le_sum fun i _ => hT _ (ha i)
      _ = 6*d := by simp
  have hf := columnQuadrupleDefect_freiman T L t (fun i => hL _ (ht i))
  have hf0 : f 0 = 0 := by simp only [f, columnQuadrupleDefect, hzero _ (ht _), add_zero, sub_zero]
  have hvanish : ∀ y ∈ bohr (S ∪ U) r, f y = 0 := by
    intro y hy
    rw [bohr_union] at hy
    obtain ⟨hyS, hyU⟩ := Finset.mem_inter.mp hy
    obtain ⟨h01', h02', h41', h42'⟩ := (mem_columnPairTuple_bohr T (p 0) (p 4) r y).mp hyS
    have hm := (mem_bohr_family_union (fun i => T (a i)) r y).mp hyU
    have e1 := h01 y h01' h02' (hm 0) (hm 1)
    have e2 := h12 y (hm 0) (hm 1) (hm 2) (hm 3)
    have e3 := h23 y (hm 2) (hm 3) (hm 4) (hm 5)
    have e4 := h34 y (hm 4) (hm 5) h41' h42'
    change L (p 0).1 y + L (p 4).2 y - L (p 0).2 y - L (p 4).1 y = 0
    linear_combination e1+e2+e3+e4
  have hker := freiman_zero_remove_frequencies S U f hrho hr hrle hS hU hf hf0 hvanish hN
  intro y h01' h02' h41' h42'
  have heq := hker y ((mem_columnPairTuple_bohr T (p 0) (p 4) _ y).mpr ⟨h01',h02',h41',h42'⟩)
  change L (p 0).1 y + L (p 4).2 y - L (p 0).2 y - L (p 4).1 y = 0 at heq
  linear_combination heq

end LeanProofs.GowersSzemeredi
