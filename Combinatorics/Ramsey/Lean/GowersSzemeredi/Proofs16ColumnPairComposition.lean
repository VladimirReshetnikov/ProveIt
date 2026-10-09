import GowersSzemeredi.Proofs16RefinementKernel
import GowersSzemeredi.Proofs16PrimeColumnIdentities

/-! Exact column-pair identities compose after a uniform radius shrink.
Intermediate column frequencies are removed from the conclusion. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def columnPairTuple {N : Nat} (p q : ZMod N × ZMod N) : Fin 4 → ZMod N :=
  ![p.1, q.2, p.2, q.1]

def ColumnPairIdentity {N : Nat} [NeZero N] (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (r : Real) (p q : ZMod N × ZMod N) : Prop :=
  ∀ y, y ∈ bohr (T p.1) r → y ∈ bohr (T p.2) r →
    y ∈ bohr (T q.1) r → y ∈ bohr (T q.2) r →
      L p.1 y - L p.2 y = L q.1 y - L q.2 y

theorem ColumnPairIdentity.refl {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (r : Real) (p : ZMod N × ZMod N) : ColumnPairIdentity T L r p p := by
  intro y _ _ _ _
  rfl

theorem ColumnPairIdentity.symm {N : Nat} [NeZero N]
    {T : ZMod N → Finset (ZMod N)} {L : ZMod N → ZMod N → ZMod N}
    {r : Real} {p q : ZMod N × ZMod N} (h : ColumnPairIdentity T L r p q) :
    ColumnPairIdentity T L r q p := by
  intro y hq1 hq2 hp1 hp2
  exact (h y hp1 hp2 hq1 hq2).symm

theorem ColumnPairIdentity.mono_radius {N : Nat} [NeZero N]
    {T : ZMod N → Finset (ZMod N)} {L : ZMod N → ZMod N → ZMod N}
    {r s : Real} {p q : ZMod N × ZMod N} (h : ColumnPairIdentity T L r p q) (hs : s ≤ r) :
    ColumnPairIdentity T L s p q := by
  intro y hp1 hp2 hq1 hq2
  exact h y (bohr_mono_radius _ hs hp1) (bohr_mono_radius _ hs hp2)
    (bohr_mono_radius _ hs hq1) (bohr_mono_radius _ hs hq2)

/-- A common-domain identity can be expressed by the four-frequency
union without introducing extra constraints. -/
theorem mem_columnPairTuple_bohr {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (p q : ZMod N × ZMod N) (r : Real) (y : ZMod N) :
    y ∈ bohr (columnQuadrupleSpectrum T (columnPairTuple p q)) r ↔
      y ∈ bohr (T p.1) r ∧ y ∈ bohr (T p.2) r ∧ y ∈ bohr (T q.1) r ∧ y ∈ bohr (T q.2) r := by
  unfold columnQuadrupleSpectrum
  rw [mem_bohr_family_union]
  simp only [columnPairTuple, Fin.forall_fin_succ, Fin.forall_fin_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, and_true]
  tauto

/-- Compose identities through an intermediate column pair, then discard
its frequencies using the prime-target refinement-kernel theorem. -/
theorem ColumnPairIdentity.trans_shrink {N d : Nat} [NeZero N] [Fact N.Prime]
    (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) {rho r : Real} (hrho : 0 < rho) (hr : 0 < r) (hrle : r ≤ rho)
    (hT : ∀ x ∈ X, (T x).card ≤ d)
    (hL : ∀ x ∈ X, IsFreimanLinearOn (bohr (T x) rho) (L x)) (hzero : ∀ x ∈ X, L x 0 = 0)
    {p q z : ZMod N × ZMod N} (hp : p.1 ∈ X ∧ p.2 ∈ X)
    (hq : q.1 ∈ X ∧ q.2 ∈ X) (hz : z.1 ∈ X ∧ z.2 ∈ X)
    (hpq : ColumnPairIdentity T L r p q) (hqz : ColumnPairIdentity T L r q z)
    (hN : refinementKernelCap (4*d) (2*d) rho r < N) :
    ColumnPairIdentity T L (refinementKernelRadius (4*d) (2*d) rho r) p z := by
  let t := columnPairTuple p z
  let S := columnQuadrupleSpectrum T t
  let U := T q.1 ∪ T q.2
  let f := columnQuadrupleDefect L t
  have ht : ∀ i, t i ∈ X := by
    intro i; fin_cases i
    · exact hp.1
    · exact hz.2
    · exact hp.2
    · exact hz.1
  have hS : S.card ≤ 4*d := by
    apply Finset.card_biUnion_le.trans
    calc (∑ i : Fin 4, (T (t i)).card) ≤ ∑ _i : Fin 4, d := Finset.sum_le_sum fun i _ => hT _ (ht i)
      _ = 4*d := by simp
  have hU : U.card ≤ 2*d := (Finset.card_union_le _ _).trans (by have := hT _ hq.1; have := hT _ hq.2; omega)
  have hf : IsFreimanLinearOn (bohr S rho) f := columnQuadrupleDefect_freiman T L t (fun i => hL _ (ht i))
  have hf0 : f 0 = 0 := by
    simp only [f, columnQuadrupleDefect, hzero _ (ht _), add_zero, sub_zero]
  have hvanish : ∀ y ∈ bohr (S ∪ U) r, f y = 0 := by
    intro y hy
    rw [bohr_union] at hy
    have hyS := (Finset.mem_inter.mp hy).1
    have hyU := (Finset.mem_inter.mp hy).2
    rw [bohr_union] at hyU
    obtain ⟨hp1, hp2, hz1, hz2⟩ := (mem_columnPairTuple_bohr T p z r y).mp hyS
    obtain ⟨hq1, hq2⟩ := Finset.mem_inter.mp hyU
    have h1 := hpq y hp1 hp2 hq1 hq2
    have h2 := hqz y hq1 hq2 hz1 hz2
    change L p.1 y + L z.2 y - L p.2 y - L z.1 y = 0
    linear_combination h1 + h2
  have hker := freiman_zero_remove_frequencies S U f hrho hr hrle hS hU hf hf0 hvanish hN
  intro y hp1 hp2 hz1 hz2
  have h := hker y ((mem_columnPairTuple_bohr T p z _ y).mpr ⟨hp1, hp2, hz1, hz2⟩)
  change L p.1 y + L z.2 y - L p.2 y - L z.1 y = 0 at h
  linear_combination h

end LeanProofs.GowersSzemeredi
