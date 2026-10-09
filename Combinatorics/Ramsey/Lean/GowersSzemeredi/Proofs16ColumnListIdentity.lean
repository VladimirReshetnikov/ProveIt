import GowersSzemeredi.Proofs16ColumnWordIdentity

/-! Compare alternating column lists through a shared representation,
then remove the shared representation's spectra. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def ColumnListIdentity {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (r : Real) (as bs : List (ZMod N)) : Prop :=
  ∀ y, (∀ x ∈ as, y ∈ bohr (T x) r) → (∀ x ∈ bs, y ∈ bohr (T x) r) →
    columnAnchorEval (fun x => L x y) as = columnAnchorEval (fun x => L x y) bs

theorem ColumnListIdentity.symm {N : Nat} [NeZero N]
    {T : ZMod N → Finset (ZMod N)} {L : ZMod N → ZMod N → ZMod N}
    {r : Real} {as bs : List (ZMod N)} (h : ColumnListIdentity T L r as bs) :
    ColumnListIdentity T L r bs as := fun y hb ha => (h y ha hb).symm

theorem ColumnWordIdentity.to_list {N : Nat} [NeZero N]
    {T : ZMod N → Finset (ZMod N)} {L : ZMod N → ZMod N → ZMod N}
    {r : Real} {as : List (ZMod N)} {w : ColumnWord N as.length}
    (h : ColumnWordIdentity T L r as w) : ColumnListIdentity T L r as (columnWordEntries w) := by
  intro y ha hw
  simpa only [columnWordEval_eq_entries] using (h y ha hw).symm

/-- Composing through a common list costs only its spectrum rank. -/
theorem columnListIdentity_trans_shrink {N d D E : Nat} [NeZero N] [Fact N.Prime]
    (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) {rho r : Real}
    (hrho : 0 < rho) (hr : 0 < r) (hrle : r ≤ rho)
    (hT : ∀ x ∈ X, (T x).card ≤ d)
    (hL : ∀ x ∈ X, IsFreimanLinearOn (bohr (T x) rho) (L x))
    (hzero : ∀ x ∈ X, L x 0 = 0)
    (as bs cs : List (ZMod N))
    (ha : ∀ x ∈ as, x ∈ X) (hb : ∀ x ∈ bs, x ∈ X) (hc : ∀ x ∈ cs, x ∈ X)
    (hD : as.length+cs.length ≤ D) (hE : bs.length ≤ E)
    (hab : ColumnListIdentity T L r as bs) (hbc : ColumnListIdentity T L r bs cs)
    (hN : refinementKernelCap (D*d) (E*d) rho r < N) :
    ColumnListIdentity T L (refinementKernelRadius (D*d) (E*d) rho r) as cs := by
  let S := columnListSpectrum T (as++cs)
  let U := columnListSpectrum T bs
  let f := fun y => columnAnchorEval (fun x => L x y) as-columnAnchorEval (fun x => L x y) cs
  have hes : ∀ x ∈ as++cs, x ∈ X := fun x hx => (List.mem_append.mp hx).elim (ha x) (hc x)
  have hS : S.card ≤ D*d :=
    (columnListSpectrum_card_le T _ (fun x hx => hT x (hes x hx))).trans
      (Nat.mul_le_mul_right d (by simpa only [List.length_append] using hD))
  have hU : U.card ≤ E*d :=
    (columnListSpectrum_card_le T bs (fun x hx => hT x (hb x hx))).trans (Nat.mul_le_mul_right d hE)
  have hLS : ∀ x ∈ as++cs, IsFreimanLinearOn (bohr S rho) (L x) := by
    intro x hx a b c e hya hyb hyc hye he
    exact hL x (hes x hx) a b c e
      ((mem_columnListSpectrum_bohr T _ rho a).mp hya x hx)
      ((mem_columnListSpectrum_bohr T _ rho b).mp hyb x hx)
      ((mem_columnListSpectrum_bohr T _ rho c).mp hyc x hx)
      ((mem_columnListSpectrum_bohr T _ rho e).mp hye x hx) he
  have hf : IsFreimanLinearOn (bohr S rho) f := by
    have hfa := columnAnchorEval_freiman (bohr S rho) L as
      (fun x hx => hLS x (List.mem_append_left _ hx))
    have hfc := columnAnchorEval_freiman (bohr S rho) L cs
      (fun x hx => hLS x (List.mem_append_right _ hx))
    intro a b c e hya hyb hyc hye he
    have ea := hfa a b c e hya hyb hyc hye he
    have ec := hfc a b c e hya hyb hyc hye he
    dsimp only [f]
    linear_combination ea-ec
  have hf0 : f 0 = 0 := by
    dsimp only [f]
    rw [columnAnchorEval_zero _ _ (fun x hx => hzero x (ha x hx)),
      columnAnchorEval_zero _ _ (fun x hx => hzero x (hc x hx)),sub_self]
  have hz : ∀ y ∈ bohr (S ∪ U) r, f y = 0 := by
    intro y hy
    rw [bohr_union] at hy
    have he := (mem_columnListSpectrum_bohr T (as++cs) r y).mp (Finset.mem_inter.mp hy).1
    have hm := (mem_columnListSpectrum_bohr T bs r y).mp (Finset.mem_inter.mp hy).2
    exact sub_eq_zero.mpr ((hab y (fun x hx => he x (List.mem_append_left _ hx)) hm).trans
      (hbc y hm (fun x hx => he x (List.mem_append_right _ hx))))
  have hker := freiman_zero_remove_frequencies S U f hrho hr hrle hS hU hf hf0 hz hN
  intro y hya hyc
  apply sub_eq_zero.mp (hker y ?_)
  apply (mem_columnListSpectrum_bohr T (as++cs) _ y).mpr
  intro x hx
  exact (List.mem_append.mp hx).elim (hya x) (hyc x)

end LeanProofs.GowersSzemeredi
