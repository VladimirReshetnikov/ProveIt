import GowersSzemeredi.Proofs16ColumnListSpectrum

/-! Remove the two auxiliary column constraints introduced by each splice.
The resulting identity uses only the anchors and output word entries. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def ColumnWordIdentity {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (r : Real) (as : List (ZMod N)) (w : ColumnWord N as.length) : Prop :=
  ∀ y, (∀ x ∈ as, y ∈ bohr (T x) r) →
    (∀ x ∈ columnWordEntries w, y ∈ bohr (T x) r) →
    columnWordEval (fun x => L x y) w = columnAnchorEval (fun x => L x y) as

/-- A length `k+1` representation needs at most `4*(k+1)*d` endpoint
frequencies and `2*k*d` auxiliary frequencies. The latter can be removed. -/
theorem column_word_identity_remove_aux {N d : Nat} [NeZero N] [Fact N.Prime]
    (X B : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) {rho r : Real}
    (hrho : 0 < rho) (hr : 0 < r) (hrle : r ≤ rho) (hBX : B ⊆ X)
    (hT : ∀ x ∈ X, (T x).card ≤ d)
    (hL : ∀ x ∈ X, IsFreimanLinearOn (bohr (T x) rho) (L x))
    (hzero : ∀ x ∈ X, L x 0 = 0)
    (a : ZMod N) (as : List (ZMod N)) (has : ∀ x ∈ a::as, x ∈ X)
    (w : ColumnWord N (a::as).length) (hw : w ∈ columnWordRepresentations B T L r (a::as))
    (hN : refinementKernelCap (4*(as.length+1)*d) (2*as.length*d) rho r < N) :
    ColumnWordIdentity T L (refinementKernelRadius (4*(as.length+1)*d) (2*as.length*d) rho r)
      (a::as) w := by
  let es := (a::as) ++ columnWordEntries w
  let us := columnWordAux (a::as) w
  let S := columnListSpectrum T es
  let U := columnListSpectrum T us
  let f := columnRepresentationDefect L (a::as) w
  have hes : ∀ x ∈ es, x ∈ X := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact has x hx
    · exact hBX (columnWordEntries_mem B w (columnWordRepresentations_spec B T L r _ w hw).1 x hx)
  have hus : ∀ x ∈ us, x ∈ X := fun x hx => hBX (columnWordAux_mem B T L r _ w hw x hx)
  have hS : S.card ≤ 4*(as.length+1)*d := by
    have h := columnListSpectrum_card_le T es (fun x hx => hT x (hes x hx))
    have hlen : es.length = 4*(as.length+1) := by
      simp only [es,List.length_append,List.length_cons,columnWordEntries_length]; omega
    simpa only [hlen] using h
  have hU : U.card ≤ 2*as.length*d := by
    have h := columnListSpectrum_card_le T us (fun x hx => hT x (hus x hx))
    simpa only [us,columnWordAux_length] using h
  have hf : IsFreimanLinearOn (bohr S rho) f :=
    columnRepresentationDefect_freiman T L (a::as) w rho (fun x hx => hL x (hes x hx))
  have hf0 : f 0 = 0 := by
    dsimp only [f,columnRepresentationDefect]
    rw [columnWordEval_eq_entries,
      columnAnchorEval_zero _ _ (fun x hx => hzero x (has x hx)),
      columnAnchorEval_zero _ _ (fun x hx => hzero x (hes x (List.mem_append_right _ hx))),sub_self]
  have hvanish : ∀ y ∈ bohr (S ∪ U) r, f y = 0 := by
    intro y hy
    rw [bohr_union] at hy
    obtain ⟨hyS,hyU⟩ := Finset.mem_inter.mp hy
    have he := (mem_columnListSpectrum_bohr T es r y).mp hyS
    have hu := (mem_columnListSpectrum_bohr T us r y).mp hyU
    have hd := columnWordDomain_of_entries_aux T r (a::as) w y
      (fun x hx => he x (List.mem_append_left _ hx))
      (fun x hx => he x (List.mem_append_right _ hx)) hu
    exact sub_eq_zero.mpr ((columnWordRepresentations_spec B T L r _ w hw).2.2 y hd).symm
  have hker := freiman_zero_remove_frequencies S U f hrho hr hrle hS hU hf hf0 hvanish hN
  intro y ha he
  have hy : y ∈ bohr S (refinementKernelRadius (4*(as.length+1)*d) (2*as.length*d) rho r) := by
    apply (mem_columnListSpectrum_bohr T es _ y).mpr
    intro x hx
    exact (List.mem_append.mp hx).elim (ha x) (he x)
  exact (sub_eq_zero.mp (hker y hy)).symm

end LeanProofs.GowersSzemeredi
