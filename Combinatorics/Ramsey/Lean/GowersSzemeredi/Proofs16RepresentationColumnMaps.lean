import GowersSzemeredi.Proofs16RepresentativeChoiceSelection

/-! Chosen representation rows define local column maps. Their normalized
version has index-zero value zero and uses at most eight original spectra.
Every property applies to any valid choice, including the good assignment
selected by the independent-choice theorem. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def representationColumnEntries {N : Nat} (q : FourRepresentationTuple N) : List (ZMod N) :=
  [q.1, q.2.1, q.2.2.1, q.2.2.2]

def representationColumnSpectrum {N : Nat} (T : ZMod N → Finset (ZMod N))
    (q : FourRepresentationTuple N) : Finset (ZMod N) := columnListSpectrum T (representationColumnEntries q)

def representationColumnMap {N : Nat} (L : ZMod N → ZMod N → ZMod N)
    (q : FourRepresentationTuple N) (y : ZMod N) : ZMod N :=
  columnAnchorEval (fun x => L x y) (representationColumnEntries q)

theorem representationColumnMap_eq {N : Nat} (L : ZMod N → ZMod N → ZMod N)
    (q : FourRepresentationTuple N) (y : ZMod N) :
    representationColumnMap L q y = representationTupleEval (fun x => L x y) q := by
  simp [representationColumnMap, representationColumnEntries, columnAnchorEval, representationTupleEval]
  ring

theorem representationColumnEntries_mem {N : Nat} (U : Finset (ZMod N)) {x : ZMod N}
    {q : FourRepresentationTuple N} (hq : q ∈ fourDifferenceRepresentations U x) :
    ∀ a ∈ representationColumnEntries q, a ∈ U := by
  have hm := (Finset.mem_filter.mp hq).1
  simpa only [representationColumnEntries, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Finset.mem_product] using hm

/-- A chosen four-term representation retains its original local-map data. -/
theorem representation_column_data {N d : Nat} [NeZero N]
    (X U : Finset (ZMod N)) (hUX : U ⊆ X) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (rho : Real)
    (hcol : ∀ x ∈ X, (T x).card ≤ d ∧ IsFreimanLinearOn (bohr (T x) rho) (L x) ∧ L x 0 = 0)
    {x : ZMod N} {q : FourRepresentationTuple N} (hq : q ∈ fourDifferenceRepresentations U x) :
    (representationColumnSpectrum T q).card ≤ 4*d ∧
      IsFreimanLinearOn (bohr (representationColumnSpectrum T q) rho) (representationColumnMap L q) ∧
      representationColumnMap L q 0 = 0 := by
  have hpoints : ∀ a ∈ representationColumnEntries q, a ∈ X :=
    fun a ha => hUX (representationColumnEntries_mem U hq a ha)
  refine ⟨?_, columnAnchorEval_freiman _ L (representationColumnEntries q) ?_,
    columnAnchorEval_zero _ _ (fun a ha => (hcol a (hpoints a ha)).2.2)⟩
  · have h := columnListSpectrum_card_le T (representationColumnEntries q)
      (fun a ha => (hcol a (hpoints a ha)).1)
    simpa [representationColumnSpectrum, representationColumnEntries] using h
  · intro a ha
    apply ((hcol a (hpoints a ha)).2.1).mono
    intro y hy
    exact (mem_columnListSpectrum_bohr T _ rho y).mp hy a ha

def normalizedRepresentationSpectrum {N : Nat} (T : ZMod N → Finset (ZMod N))
    (f : ZMod N → FourRepresentationTuple N) (x : ZMod N) : Finset (ZMod N) :=
  representationColumnSpectrum T (f x) ∪ representationColumnSpectrum T (f 0)

def normalizedRepresentationMap {N : Nat} (L : ZMod N → ZMod N → ZMod N)
    (f : ZMod N → FourRepresentationTuple N) (x y : ZMod N) : ZMod N :=
  representationColumnMap L (f x) y-representationColumnMap L (f 0) y

theorem normalizedRepresentationMap_index_zero {N : Nat}
    (L : ZMod N → ZMod N → ZMod N) (f : ZMod N → FourRepresentationTuple N) (y : ZMod N) :
    normalizedRepresentationMap L f 0 y = 0 := by simp [normalizedRepresentationMap]

/-- Normalization keeps a common full radius with eight original spectra. -/
theorem normalized_representation_column_data {N d : Nat} [NeZero N]
    (X U C : Finset (ZMod N)) (hUX : U ⊆ X) (h0 : (0 : ZMod N) ∈ C)
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N) (rho : Real)
    (hcol : ∀ x ∈ X, (T x).card ≤ d ∧ IsFreimanLinearOn (bohr (T x) rho) (L x) ∧ L x 0 = 0)
    (f : ZMod N → FourRepresentationTuple N) (hvalid : ∀ x ∈ C, f x ∈ fourDifferenceRepresentations U x) :
    ∀ x ∈ C, (normalizedRepresentationSpectrum T f x).card ≤ 8*d ∧
      IsFreimanLinearOn (bohr (normalizedRepresentationSpectrum T f x) rho) (normalizedRepresentationMap L f x) ∧
      normalizedRepresentationMap L f x 0 = 0 := by
  have href := representation_column_data X U hUX T L rho hcol (hvalid 0 h0)
  intro x hx
  have hdata := representation_column_data X U hUX T L rho hcol (hvalid x hx)
  refine ⟨(Finset.card_union_le _ _).trans (by omega), ?_, ?_⟩
  · have hxF := hdata.2.1.mono (show bohr (normalizedRepresentationSpectrum T f x) rho ⊆
        bohr (representationColumnSpectrum T (f x)) rho from by
      intro y hy; rw [normalizedRepresentationSpectrum, bohr_union] at hy
      exact (Finset.mem_inter.mp hy).1)
    have h0F := href.2.1.mono (show bohr (normalizedRepresentationSpectrum T f x) rho ⊆
        bohr (representationColumnSpectrum T (f 0)) rho from by
      intro y hy; rw [normalizedRepresentationSpectrum, bohr_union] at hy
      exact (Finset.mem_inter.mp hy).2)
    intro a b c d ha hb hc hd he
    have ex := hxF a b c d ha hb hc hd he
    have e0 := h0F a b c d ha hb hc hd he
    simp only [normalizedRepresentationMap]
    linear_combination ex-e0
  · simp only [normalizedRepresentationMap, hdata.2.2, href.2.2, sub_self]

end LeanProofs.GowersSzemeredi
