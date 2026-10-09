import GowersSzemeredi.Proofs16BohrFrequencyEscape

/-! Escaping frequencies enlarge a dissociated family. Its size is bounded
by the existing explicit bounded-span rank estimate. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- A frequency outside the selected unit span preserves dissociation
when added to the selected set. -/
theorem addDissociated_insert_of_not_mem_unit_span {N : Nat} [NeZero N]
    (D : Finset (ZMod N)) (q : ZMod N) (hD : AddDissociated (D : Set (ZMod N)))
    (hq : q ∉ boundedFrequencySpan (fun a : D => (a : ZMod N)) 1) :
    AddDissociated ((insert q D : Finset (ZMod N)) : Set (ZMod N)) := by
  have hqa : q ∉ D.addSpan := fun h => hq (addSpan_subset_boundedFrequencySpan_one D h)
  by_contra hn
  obtain ⟨t,u,ht,hu,hdisj,hne,he⟩ := not_addDissociated_iff_exists_disjoint.mp hn
  have hex (v w : Finset (ZMod N))
      (hv : v ⊆ insert q D) (hw : w ⊆ insert q D)
      (hd : Disjoint v w) (hvw : ∑ a ∈ v, a = ∑ a ∈ w, a) (hqv : q ∈ v) : False := by
    have hqw : q ∉ w := fun h => Finset.disjoint_left.mp hd hqv h
    have hwD : w ⊆ D := (Finset.subset_insert_iff_of_notMem hqw).mp hw
    have hvD : v.erase q ⊆ D := (Finset.subset_insert_iff.mp hv)
    have hrepr : q = (∑ a ∈ w, a)-(∑ a ∈ v.erase q, a) := by
      have hsum := Finset.sum_erase_add v id hqv
      change (∑ a ∈ v.erase q, a)+q = ∑ a ∈ v, a at hsum
      linear_combination hvw+hsum
    exact hqa (hrepr ▸ Finset.sum_sub_sum_mem_addSpan hwD hvD)
  by_cases hqt : q ∈ t
  · exact hex t u ht hu hdisj he hqt
  by_cases hqu : q ∈ u
  · exact hex u t hu ht hdisj.symm he.symm hqu
  have htD : t ⊆ D := (Finset.subset_insert_iff_of_notMem hqt).mp ht
  have huD : u ⊆ D := (Finset.subset_insert_iff_of_notMem hqu).mp hu
  exact hne (hD htD huD he)

/-- Each new independent frequency consumes one unit of the explicit
rank budget of the ambient bounded span. -/
theorem bounded_span_escape_rank_budget {N : Nat} [NeZero N]
    (K D : Finset (ZMod N)) (R : Nat) (q : ZMod N)
    (hD : AddDissociated (D : Set (ZMod N)))
    (hDK : D ⊆ boundedFrequencySpan (fun a : K => (a : ZMod N)) R)
    (hqK : q ∈ boundedFrequencySpan (fun a : K => (a : ZMod N)) R)
    (hqD : q ∉ boundedFrequencySpan (fun a : D => (a : ZMod N)) 1) :
    AddDissociated ((insert q D : Finset (ZMod N)) : Set (ZMod N)) ∧
      D.card+1 ≤ spanGeneratorBound K.card R := by
  have hnew := addDissociated_insert_of_not_mem_unit_span D q hD hqD
  have hqnot : q ∉ D := fun h => hqD
    (addSpan_subset_boundedFrequencySpan_one D (Finset.subset_addSpan h))
  have hbound := subsetSum_count_rank_bound (insert q D).card K.card R
    (dissociated_boundedSpan_count K (insert q D) R (Finset.insert_subset_iff.mpr ⟨hqK,hDK⟩) hnew)
  exact ⟨hnew,by simpa only [Finset.card_insert_of_notMem hqnot] using hbound⟩

/-- A failed containment supplies an actual enlargement of the selected
independent family, within the explicit rank budget. -/
theorem bohr_escape_extends_independent_family {N d : Nat} [NeZero N] [Fact N.Prime]
    (T U D : Finset (ZMod N)) {r sigma : Real}
    (hr : 0 < r) (hr4 : r < 4) (hT : T.card ≤ d) (hU : U.card ≤ d)
    (hD : AddDissociated (D : Set (ZMod N)))
    (hDT : D ⊆ boundedFrequencySpan (fun a : T => (a : ZMod N)) (bohrExtensionCutoff d r))
    (hs : (D.card : Real)*sigma ≤ 1/(4*Real.pi))
    (hfail : ¬ bohr D sigma ⊆ bohrQuarterSum T U r) :
    ∃ q ∈ bohrExtensionSpectrum T U d r,
      q ∉ D ∧ AddDissociated ((insert q D : Finset (ZMod N)) : Set (ZMod N)) ∧
      D.card+1 ≤ spanGeneratorBound T.card (bohrExtensionCutoff d r) := by
  obtain ⟨y,hy,q,hq,_,hqD⟩ := bohr_sum_frequency_escape T U D hr hr4 hT hU hs hfail
  have hbudget := bounded_span_escape_rank_budget T D _ q hD hDT (Finset.mem_inter.mp hq).1 hqD
  exact ⟨q,hq,fun h => hqD (addSpan_subset_boundedFrequencySpan_one D (Finset.subset_addSpan h)),hbudget⟩

end LeanProofs.GowersSzemeredi
