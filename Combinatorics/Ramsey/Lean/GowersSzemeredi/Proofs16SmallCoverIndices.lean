import GowersSzemeredi.Proofs16BoundedSpanPhase
import GowersSzemeredi.Proofs16SelectedRowBohr

/-! Lift small signed-span generators to actual selected-map indices.
The chosen indices retain both domain membership and row-alphabet membership. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem spanGeneratorBound_mono_rank {k l : Nat} (hkl : k ≤ l) (R : Nat) :
    spanGeneratorBound k R ≤ spanGeneratorBound l R := by
  unfold spanGeneratorBound
  apply Nat.ceil_mono
  have hklR : (k : Real) ≤ l := by exact_mod_cast hkl
  have hlog : 0 ≤ Real.log (2 * (R : Real) + 1) := Real.log_nonneg (by have : (0 : Real) ≤ R := Nat.cast_nonneg R; linarith)
  gcongr

/-- A small family of actual indices spans all covered values. Zero does
not require an index or a domain-membership hypothesis. -/
theorem exists_small_cover_indices {N : Nat} [NeZero N] {ι : Type*}
    (K B : Finset (ZMod N)) (R : Nat) (I : Finset ι) (f : ι → ZMod N)
    (hB : B ⊆ boundedFrequencySpan (fun k : K => (k : ZMod N)) R)
    (hcover : B ⊆ insert 0 (I.image f)) :
    ∃ J : Finset ι, J ⊆ I ∧ J.card ≤ spanGeneratorBound K.card R ∧
      B ⊆ boundedFrequencySpan (fun k : J.image f => (k : ZMod N)) 1 := by
  classical
  obtain ⟨D, hDB, hDcard, hDspan⟩ := boundedSpan_small_generators K (B.erase 0) R
    ((Finset.erase_subset _ _).trans hB)
  have hex (d : D) : ∃ i ∈ I, f i = (d : ZMod N) := by
    have hd := Finset.mem_erase.mp (hDB d.property)
    exact Finset.mem_image.mp ((Finset.mem_insert.mp (hcover hd.2)).resolve_left hd.1)
  choose j hj heq using hex
  let J := Finset.univ.image j
  have hJI : J ⊆ I := by
    intro i hi
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hi
    exact hj d
  have hJcard : J.card ≤ D.card := Finset.card_image_le.trans (by simp)
  have hJD : J.image f = D := by
    ext d
    constructor
    · intro hd
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hd
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hi
      rw [heq]
      exact e.property
    · intro hd
      exact Finset.mem_image.mpr ⟨j ⟨d, hd⟩,
        Finset.mem_image.mpr ⟨⟨d, hd⟩, Finset.mem_univ _, rfl⟩, heq ⟨d, hd⟩⟩
  refine ⟨J, hJI, hJcard.trans hDcard, ?_⟩
  intro x hx
  rw [hJD]
  by_cases hx0 : x = 0
  · rw [hx0]
    exact zero_mem_boundedFrequencySpan _ _
  · exact hDspan (Finset.mem_erase.mpr ⟨hx0, hx⟩)

/-- The covered values in each bounded-span row need only a small number
of selected maps, all evaluated inside their original selected pieces. -/
theorem covered_values_small_indices {N m : Nat} [NeZero N]
    (Gamma : ZMod N → Finset (ZMod N)) (r R : Nat)
    (hGamma : ∀ y, (Gamma y).card ≤ r)
    (E : Fin m → Finset (ZMod N)) (L : Fin m → ZMod N → ZMod N) (y : ZMod N) :
    ∃ J : Finset (Fin m), J.card ≤ spanGeneratorBound r R ∧
      (∀ i ∈ J, y ∈ E i ∧ L i y ∈ rowSpanAlphabet Gamma R y) ∧
      covSet (rowSpanAlphabet Gamma R) E L y ⊆
        boundedFrequencySpan (fun k : J.image (fun i => L i y) => (k : ZMod N)) 1 := by
  let U := rowSpanAlphabet Gamma R
  let I := Finset.univ.filter fun i => y ∈ E i ∧ L i y ∈ U y
  have hzero : ∀ t, (0 : ZMod N) ∈ U t := fun t => zero_mem_boundedFrequencySpan _ _
  obtain ⟨J, hJI, hJ, hspan⟩ := exists_small_cover_indices (Gamma y) (covSet U E L y) R I
    (fun i => L i y) (covSet_subset U hzero E L y) (fun x hx => hx)
  refine ⟨J, hJ.trans (spanGeneratorBound_mono_rank (hGamma y) R), ?_, hspan⟩
  intro i hi
  exact (Finset.mem_filter.mp (hJI hi)).2

/-- Small actual index sets give Bohr control of all covered row values.
The maximum with one handles the empty-generator case without division by zero. -/
theorem covered_values_small_bohr {N m : Nat} [NeZero N]
    (Gamma : ZMod N → Finset (ZMod N)) (r R : Nat)
    (hGamma : ∀ y, (Gamma y).card ≤ r)
    (E : Fin m → Finset (ZMod N)) (L : Fin m → ZMod N → ZMod N) (y : ZMod N) :
    ∃ J : Finset (Fin m), J.card ≤ spanGeneratorBound r R ∧
      (∀ i ∈ J, y ∈ E i ∧ L i y ∈ rowSpanAlphabet Gamma R y) ∧
      bohr (J.image (fun i => L i y)) (1 / (16 * (max 1 (spanGeneratorBound r R) : Nat))) ⊆
        bohr (covSet (rowSpanAlphabet Gamma R) E L y) (1 / 16) := by
  obtain ⟨J, hJ, hactive, hspan⟩ := covered_values_small_indices Gamma r R hGamma E L y
  refine ⟨J, hJ, hactive, ?_⟩
  intro x hx
  have hb := bohr_subset_boundedFrequencySpan_bohr (J.image (fun i => L i y)) 1
    (1 / (16 * (max 1 (spanGeneratorBound r R) : Nat))) hx
  simp only [Nat.cast_one] at hb
  have hcard : ((J.image (fun i => L i y)).card : Real) ≤ (max 1 (spanGeneratorBound r R) : Nat) := by
    exact_mod_cast (Finset.card_image_le.trans hJ).trans (Nat.le_max_right _ _)
  have hpos : (0 : Real) < (max 1 (spanGeneratorBound r R) : Nat) := by
    exact_mod_cast (show 0 < max 1 (spanGeneratorBound r R) by omega)
  have hrad : ((J.image (fun i => L i y)).card : Real) * 1 *
      (1 / (16 * (max 1 (spanGeneratorBound r R) : Nat))) ≤ 1 / 16 := by
    rw [mul_one, mul_one_div]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [hcard]
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun q hq => ?_⟩
  exact ((Finset.mem_filter.mp hb).2 q (hspan hq)).trans
    (mul_le_mul_of_nonneg_right hrad (Nat.cast_nonneg N))

end LeanProofs.GowersSzemeredi
