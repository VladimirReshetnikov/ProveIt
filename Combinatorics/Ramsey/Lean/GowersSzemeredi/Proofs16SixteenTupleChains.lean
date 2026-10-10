import GowersSzemeredi.Proofs16ProgressionExactEightRelations

/-! Closed chains for eight pairs / sixteen endpoints. Their prefix vertices
remain in the original progression. Only eight anchor spectra are needed:
the ninth vertex equals the first when the tuple is additive. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open scoped BigOperators

abbrev PairedSixteenTuple (N : Nat) := Fin 8 → ZMod N × ZMod N

def pairedSixteenIndex {N : Nat} (q : PairedSixteenTuple N) : ZMod N :=
  ∑ i, ((q i).1-(q i).2)

def pairedSixteenSpectrum {N : Nat} (T : ZMod N → Finset (ZMod N))
    (q : PairedSixteenTuple N) : Finset (ZMod N) :=
  Finset.univ.biUnion fun i => T (q i).1 ∪ T (q i).2

def pairedSixteenDefect {N : Nat} (L : ZMod N → ZMod N → ZMod N)
    (q : PairedSixteenTuple N) (y : ZMod N) : ZMod N :=
  ∑ i, (L (q i).1 y-L (q i).2 y)

def pairedSixteenShift {N : Nat} (q : PairedSixteenTuple N) : Fin 9 → ZMod N :=
  ![0,((q 0).1-(q 0).2),((q 0).1-(q 0).2)+((q 1).1-(q 1).2),((q 0).1-(q 0).2)+((q 1).1-(q 1).2)+((q 2).1-(q 2).2),((q 0).1-(q 0).2)+((q 1).1-(q 1).2)+((q 2).1-(q 2).2)+((q 3).1-(q 3).2),((q 0).1-(q 0).2)+((q 1).1-(q 1).2)+((q 2).1-(q 2).2)+((q 3).1-(q 3).2)+((q 4).1-(q 4).2),((q 0).1-(q 0).2)+((q 1).1-(q 1).2)+((q 2).1-(q 2).2)+((q 3).1-(q 3).2)+((q 4).1-(q 4).2)+((q 5).1-(q 5).2),((q 0).1-(q 0).2)+((q 1).1-(q 1).2)+((q 2).1-(q 2).2)+((q 3).1-(q 3).2)+((q 4).1-(q 4).2)+((q 5).1-(q 5).2)+((q 6).1-(q 6).2),((q 0).1-(q 0).2)+((q 1).1-(q 1).2)+((q 2).1-(q 2).2)+((q 3).1-(q 3).2)+((q 4).1-(q 4).2)+((q 5).1-(q 5).2)+((q 6).1-(q 6).2)+((q 7).1-(q 7).2)]

def pairedSixteenShiftWord {N : Nat} (q : PairedSixteenTuple N) (i : Fin 9) : Fin 16 → ZMod N :=
  ![(if (0 : Fin 9) < i then (q 0).1 else 0),(if (0 : Fin 9) < i then -(q 0).2 else 0),(if (1 : Fin 9) < i then (q 1).1 else 0),(if (1 : Fin 9) < i then -(q 1).2 else 0),(if (2 : Fin 9) < i then (q 2).1 else 0),(if (2 : Fin 9) < i then -(q 2).2 else 0),(if (3 : Fin 9) < i then (q 3).1 else 0),(if (3 : Fin 9) < i then -(q 3).2 else 0),(if (4 : Fin 9) < i then (q 4).1 else 0),(if (4 : Fin 9) < i then -(q 4).2 else 0),(if (5 : Fin 9) < i then (q 5).1 else 0),(if (5 : Fin 9) < i then -(q 5).2 else 0),(if (6 : Fin 9) < i then (q 6).1 else 0),(if (6 : Fin 9) < i then -(q 6).2 else 0),(if (7 : Fin 9) < i then (q 7).1 else 0),(if (7 : Fin 9) < i then -(q 7).2 else 0)]

/-- The sixteen signed word entries are exactly the selected prefix. -/
theorem paired_sixteen_shift_word_sum {N : Nat} (q : PairedSixteenTuple N) (i : Fin 9) :
    ∑ j, pairedSixteenShiftWord q i j = pairedSixteenShift q i := by
  fin_cases i <;> simp [pairedSixteenShiftWord, pairedSixteenShift, Fin.sum_univ_succ] <;> ring

/-- Every prefix is in the full parent progression when endpoints are in
its 1/256 shrinking. No dense-core selection is required. -/
theorem paired_sixteen_chain_mem {N : Nat} (Q : CenteredProgression N) (q : PairedSixteenTuple N)
    (hq : ∀ j, (q j).1 ∈ (centeredProgressionShrink Q 256).carrier ∧
      (q j).2 ∈ (centeredProgressionShrink Q 256).carrier) (i : Fin 9) :
    pairedSixteenShift q i ∈ Q.carrier := by
  have h0 : (0 : ZMod N) ∈ (centeredProgressionShrink Q 256).carrier :=
    (centered_progression_mem_iff _ 0).mpr ⟨fun _ => 0, by simp, by simp⟩
  have hneg : ∀ j, -(q j).2 ∈ (centeredProgressionShrink Q 256).carrier :=
    fun j => cyclic_centered_progression_neg_mem _ (hq j).2
  have hword : ∀ j, pairedSixteenShiftWord q i j ∈ (centeredProgressionShrink Q 256).carrier := by
    intro j
    fin_cases j <;> dsimp [pairedSixteenShiftWord] <;> split_ifs <;>
      first | exact (hq 0).1 | exact hneg 0 | exact (hq 1).1 | exact hneg 1 |
        exact (hq 2).1 | exact hneg 2 | exact (hq 3).1 | exact hneg 3 |
        exact (hq 4).1 | exact hneg 4 | exact (hq 5).1 | exact hneg 5 |
        exact (hq 6).1 | exact hneg 6 | exact (hq 7).1 | exact hneg 7 | exact h0
  have hz : (0 : ZMod N) ∈ (centeredProgressionResize Q (fun _ => 0)).carrier :=
    (centered_progression_mem_iff _ 0).mpr ⟨fun _ => 0, by simp, by simp⟩
  have h := centered_progression_translated_sum_mem Q (fun j => Q.radius j/256)
    (fun _ => 0) Q.radius (fun j => by omega) 0 (pairedSixteenShiftWord q i) hz hword
  have hresize : centeredProgressionResize Q Q.radius = Q := by cases Q; rfl
  rw [hresize] at h
  simpa only [zero_add, paired_sixteen_shift_word_sum] using h

/-- Each adjacent chain step is the corresponding endpoint difference. -/
theorem paired_sixteen_chain_step {N : Nat} (q : PairedSixteenTuple N) (i : Fin 8) :
    (q i).1-(q i).2 = pairedSixteenShift q i.succ-pairedSixteenShift q i.castSucc := by
  fin_cases i <;> simp [pairedSixteenShift]

theorem paired_sixteen_chain_closed {N : Nat} (q : PairedSixteenTuple N)
    (hadd : pairedSixteenIndex q = 0) : pairedSixteenShift q (Fin.last 8) = pairedSixteenShift q 0 := by
  have hi : pairedSixteenShift q (Fin.last 8) = pairedSixteenIndex q := by
    dsimp only [pairedSixteenShift, pairedSixteenIndex]
    simp [Fin.sum_univ_succ]
    ring
  rw [hi, hadd]
  rfl

/-- The finite telescoping identity used by the map chain. -/
theorem fin_eight_chain_telescope {G : Type*} [AddCommGroup G] (F : Fin 9 → G) :
    (∑ i : Fin 8, (F i.succ-F i.castSucc)) = F (Fin.last 8)-F 0 := by
  simp [Fin.sum_univ_succ]
  abel

/-- The eight quadruple defects telescope to the sixteen-endpoint defect. -/
theorem paired_sixteen_chain_defect {N : Nat} (L : ZMod N → ZMod N → ZMod N)
    (q : PairedSixteenTuple N) (hadd : pairedSixteenIndex q = 0) (y : ZMod N) :
    (∑ i : Fin 8, columnQuadDefect L (q i).1 (q i).2
      (pairedSixteenShift q i.succ) (pairedSixteenShift q i.castSucc) y) = pairedSixteenDefect L q y := by
  have he : ∀ i : Fin 8, columnQuadDefect L (q i).1 (q i).2
      (pairedSixteenShift q i.succ) (pairedSixteenShift q i.castSucc) y =
      (L (q i).1 y-L (q i).2 y)-
        (L (pairedSixteenShift q i.succ) y-L (pairedSixteenShift q i.castSucc) y) := by
    intro i
    dsimp only [columnQuadDefect]
    ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib, fin_eight_chain_telescope (fun i => L (pairedSixteenShift q i) y)]
  rw [paired_sixteen_chain_closed q hadd, sub_self, sub_zero]
  rfl

theorem mem_paired_sixteen_spectrum_bohr {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (q : PairedSixteenTuple N) (rho : Real) (y : ZMod N) :
    y ∈ bohr (pairedSixteenSpectrum T q) rho ↔
      ∀ i, y ∈ bohr (T (q i).1) rho ∧ y ∈ bohr (T (q i).2) rho := by
  constructor
  · intro hy i
    constructor
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun t ht => ?_⟩
      exact (Finset.mem_filter.mp hy).2 t (Finset.mem_biUnion.mpr
        ⟨i,Finset.mem_univ _,Finset.mem_union_left _ ht⟩)
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun t ht => ?_⟩
      exact (Finset.mem_filter.mp hy).2 t (Finset.mem_biUnion.mpr
        ⟨i,Finset.mem_univ _,Finset.mem_union_right _ ht⟩)
  · intro hy
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun t ht => ?_⟩
    obtain ⟨i,_,ht⟩ := Finset.mem_biUnion.mp ht
    rcases Finset.mem_union.mp ht with ht | ht
    · exact (Finset.mem_filter.mp (hy i).1).2 t ht
    · exact (Finset.mem_filter.mp (hy i).2).2 t ht

theorem paired_sixteen_spectrum_card {N d : Nat} (T : ZMod N → Finset (ZMod N))
    (q : PairedSixteenTuple N) (hT : ∀ i, (T (q i).1).card ≤ d ∧ (T (q i).2).card ≤ d) :
    (pairedSixteenSpectrum T q).card ≤ 16*d := by
  apply Finset.card_biUnion_le.trans
  calc (∑ i : Fin 8, (T (q i).1 ∪ T (q i).2).card) ≤ ∑ _i : Fin 8, 2*d :=
      Finset.sum_le_sum fun i _ => (Finset.card_union_le _ _).trans (by
        have := (hT i).1
        have := (hT i).2
        omega)
    _ = _ := by simp [Fintype.card_fin]; ring

theorem paired_sixteen_defect_freiman {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (q : PairedSixteenTuple N) (rho : Real)
    (hL : ∀ i, IsFreimanLinearOn (bohr (T (q i).1) rho) (L (q i).1) ∧
      IsFreimanLinearOn (bohr (T (q i).2) rho) (L (q i).2)) :
    IsFreimanLinearOn (bohr (pairedSixteenSpectrum T q) rho) (pairedSixteenDefect L q) := by
  intro a b c e ha hb hc he hadd
  have hm := fun y hy => (mem_paired_sixteen_spectrum_bohr T q rho y).mp hy
  have hf : ∀ i, (L (q i).1 a-L (q i).2 a)+(L (q i).1 b-L (q i).2 b) =
      (L (q i).1 c-L (q i).2 c)+(L (q i).1 e-L (q i).2 e) := by
    intro i
    have ea := (hL i).1 a b c e (hm a ha i).1 (hm b hb i).1 (hm c hc i).1 (hm e he i).1 hadd
    have eb := (hL i).2 a b c e (hm a ha i).2 (hm b hb i).2 (hm c hc i).2 (hm e he i).2 hadd
    linear_combination ea-eb
  dsimp only [pairedSixteenDefect]
  rw [←Finset.sum_add_distrib, ←Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => hf i

end LeanProofs.GowersSzemeredi
