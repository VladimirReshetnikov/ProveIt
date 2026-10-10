import GowersSzemeredi.Proofs16PairedColumnImages
import GowersSzemeredi.Proofs16CommonCoreTranslation

/-! Extend all-quadruple image compatibility to additive eight-tuples on
a small shrinking. Shared chain anchors are selected in the dense core;
their spectra are removed by the linear-cap theorem at half radius. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- All eight-tuple endpoint defects are controlled by four telescoping
core quadruples. The core complement must be small enough for four anchors. -/
theorem paired_eight_image_extension {N d H : Nat} [NeZero N]
    (Q : CenteredProgression N) (S : Finset (ZMod N))
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    {rho : Real} (hrho : 0 < rho) (hH : 0 < H)
    (hsmall : 4*((centeredProgressionShrink Q 16).carrier \ S).card <
      (centeredProgressionShrink Q 32).carrier.card)
    (hT : ∀ x ∈ S, (T x).card ≤ d)
    (hL : ∀ x ∈ S, IsFreimanLinearOn (bohr (T x) rho) (L x))
    (hquad : ∀ a b c e : ZMod N, a ∈ S → b ∈ S → c ∈ S → e ∈ S → a-b = c-e →
      ColumnQuadImageRelation T L rho H a b c e)
    (q : PairedColumnTuple N)
    (hq : ∀ i, (q i).1 ∈ S ∩ (centeredProgressionShrink Q 256).carrier ∧
      (q i).2 ∈ S ∩ (centeredProgressionShrink Q 256).carrier)
    (hadd : pairedColumnIndex q = 0) :
    PairedColumnImageRelation T L (rho/2)
      (H^4*refinementKernelCap (8*d) (4*d) rho rho) q := by
  have hqtiny : ∀ i, (q i).1 ∈ (centeredProgressionShrink Q 256).carrier ∧
      (q i).2 ∈ (centeredProgressionShrink Q 256).carrier :=
    fun i => ⟨(Finset.mem_inter.mp (hq i).1).2,(Finset.mem_inter.mp (hq i).2).2⟩
  have hqS : ∀ i, (q i).1 ∈ S ∧ (q i).2 ∈ S :=
    fun i => ⟨(Finset.mem_inter.mp (hq i).1).1,(Finset.mem_inter.mp (hq i).2).1⟩
  obtain ⟨u,hu,hchain⟩ := exists_common_translation_into_core
    (centeredProgressionShrink Q 32).carrier (centeredProgressionShrink Q 16).carrier S
    (pairedTupleShift q) (fun u hu i => paired_tuple_chain_mem Q q hqtiny hu i)
    (by simpa only [Fintype.card_fin] using hsmall)
  let A := pairedColumnSpectrum T q
  let U := Finset.univ.biUnion fun i : Fin 4 => T (u+pairedTupleShift q i)
  let D := bohr (A ∪ U) rho
  have hmem : ∀ y ∈ D,
      (∀ i, y ∈ bohr (T (q i).1) rho ∧ y ∈ bohr (T (q i).2) rho) ∧
      (∀ i, y ∈ bohr (T (u+pairedTupleShift q i)) rho) := by
    intro y hy
    dsimp only [D] at hy
    rw [bohr_union] at hy
    refine ⟨(mem_paired_column_spectrum_bohr T q rho y).mp (Finset.mem_inter.mp hy).1, ?_⟩
    intro i
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun t ht => ?_⟩
    exact (Finset.mem_filter.mp (Finset.mem_inter.mp hy).2).2 t
      (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,ht⟩)
  let defects := fun i : Fin 4 => columnQuadDefect L (q i).1 (q i).2
    (u+pairedTupleShift q (i+1)) (u+pairedTupleShift q i)
  have himages : ∀ i, (D.image (defects i)).card ≤ H := by
    intro i
    have h := hquad (q i).1 (q i).2 (u+pairedTupleShift q (i+1)) (u+pairedTupleShift q i)
      (hqS i).1 (hqS i).2 (hchain (i+1)) (hchain i) (paired_chain_quad_additive q hadd u i)
    apply (image_card_le_of_eq_on_subset D
      (columnQuadCommonDomain T rho (q i).1 (q i).2 (u+pairedTupleShift q (i+1)) (u+pairedTupleShift q i))
      _ _ ?_ (fun _ _ => rfl)).trans h
    intro y hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hmem y hy).1 i |>.1,
      (hmem y hy).1 i |>.2,(hmem y hy).2 (i+1),(hmem y hy).2 i⟩
  have hsum : (D.image (fun y => ∑ i, defects i y)).card ≤ H^4 := by
    have h := image_sum_defects_card_le D defects (fun _ => H) himages
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h
  have himage : (D.image (pairedColumnDefect L q)).card ≤ H^4 := by
    apply (image_card_le_of_eq_on_subset D D _ _ (fun _ h => h) ?_).trans hsum
    intro y _
    exact paired_column_chain_defect L q u y
  have hA : A.card ≤ 8*d := paired_column_spectrum_card T q
    (fun i => ⟨hT _ (hqS i).1,hT _ (hqS i).2⟩)
  have hU : U.card ≤ 4*d := by
    apply Finset.card_biUnion_le.trans
    calc (∑ i : Fin 4, (T (u+pairedTupleShift q i)).card) ≤ ∑ _i : Fin 4, d :=
        Finset.sum_le_sum fun i _ => hT _ (hchain i)
      _ = _ := by simp
  exact freiman_image_remove_frequencies_nat A U (pairedColumnDefect L q) hrho hA hU
    (pow_pos hH _) (paired_column_defect_freiman T L q rho
      (fun i => ⟨hL _ (hqS i).1,hL _ (hqS i).2⟩)) himage

end LeanProofs.GowersSzemeredi
