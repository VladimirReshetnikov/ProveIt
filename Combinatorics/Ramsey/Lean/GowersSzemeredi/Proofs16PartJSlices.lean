import GowersSzemeredi.Proofs16PartJInterface
import GowersSzemeredi.Proofs16FreimanSliceExtraction
import GowersSzemeredi.Proofs16GoodDomainTransport
import GowersSzemeredi.Proofs16CubicStructuredCover

/-! Part J: final-coordinate slices covered by a stackable class.

This is the higher-dimensional analogue of `Section16FinalFreimanFamilies`.
Every final-coordinate slice of `B ⊆ Z_N^(d+1)` is covered by `Q` members
of a cubic-stackable class `S` on `Z_N^d`. The module proves three things:

* the property survives passing to subsets;
* any stackable cover of relations in dimension `d` gives a restriction of
  `B`, losing at most `theta*N^(d+1)` points, on which every slice is
  covered (`section16_restrict_final_stackable`);
* such slices discharge the cubic slice provider of the affine lift on any
  common-base good domain, with stacking parameter `Q*q`
  (`Section16FinalStackable.good_domain_slice_provider`).

In dimension one these specialise to the Freiman-family statements. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Every final-coordinate slice is covered by `Q` members of `S`. -/
def Section16FinalStackable {N d : Nat} [NeZero N] (Q : Nat)
    (S : Set (Finset (Point N d) × (Point N d → ZMod N)))
    (B : Finset (Point N (d + 1))) (phi : Point N (d + 1) → ZMod N) : Prop :=
  ∀ t, ∃ D : Fin Q → Finset (Point N d) × (Point N d → ZMod N), (∀ i, D i ∈ S) ∧
    partialGraph (section16FinalCoordinateSection B t) (section16FinalCoordinateRestriction phi t) ⊆
      section16FinsetUnion (fun i => partialGraph (D i).1 (D i).2)

theorem partialGraph_mono {N d : Nat} {B C : Finset (Point N d)} (phi : Point N d → ZMod N)
    (h : C ⊆ B) : partialGraph C phi ⊆ partialGraph B phi := by
  classical
  intro z hz
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
  exact Finset.mem_image.mpr ⟨x, h hx, rfl⟩

theorem section16FinalCoordinateSection_mono {N d : Nat} [NeZero N]
    {B C : Finset (Point N (d + 1))} (h : C ⊆ B) (t : ZMod N) :
    section16FinalCoordinateSection C t ⊆ section16FinalCoordinateSection B t := by
  intro x hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h (Finset.mem_filter.mp hx).2⟩

theorem Section16FinalStackable.mono {N d Q : Nat} [NeZero N]
    {S : Set (Finset (Point N d) × (Point N d → ZMod N))}
    {B C : Finset (Point N (d + 1))} {phi : Point N (d + 1) → ZMod N}
    (h : Section16FinalStackable Q S B phi) (hCB : C ⊆ B) :
    Section16FinalStackable Q S C phi := by
  intro t
  obtain ⟨D, hD, hc⟩ := h t
  exact ⟨D, hD, (partialGraph_mono _ (section16FinalCoordinateSection_mono hCB t)).trans hc⟩

/-- Restrict all final-coordinate slices at once to their stackable covers. -/
theorem section16_restrict_final_stackable {N d Q : Nat} [NeZero N]
    {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (S : Set (Finset (Point N d) × (Point N d → ZMod N)))
    (hcover : ∀ Gamma : Finset (Point N d × ZMod N),
      (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ d →
      RelationProductProperty gamma Gamma →
      ∃ J : Finset (Point N d), (1 - theta) * (N : Real) ^ d ≤ J.card ∧
        ∃ D : Fin Q → Finset (Point N d) × (Point N d → ZMod N), (∀ i, D i ∈ S) ∧
          restrictRelation Gamma J ⊆ section16FinsetUnion (fun i => partialGraph (D i).1 (D i).2))
    (B : Finset (Point N (d + 1))) (phi : Point N (d + 1) → ZMod N)
    (hprod : HasProductProperty B phi gamma) :
    ∃ C : Finset (Point N (d + 1)), C ⊆ B ∧
      (B.card : Real) - theta * (N : Real) ^ (d + 1) ≤ C.card ∧
      Section16FinalStackable Q S C phi := by
  classical
  have hginv : 1 ≤ gamma ^ (-(2 : Int)) := by
    rw [zpow_neg, zpow_ofNat]
    exact (one_le_inv₀ (pow_pos hg 2)).mpr (pow_le_one₀ hg.le hg1)
  have hstep (t : ZMod N) : ∃ C : Finset (Point N d), C ⊆ section16FinalCoordinateSection B t ∧
      ((section16FinalCoordinateSection B t).card : Real) - theta * (N : Real) ^ d ≤ C.card ∧
      ∃ D : Fin Q → Finset (Point N d) × (Point N d → ZMod N), (∀ i, D i ∈ S) ∧
        partialGraph C (section16FinalCoordinateRestriction phi t) ⊆
          section16FinsetUnion (fun i => partialGraph (D i).1 (D i).2) := by
    let Bt := section16FinalCoordinateSection B t
    let phit := section16FinalCoordinateRestriction phi t
    have hs : HasProductProperty Bt phit gamma :=
      hprod.coordinateFace (CoordinateFace.lastSlice t)
    have hBt : (Bt.card : Real) ≤ (N : Real) ^ d := by
      exact_mod_cast (show Bt.card ≤ N ^ d by simpa [Point, ZMod.card] using Finset.card_le_univ Bt)
    have hsize : ((partialGraph Bt phit).card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ d := by
      rw [partialGraph_card]
      exact hBt.trans (le_mul_of_one_le_left (by positivity) hginv)
    obtain ⟨J, hJ, D, hD, hc⟩ := hcover (partialGraph Bt phit) hsize
      (partialGraph_relationProductProperty hs)
    refine ⟨Bt ∩ J, Finset.inter_subset_left, ?_, D, hD, ?_⟩
    · have hsum : ((Bt ∪ J).card : Real) + (Bt ∩ J).card = Bt.card + J.card := by
        exact_mod_cast Finset.card_union_add_card_inter Bt J
      have hunion : ((Bt ∪ J).card : Real) ≤ (N : Real) ^ d := by
        exact_mod_cast (show (Bt ∪ J).card ≤ N ^ d by
          simpa [Point, ZMod.card] using Finset.card_le_univ (Bt ∪ J))
      linarith
    · rw [restrictRelation_partialGraph] at hc
      exact hc
  choose C hsub hmass hfam using hstep
  refine ⟨section16SliceUnion C, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨t, -, hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact (Finset.mem_filter.mp (hsub t hx)).2
  · have hsum := Finset.sum_le_sum (s := Finset.univ)
      (fun t (_ : t ∈ (Finset.univ : Finset (ZMod N))) => hmass t)
    have hBsum : (∑ t, ((section16FinalCoordinateSection B t).card : Real)) = B.card := by
      exact_mod_cast ((section16SliceUnion_card (section16FinalCoordinateSection B)).symm.trans
        (congrArg Finset.card (section16SliceUnion_sections B)))
    have hCsum : (∑ t, ((C t).card : Real)) = (section16SliceUnion C).card := by
      exact_mod_cast (section16SliceUnion_card C).symm
    rw [Finset.sum_sub_distrib, hBsum, hCsum] at hsum
    have hvol : (∑ _t : ZMod N, theta * (N : Real) ^ d) = theta * (N : Real) ^ (d + 1) := by
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      ring
    rwa [hvol] at hsum
  · intro t
    obtain ⟨D, hD, hc⟩ := hfam t
    refine ⟨D, hD, ?_⟩
    rw [section16FinalCoordinateSection_sliceUnion]
    exact hc

/-- A slice of the translated good-domain function lies in the translate of
the corresponding original slice. -/
theorem section16_goodDomain_slice_graph_subset {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N) (H : Finset (Point N k))
    (Y : (h : Point N k) → Finset (Section16CubeElement B h)) (x0 : Point N k) (t : ZMod N) :
    partialGraph (section16FinalCoordinateSection (section16GoodDomain B H Y x0) t)
        (section16FinalCoordinateRestriction (section16PhiOne phi x0) t) ⊆
      (partialGraph (section16FinalCoordinateSection B t)
        (section16FinalCoordinateRestriction phi t)).image (fun w => (w.1 + -x0, w.2)) := by
  classical
  intro z hz
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
  have hv := section16GoodDomain_vertex_mem B H Y x0 (Finset.mem_filter.mp hy).2 (fun _ => true)
  have hb : appendCoordinate (y + x0) t ∈ B := by
    simpa only [section16Init_appendCoordinate, section16Last_appendCoordinate,
      ite_true, ← Pi.add_def, add_comm] using hv
  refine Finset.mem_image.mpr ⟨(y + x0, section16FinalCoordinateRestriction phi t (y + x0)),
    Finset.mem_image.mpr ⟨y + x0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩, rfl⟩, ?_⟩
  refine Prod.ext ?_ ?_
  · show y + x0 + -x0 = y
    abel
  · show section16FinalCoordinateRestriction phi t (y + x0) =
      section16FinalCoordinateRestriction (section16PhiOne phi x0) t y
    unfold section16FinalCoordinateRestriction section16PhiOne
    rw [section16Init_appendCoordinate, section16Last_appendCoordinate]
    congr 2
    funext i
    simp only [Pi.add_apply]
    exact add_comm _ _

/-- **Stackable slices give the cubic slice provider** on every common-base
good domain, with stacking parameter `Q*q`. -/
theorem Section16FinalStackable.good_domain_slice_provider {N k Q q : Nat} [Fact N.Prime]
    {S : Set (Finset (Point N k) × (Point N k → ZMod N))}
    (hS : CubicStackableClass k q S) (hQ : 0 < Q)
    {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    (h : Section16FinalStackable Q S B phi)
    (H : Finset (Point N k)) (Y : (a : Point N k) → Finset (Section16CubeElement B a))
    (x0 : Point N k) :
    Section16SliceProvider (section16GoodDomain B H Y x0) (section16PhiOne phi x0)
      (fun r _ => ((3 * (max 1 r * (Q * q)) : Nat) : Real))
      (fun r => cubicBaseExponent (max 1 r * (Q * q))) := by
  classical
  intro r sample
  choose D hD hc using h
  let m := max 1 r
  have hm : 0 < m := lt_of_lt_of_le Nat.one_pos (le_max_left 1 r)
  let sample' : Fin m → ZMod N := fun i => if hi : (i : Nat) < r then sample ⟨i, hi⟩ else 0
  let E : Fin m × Fin Q → Finset (Point N k) × (Point N k → ZMod N) :=
    fun p => D (sample' p.1) p.2
  let Γ0 := section16FinsetUnion (fun p : Fin m × Fin Q => partialGraph (E p).1 (E p).2)
  have hcardι : 0 < Fintype.card (Fin m × Fin Q) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    exact Nat.mul_pos hm hQ
  have hML0 := hS.cover_fintype hcardι E (fun p => hD _ _) Γ0 (fun z hz => hz)
  have hcard : Fintype.card (Fin m × Fin Q) * q = max 1 r * (Q * q) := by
    simp only [Fintype.card_prod, Fintype.card_fin, m, Nat.mul_assoc]
  rw [hcard] at hML0
  apply (hML0.translate (-x0)).subset
  intro z hz
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hz
  have hz' := section16_goodDomain_slice_graph_subset B phi H Y x0 (sample i) hi
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz'
  obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp (hc (sample i) hw)
  let i' : Fin m := ⟨i, lt_of_lt_of_le i.isLt (le_max_right 1 r)⟩
  have hsi : sample' i' = sample i := by
    simp only [sample', i', dif_pos i.isLt]
  refine Finset.mem_image.mpr ⟨w, Finset.mem_biUnion.mpr ⟨(i', j), Finset.mem_univ _, ?_⟩, rfl⟩
  simpa only [E, hsi] using hj

end LeanProofs.GowersSzemeredi
