import GowersSzemeredi.Proofs16BaseCaseExtraction
import GowersSzemeredi.Proofs16CubicCoverControls

/-! Loss-independent Freiman families from the one-dimensional product property.
The greedy extraction chooses the good domain before any inner cover loss
is requested. Pad its family to an explicit bound depending only on the
original density parameters, then apply the simultaneous cubic cover. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open BaseCase

def section16BaseFamilyBound (gamma theta : Real) : Nat :=
  max 1 ⌊gamma ^ (-(2 : Int)) / lemma163Alpha gamma theta⌋₊

theorem section16BaseFamilyBound_pos (gamma theta : Real) :
    0 < section16BaseFamilyBound gamma theta := by
  unfold section16BaseFamilyBound
  omega

/-- A single large base domain is covered by a uniformly bounded family of
Freiman graphs, independently of any subsequently requested cover loss. -/
theorem section16_extract_uniform_base_family {N : Nat} [Fact N.Prime]
    {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1)
    (Gamma : Finset (Point N 1 × ZMod N))
    (hsize : (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * N)
    (hproduct : RelationProductProperty gamma Gamma) :
    ∃ (J : Finset (Point N 1))
      (D : Fin (section16BaseFamilyBound gamma theta) → Finset (Point N 1))
      (f : Fin (section16BaseFamilyBound gamma theta) → Point N 1 → ZMod N),
      (1 - theta) * (N : Real) ≤ J.card ∧
      (∀ i, FreimanHom 8 (pointOneDomain (D i)) (pointOneMap (f i))) ∧
      restrictRelation Gamma J ⊆ section16FinsetUnion (fun i => partialGraph (D i) (f i)) := by
  classical
  let E := section16_extract_base_family gamma theta hg hg1 ht ht1
    (Fact.out : N.Prime) Gamma hsize hproduct
  have hcount : E.q ≤ section16BaseFamilyBound gamma theta := by
    have hreal : (E.q : Real) ≤ gamma ^ (-(2 : Int)) / lemma163Alpha gamma theta :=
      (le_div_iff₀ (lemma163Alpha_pos hg ht)).mpr E.count
    exact (Nat.le_floor hreal).trans (le_max_right _ _)
  let D : Fin (section16BaseFamilyBound gamma theta) → Finset (Point N 1) :=
    fun i => if h : i.val < E.q then E.B ⟨i.val, h⟩ else ∅
  let f : Fin (section16BaseFamilyBound gamma theta) → Point N 1 → ZMod N :=
    fun i => if h : i.val < E.q then E.phi ⟨i.val, h⟩ else fun _ => 0
  refine ⟨E.J, D, f, E.Jcard, ?_, ?_⟩
  · intro i
    by_cases hi : i.val < E.q
    · simpa only [D, f, dif_pos hi] using E.freiman ⟨i.val, hi⟩
    · simp only [D, f, dif_neg hi, pointOneDomain, Finset.map_empty, FreimanHom, Finset.coe_empty]
      exact isAddFreimanHom_empty
  · intro z hz
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp (E.cover hz)
    let j : Fin (section16BaseFamilyBound gamma theta) := ⟨i.val, lt_of_lt_of_le i.isLt hcount⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨j, Finset.mem_univ _, ?_⟩
    simpa only [D, f, j, dif_pos i.isLt] using hi

/-- Strengthened one-dimensional cover: a domain chosen once has graph
count independent of the inner loss and an explicit cubic width exponent. -/
theorem section16_product_relation_cubic_cover {N : Nat} [Fact N.Prime]
    {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1)
    (Gamma : Finset (Point N 1 × ZMod N))
    (hsize : (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * N)
    (hproduct : RelationProductProperty gamma Gamma) :
    ∃ J : Finset (Point N 1), (1 - theta) * (N : Real) ≤ J.card ∧
      MultiplyLinearWith
        (fun _ => ((3 * section16BaseFamilyBound gamma theta : Nat) : Real))
        (cubicBaseExponent (section16BaseFamilyBound gamma theta))
        (restrictRelation Gamma J) := by
  obtain ⟨J, D, f, hJ, hfreiman, hcover⟩ :=
    section16_extract_uniform_base_family hg hg1 ht ht1 Gamma hsize hproduct
  exact ⟨J, hJ, section16_freiman_family_cubic_cover
    (section16BaseFamilyBound_pos gamma theta) D f hfreiman _ hcover⟩

end LeanProofs.GowersSzemeredi
