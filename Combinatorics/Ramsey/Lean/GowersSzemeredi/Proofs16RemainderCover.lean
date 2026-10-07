import GowersSzemeredi.Proofs16VertexCovers
import GowersSzemeredi.Proofs16WeightedSumCovers

/-! The actual structured pair supplies the remainder-cover premise of
Lemma 16.9 with exactly its stated parameter. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Sum the signed non-top vertex covers. There are exactly `2^k - 1`
summands, so the resulting parameter is precisely `section16Lemma9R`. -/
theorem Section16StructuredPair.good_domain_remainder_cover
    {N k : Nat} [NeZero N] [Fact N.Prime] {theta gamma : Real}
    {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    (h : Section16StructuredPair theta gamma B phi) (hk : 1 ≤ k)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (H : Finset (Point N k)) (Y : (a : Point N k) → Finset (Section16CubeElement B a))
    (x0 : Point N k) :
    MultiplyLinearFunction gamma (section16Lemma9R theta gamma k)
      (section16GoodDomain B H Y x0) (section16PhiRemainder phi x0) := by
  classical
  let E := Finset.univ.filter (fun e : Fin k → Bool => e ≠ fun _ => true)
  have hE : E.card = 2 ^ k - 1 := by
    have heq : E = Finset.univ.erase (fun _ : Fin k => true) := by
      ext e
      simp [E]
    rw [heq, Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp
  have hfalse : (fun _ : Fin k => false) ∈ E := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro he
    have hh := congrFun he ⟨0, by omega⟩
    contradiction
  letI : Nonempty E := ⟨⟨fun _ => false, hfalse⟩⟩
  let r := gamma ^ (-(2 : Int)) * multipleS ((2 : Real) ^ (-(k + 2 : Real)) * theta) gamma k
  let D := section16GoodDomain B H Y x0
  let psi : E → Point N (k + 1) → ZMod N := fun e z =>
    -((-1 : ZMod N) ^ (k + boolWeight e.val)) * section16TranslatedVertex phi x0 e.val z
  have hr : 1 ≤ r := by
    have hh := (section16_face_parameter_lift_reserve k ht ht1 hg hg1).1
    change 1 ≤ gamma ^ (-(2 : Int)) * multipleS ((2 : Real) ^ (-(k + 2 : Real)) * theta) gamma k
    linarith
  have hpsi : ∀ e, MultiplyLinearFunction gamma r D (psi e) := by
    intro e
    exact (h.good_domain_vertex_cover ht ht1 hg hg1 H Y x0 e.val
      (Finset.mem_filter.mp e.property).2).const_mul _
  have hp := multiplyLinearFunction_fintype_sum gamma r hr D psi hpsi
  have hparam : (Fintype.card E : Real) * r = section16Lemma9R theta gamma k := by
    rw [Fintype.card_coe, hE]
    exact (mul_assoc _ _ _).symm
  have hfun : (fun z => ∑ e, psi e z) = section16PhiRemainder phi x0 := by
    funext z
    change (∑ e : E, -((-1 : ZMod N) ^ (k + boolWeight e.val)) *
      section16TranslatedVertex phi x0 e.val z) = _
    rw [Finset.sum_coe_sort E (fun e => -((-1 : ZMod N) ^ (k + boolWeight e)) *
      section16TranslatedVertex phi x0 e z)]
    simp only [neg_mul, Finset.sum_neg_distrib]
    rfl
  rw [hparam, hfun] at hp
  exact hp

end LeanProofs.GowersSzemeredi
