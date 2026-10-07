import GowersSzemeredi.Proofs16FiniteAlphabetFibres
import GowersSzemeredi.Proofs16FibreGeometry

/-! Transport the finite-alphabet obstruction to the actual multilinear
maps and appended-coordinate domains used in Section 16. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem finiteAlphabet_multilinear_cover_bound {N k q : Nat} [NeZero N] [Fact N.Prime]
    (U : Finset (Point N k)) (V S : Finset (ZMod N)) (H : Finset (Point N (k + 1)))
    (f : ZMod N → ZMod N) (hf : ∀ y ∈ V, f y ∈ S)
    (mu : Fin q → Point N (k + 1) → ZMod N) (hmu : ∀ i, IsMultilinear (mu i))
    (beta : Real) (hbeta : 0 ≤ beta)
    (hbalanced : ∀ c : ZMod N, ((V.filter (fun y => f y = c)).card : Real) ≤ beta * V.card)
    (hsub : H ⊆ lastProductSet U V)
    (hcover : ∀ x ∈ H, ∃ i : Fin q, f (section16Last x) = mu i x) :
    (H.card : Real) ≤ U.card * q * (beta * V.card + S.card) := by
  classical
  let T := (U.product V).filter (fun p => appendCoordinate p.1 p.2 ∈ H)
  have hTsub : T ⊆ U.product V := Finset.filter_subset _ _
  have hi : Function.Injective (fun p : Point N k × ZMod N => appendCoordinate p.1 p.2) := by
    intro p p' he
    apply Prod.ext
    · have hh := congrArg section16Init he
      simpa only [section16Init_appendCoordinate] using hh
    · have hh := congrArg section16Last he
      simpa only [section16Last_appendCoordinate] using hh
  have happend (x : Point N (k + 1)) : appendCoordinate (section16Init x) (section16Last x) = x := by
    rw [appendCoordinate_eq_snoc]
    exact Fin.snoc_init_self x
  have he : T.image (fun p => appendCoordinate p.1 p.2) = H := by
    ext x
    constructor
    · intro hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hp).2
    · intro hx
      have hm := (Finset.mem_filter.mp (hsub hx)).2
      refine Finset.mem_image.mpr ⟨(section16Init x, section16Last x), ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_product.mpr hm, ?_⟩
        rwa [happend]
      · exact happend x
  have hcard : T.card = H.card := by
    rw [← he, Finset.card_image_of_injective _ hi]
  choose a b hab using fun (x : Point N k) (i : Fin q) => (hmu i).linearOn_last_fibre x
  have hTcover : ∀ p ∈ T, ∃ i : Fin q, f p.2 = a p.1 i * p.2 + b p.1 i := by
    intro p hp
    obtain ⟨i, hi⟩ := hcover (appendCoordinate p.1 p.2) (Finset.mem_filter.mp hp).2
    rw [section16Last_appendCoordinate] at hi
    exact ⟨i, hi.trans (hab p.1 i p.2 (Finset.mem_univ _))⟩
  have ht := finiteAlphabet_fibrewise_affine_cover U V S T f hf a b beta hbeta hbalanced hTsub hTcover
  rwa [hcard] at ht

theorem finiteAlphabet_multilinear_cover_five_sixteenths {N k q : Nat} [NeZero N] [Fact N.Prime]
    (U : Finset (Point N k)) (V S : Finset (ZMod N)) (H : Finset (Point N (k + 1)))
    (f : ZMod N → ZMod N) (hf : ∀ y ∈ V, f y ∈ S)
    (mu : Fin q → Point N (k + 1) → ZMod N) (hmu : ∀ i, IsMultilinear (mu i))
    (beta : Real) (hbeta : 0 ≤ beta)
    (hbalanced : ∀ c : ZMod N, ((V.filter (fun y => f y = c)).card : Real) ≤ beta * V.card)
    (hsub : H ⊆ lastProductSet U V)
    (hcover : ∀ x ∈ H, ∃ i : Fin q, f (section16Last x) = mu i x)
    (hsmall : (q : Real) * beta ≤ 9 / 32)
    (hwidth : (q : Real) * S.card ≤ (V.card : Real) / 32) :
    (H.card : Real) ≤ (5 / 16 : Real) * U.card * V.card := by
  have hc := finiteAlphabet_multilinear_cover_bound U V S H f hf mu hmu beta hbeta hbalanced hsub hcover
  have hm := mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg V.card)
  have hr : (q : Real) * (beta * V.card + S.card) ≤ (5 / 16 : Real) * V.card := by
    nlinarith only [hm, hwidth]
  have ht := mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg U.card)
  nlinarith only [hc, ht]

end LeanProofs.GowersSzemeredi
