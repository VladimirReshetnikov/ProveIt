import GowersSzemeredi.Proofs16CubicAllScaleCover
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Logic.Equiv.Fintype

/-! A genuine dimension-two graph piece with explicit all-box controls.
Both the spectrum and slice inputs are constructed from the preceding
extractions. The result retains a positive density and lies in the original
graph. Comparison with the manuscript's prescribed controls remains separate.

`section16CubicTwoExponent`, `section16CubicTwoGraphBound`,
`section16_cubic_product_graph_piece` and `section16_cubic_structured_piece` are
in `Proofs16CubicStructuredCoverSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem MultiplyLinearWith.translate {N k : Nat} [NeZero N] [Fact N.Prime]
    {Qb Eb : Real → Real} {Gamma : Finset (Point N k × ZMod N)}
    (h : MultiplyLinearWith Qb Eb Gamma) (t : Point N k) :
    MultiplyLinearWith Qb Eb (Gamma.image (fun z => (z.1 + t, z.2))) := by
  intro theta ht ht1 P hP
  obtain ⟨M, q, H, Q, mu, hH, hHcard, hpart, hproper, hq, hw, hmu, hcover⟩ :=
    h theta ht ht1 (P.translate (-t)) (hP.translate (-t))
  refine ⟨M, q, H.image (fun x => x + t), fun j => (Q j).translate t,
    fun j i x => mu j i (x + -t), fun x hx => ?_,
    by rw [Finset.card_image_of_injective _ (add_left_injective t)]; simpa using hHcard,
    by simpa using hpart.translate t, fun j => (hproper j).translate t, hq,
    fun j => by simpa using hw j, fun j i => (hmu j i).translate (-t), fun j x hx hh y hxy => ?_⟩
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    simpa using (Box.translate_mem_carrier (P.translate (-t)) t y).mpr (hH hy)
  · obtain ⟨⟨a, b⟩, hab, heq⟩ := Finset.mem_image.mp hxy
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    obtain ⟨i, hi⟩ := hcover j a ((Box.translate_mem_carrier (Q j) t a).mp hx)
      ((add_left_injective t).mem_finset_image.mp hh) b hab
    exact ⟨i, by simpa using hi⟩

end LeanProofs.GowersSzemeredi
