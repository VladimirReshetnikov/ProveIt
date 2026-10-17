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
    fun j i x => mu j i (x + -t), ?_, ?_, ?_, fun j => (hproper j).translate t,
    hq, ?_, fun j i => (hmu j i).translate (-t), ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    simpa using (Box.translate_mem_carrier (P.translate (-t)) t y).mpr (hH hy)
  · rw [Finset.card_image_of_injective _ (add_left_injective t)]
    simpa using hHcard
  · simpa using hpart.translate t
  · intro j
    simpa using hw j
  · intro j x hx hh y hxy
    obtain ⟨⟨a, b⟩, hab, heq⟩ := Finset.mem_image.mp hxy
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    have haQ := (Box.translate_mem_carrier (Q j) t a).mp hx
    have haH := (add_left_injective t).mem_finset_image.mp hh
    obtain ⟨i, hi⟩ := hcover j a haQ haH b hab
    exact ⟨i, by simpa using hi⟩

end LeanProofs.GowersSzemeredi
