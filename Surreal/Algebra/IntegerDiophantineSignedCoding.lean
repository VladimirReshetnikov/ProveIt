import Surreal.Algebra.IntegerDiophantineImages
import Surreal.Algebra.NaturalDiophantineIntegers
import Surreal.Algebra.IntegerDiophantineEnumeration

/-!
# Signed natural coding for integer Diophantine classification

The sign-coding reduction in the proof of `odg:def:thm:ce`. A doubled natural
tuple represents an integer tuple by coordinatewise subtraction. This map
and its canonical section are primitive recursive. Signed preimages preserve
and reflect computable enumerability, and a natural Diophantine presentation
of such a preimage gives an integer presentation of the original set.
-/

namespace Surreal.IntegerDiophantine
open MvPolynomial
noncomputable section

variable {n : ℕ}

/-- Decode two natural blocks as positive minus negative coordinates. -/
def signedDecode (x : Fin (n + n) → ℕ) : Fin n → ℤ :=
  fun j => (x (Fin.castAdd n j) : ℤ) - (x (Fin.natAdd n j) : ℤ)

/-- The canonical positive/negative-part representation. -/
def signedEncode (z : Fin n → ℤ) : Fin (n + n) → ℕ :=
  Fin.addCases (fun j => (z j).toNat) (fun j => (-z j).toNat)

/-- Decoding the canonical representation recovers every integer coordinate. -/
@[simp] theorem signedDecode_encode (z : Fin n → ℤ) : signedDecode (signedEncode z) = z := by
  funext j
  simpa only [signedDecode, signedEncode, Fin.addCases_left, Fin.addCases_right] using
    Int.toNat_sub_toNat_neg (z j)

/-- Every integer tuple has a natural signed representation, including the empty tuple. -/
theorem signedDecode_surjective : Function.Surjective (@signedDecode n) :=
  fun z => ⟨signedEncode z, signedDecode_encode z⟩

/-- Signed decoding is primitive recursive under Mathlib's standard tuple and integer encodings. -/
theorem signedDecode_primrec : Primrec (@signedDecode n) := by
  apply Primrec.fin_curry.mpr
  apply Primrec₂.swap
  apply Primrec.fin_curry₁.mpr
  intro j
  exact IntegerArithmeticComputability.difference_primrec.comp
    (Primrec.fin_app.comp Primrec.id (Primrec.const (Fin.castAdd n j)))
    (Primrec.fin_app.comp Primrec.id (Primrec.const (Fin.natAdd n j))) |>.of_eq
      (fun x => by simp only [signedDecode, IntegerArithmeticComputability.difference_eq, id_eq])

/-- Taking the canonical positive and negative parts is primitive recursive. -/
theorem signedEncode_primrec : Primrec (@signedEncode n) := by
  apply Primrec.fin_curry.mpr
  apply Primrec₂.swap
  apply Primrec.fin_curry₁.mpr
  intro j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · exact IntegerArithmeticComputability.toNat_primrec.comp
      (Primrec.fin_app.comp Primrec.id (Primrec.const i)) |>.of_eq
        (fun z => by simp only [signedEncode, Fin.addCases_left, id_eq])
  · exact IntegerArithmeticComputability.negativePart_primrec.comp
      (Primrec.fin_app.comp Primrec.id (Primrec.const i)) |>.of_eq
        (fun z => by simp only [signedEncode, Fin.addCases_right, id_eq])

/-- Computably enumerable integer sets have computably enumerable signed natural preimages. -/
theorem re_signed_preimage {D : Set (Fin n → ℤ)} (hD : REPred (· ∈ D)) :
    REPred (fun x : Fin (n + n) → ℕ => signedDecode x ∈ D) := by
  exact hD.comp signedDecode_primrec.to_comp.partrec

/-- An integer set is computably enumerable exactly when its signed natural preimage is. -/
theorem re_iff_signed_preimage (D : Set (Fin n → ℤ)) :
    REPred (· ∈ D) ↔ REPred (fun x : Fin (n + n) → ℕ => signedDecode x ∈ D) := by
  constructor
  · exact re_signed_preimage
  · intro h
    have hr : REPred (fun z : Fin n → ℤ => signedDecode (signedEncode z) ∈ D) :=
      h.comp signedEncode_primrec.to_comp.partrec
    exact hr.of_eq (fun z => by rw [signedDecode_encode])

/-- The integer-polynomial map underlying signed decoding. -/
def signedPolynomials (j : Fin n) : MvPolynomial (Fin (n + n)) ℤ :=
  X (Fin.castAdd n j) - X (Fin.natAdd n j)

/-- Evaluating the polynomial map on a natural tuple gives signed decoding. -/
theorem eval_signedPolynomials (x : Fin (n + n) → ℕ) (j : Fin n) :
    (signedPolynomials j).eval₂ (Int.castRingHom ℤ) (fun k => (x k : ℤ)) = signedDecode x j := by
  simp [signedPolynomials, signedDecode]

/-- A natural Diophantine definition of the signed preimage supplies an integer Diophantine definition. -/
theorem definable_of_natDefinable_signed_preimage {D : Set (Fin n → ℤ)}
    (hD : NatDefinable {x : Fin (n + n) → ℕ | signedDecode x ∈ D}) : Definable D := by
  obtain ⟨p, hp⟩ := hD.naturalImage.polynomialImage signedPolynomials
  refine ⟨p, fun x => (hp x).trans ?_⟩
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, he⟩
    have hx : x = signedDecode y := funext fun j => (he j).trans (eval_signedPolynomials y j)
    exact hx.symm ▸ hy
  · intro hx
    obtain ⟨y, rfl⟩ := signedDecode_surjective x
    exact ⟨fun j => (y j : ℤ), ⟨y, hx, rfl⟩, fun j => (eval_signedPolynomials y j).symm⟩

/-- Mathlib Dioph on the signed preimage also suffices, using the proved finite-system bridge. -/
theorem definable_of_dioph_signed_preimage {D : Set (Fin n → ℤ)}
    (hD : Dioph {x : Fin (n + n) → ℕ | signedDecode x ∈ D}) : Definable D :=
  definable_of_natDefinable_signed_preimage ((natDefinable_iff_dioph _).mpr hD)

end
end Surreal.IntegerDiophantine
