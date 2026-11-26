import Lib.Adelic.Unitary.GramMatrix
import Lib.ClassField.HeckeCharacter.Basic
import Lib.Weil.Construction.HeisenbergModel

/-!
# Splitting characters, Weil data, and the adelic Heisenberg cocycle and vacuum

On a CM field `E` with CM type `Φ` (`New.CMType`; `Φ w` is the embedding τ : E → ℂ chosen at the
infinite place w), this file fixes the arithmetic data that determine the Weil representation. From
these data the file builds the adelic Heisenberg bicharacter and the vacuum function on `𝔸^n`, the
two ingredients of the adelic Weil representation.

## Main definitions and results

* `New.SplittingChar`: a splitting character `υ`, a unitary Hecke character with prescribed values
  on ideles whose finite part is a unit.
* `New.WeilData`: `υ` together with a purely imaginary `ȷ ∈ E`, which turns the hermitian form into
  a Heisenberg cocycle, and a finite idele `α`, which scales the vacuum lattice.
* `New.WeilData.scaleIdele`: the idele with finite part `α` that normalises the real coordinates.
* `New.adelicHeisenberg`: the bicharacter β(x, y) = ψ(½ȷ y*Sx), where S is `New.stdForm`, the
  diagonal form with signs `s` at the infinite places and 1 at the finite ones.
* `New.vacuumFn`: the vacuum, a Gaussian at the infinite places times a function of modulus one on
  the lattice αÔ^n of finite vectors (zero off the lattice). It does not depend on `s`.

Notions from other files:
* `New.𝔸`: The ring ℂ^f × 𝔸_f, one copy of ℂ for each infinite place of E times the finite adeles:
  the adele ring of E when E is totally complex.
* `New.ψf`: The standard additive character of the finite adeles: ψ_f(x) = exp(2πi Tr_{E/ℚ}(a)) for
  any a in E with x − a integral.
* `New.Heisenberg`: A continuous function β on W × W, W a topological abelian group, with values of
  modulus one, multiplicative in each variable, and β(x,x) = 1.

## Relation to the literature

Known; see `Lib.Weil.MixedModel.ZeroTerm` and `Lib.ClassField.Global.CMSplittingCharacters` for
sources.
-/

noncomputable section

namespace New

/-!
## Splitting characters and Weil data

`New.Ô E` is the ring of integral finite adeles.
-/

section WeilData

open MulEquiv NumberField Valued

variable (E : Type*) [Field E] [CMType E]

/-- A splitting character: a unitary Hecke character `υ` of `E` with `υ x̄ = (υ x)⁻¹` that equals
`∏ x_τ / |x_τ|` (over the infinite places) when the finite part of the idele `x` is a unit of
`Ô`, that is, when the finite parts of `x` and of `x⁻¹` both lie in `Ô`. -/
class SplittingChar where
  /-- The unitary Hecke character υ of E. -/
  υ : HeckeChar E
  /-- If the finite part of the idele x is a unit of Ô, then υ(x) = ∏ x_τ / |x_τ| over the infinite
  places τ, where x_τ = `(x : 𝔸 E).fst τ` is the component of x at τ. -/
  υ_unit (x : (𝔸 E)ˣ) :
      x.map (MonoidHom.snd (InfinitePlace E → ℂ) (𝔸f E)) ∈ (Ô E).units →
        υ.1 x = ∏ w : InfinitePlace E, (x : 𝔸 E).fst w / ‖(x : 𝔸 E).fst w‖
  /-- Complex conjugation inverts υ: υ(x̄) = υ(x)⁻¹. -/
  υ_star (x : (𝔸 E)ˣ) : υ.1 (star x) = (υ.1 x)⁻¹

/-- Weil data on E, which contains a primitive 5040th root of unity (`New.HasPrimitiveRoot5040`;
then E/E⁺ is unramified at the finite places): ȷ = −ȷ̄ in E with Im τȷ > 0 and (1 − ȷ⁻¹)/2 integral,
a finite idele α making Ô self-dual for the pairing (z, u) ↦ ψ_f(ȷαᾱzu) of finite adeles z, u, and a
splitting character υ equal to −1 at uniformisers of places w = w̄. -/
class WeilData extends HasPrimitiveRoot5040 E, SplittingChar E where
  /-- The element ȷ of E. -/
  j : E
  /-- ȷ is purely imaginary: its conjugate is −ȷ. -/
  star_j : star j = -j
  /-- ȷ has positive imaginary part under each embedding of the CM type. -/
  im_pos (w : InfinitePlace E) : 0 < (Φ w j).im
  /-- The finite idele α of E. -/
  α : (𝔸f E)ˣ
  /-- At every finite place w, the order of ȷαᾱ is minus the order of the different of E. -/
  self_dual (w : IsDedekindDomain.HeightOneSpectrum (𝓞 E)) :
      v ((algebraMap E (𝔸f E) j * α.1 * star α.1) w) =
        .exp (multiplicity w.asIdeal (differentIdeal ℤ (𝓞 E)))
  /-- c₀ = (1 − ȷ⁻¹) / 2 is an algebraic integer. -/
  isIntegral_traceOne : IsIntegral ℤ ((1 - j⁻¹) / 2)
  /-- At a finite place w fixed by conjugation, υ is −1 on the chosen uniformiser. -/
  υ_inert (w : FinPlace E) : star w = w → υ.atUniformizer w = -1

namespace WeilData

attribute [simp] star_j

export SplittingChar (υ υ_unit υ_star)

/-- The idele whose component at each infinite place τ is (2π Im τȷ)^(-1/2) and whose finite
part is α. -/
@[simps! -isSimp val_fst val_snd]
noncomputable def scaleIdele [WeilData E] : (𝔸 E)ˣ :=
  prodUnits.symm
    (piUnits.symm fun w ↦
        Units.mk0 ↑(√(2 * Real.pi * (Φ w j).im))⁻¹ (mod_cast by positivity [im_pos w]),
      α)

variable {E} [WeilData E]

/-- The element c₀ = (1 − ȷ⁻¹)/2 of E, ȷ from the Weil data; it is an algebraic integer with
c₀ + c̄₀ = 1. -/
def traceOne : E := (1 - j⁻¹) / 2

/-- The element ȷ of the Weil data is nonzero, since Im τȷ > 0 at every infinite place τ. -/
@[grind .]
lemma j_ne_zero : (j : E) ≠ 0 := by
  intro hj
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  simpa [hj] using im_pos w

end WeilData

end WeilData

/-!
## The adelic vacuum function and the Heisenberg cocycle

The purely imaginary ȷ (written `j`), the finite idele α and c₀ = (1 − ȷ⁻¹)/2 (written `traceOne`)
come from `New.WeilData`. ψ is `New.stdAddChar`, the standard additive character of the adeles. An
adele `x` is a pair: `x.1` is the family of its infinite components, `x.2` its finite part.
-/

section AdelicHeisenberg

open Matrix NumberField Real WeilData

variable {E : Type*} [Field E] [CMType E] [WeilData E]
  {n : Type*} [Fintype n] [DecidableEq n] (s : n → ℤˣ)

open scoped Classical in
/-- The vacuum on adelic vectors: exp(−π ∑_{i,τ} Im(τȷ)|x_{i,τ}|²) times ψ_f(½c₀ȷ x_f*x_f) if
the finite part x_f lies in αÔ^n, and 0 otherwise. -/
def vacuumFn (x : n → 𝔸 E) : ℂ :=
  Real.exp (-∑ i : n, ∑ w : InfinitePlace E, π * (Φ w j).im * ‖(x i).1 w‖ ^ 2) *
    if ∀ i : n, α⁻¹.1 * (x i).2 ∈ Ô E then
      (ψf E ((traceOne * j / 2 : E) * ∑ i : n, star (x i).2 * (x i).2)).1
    else
      0

omit [DecidableEq n] in
open scoped Classical in
/-- The phase of the vacuum is ψ_f(−¼ x_f*x_f): c₀ȷ/2 = (ȷ − 1)/4, and ψ_f does not see the skew
part ȷ x_f*x_f/4. -/
lemma vacuumFn_eq_exp_mul_ite (x : n → 𝔸 E) :
    vacuumFn x =
      Real.exp (-∑ i : n, ∑ w : InfinitePlace E, π * (Φ w j).im * ‖(x i).1 w‖ ^ 2) *
        if ∀ i : n, α⁻¹.1 * (x i).2 ∈ Ô E then
          (ψf E ((-4⁻¹ : E) * ∑ i : n, star (x i).2 * (x i).2) : ℂ)
        else
          0 := by
  set r : 𝔸f E := ∑ i : n, star (x i).2 * (x i).2
  have h_trace : 2⁻¹ * ((traceOne * j / 2 : E) + star (traceOne * j / 2)) = -4⁻¹ := by
    have h_coeff : (traceOne * j / 2 : E) = (j - 1) / 4 := by
      rw [traceOne]
      field [j_ne_zero]
    simp only [h_coeff, star_div₀, star_sub, star_j, star_one, star_ofNat]
    ring
  have h_phase : ψf E ((traceOne * j / 2 : E) * r) = ψf E ((-4⁻¹ : E) * r) := by
    have h_real : star r = r := by simp [r, mul_comm]
    rw [← ψf_inv_two_mul_add_star, ← h_trace, star_mul', h_real]
    simp [mul_add, add_mul, mul_assoc]
  rw [vacuumFn, h_phase]

variable (E)

/-- The Heisenberg datum on adelic n-space with bicharacter β(x,y)=ψ(½ȷ h(y,x)), h being the
hermitian form with matrix `New.stdForm E s`; `toAdele` is the embedding of E in the adeles
`𝔸 E`. -/
def adelicHeisenberg : Heisenberg (n → 𝔸 E) where
  β x y := stdAddChar E (toAdele (j / 2) * star y ⬝ᵥ stdForm E s *ᵥ x)
  add_left := by simp [mul_add, AddChar.map_add_eq_mul, mulVec_add]
  add_right := by simp [mul_add, AddChar.map_add_eq_mul]
  self_eq_one x := by
    -- by `stdAddChar_inv_two_mul_add_star`, `stdAddChar` sees only `a + star a` of its argument
    -- `a`, and this vanishes here since `star j = -j` and the form is Hermitian
    rw [← stdAddChar_inv_two_mul_add_star]
    simp [neg_div, ← star_dotProduct, star_mulVec_dotProduct]
  norm_eq_one := by simp [Circle.norm_coe]
  cont := Continuous.subtype_val (by fun_prop)

end AdelicHeisenberg

end New

end
