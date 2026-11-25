import IPRADerivations.Analysis.GaussianStirlingConstant
import IPRADerivations.Analysis.GaussianEulerExponentCompactBounds

/-!
# The original π observations used in the Binet kernel

Every actual arctangent observation is a canonical real fraction between
two and five. The finite bounds include the original dyadic margin
errors, including the first observation.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBinetKernelPi

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaHalfSqrtBrackets (fraction_first_represents)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianStirlingConstant (piNumerator piDenominator)
open RationalValueBounds (upper upper_congr positive_cancel)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "P" => GaussianGammaHalfPiName.nameF

def sample (p : PTm n) : PTm n := ap2 P p zero

@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (p : PTm n) :
    Syn.subst σ (sample p) = sample (Syn.subst σ p) := by simp [sample]

theorem sample_fraction (p : PTm n) : Γ ⊢[PRAAx] sample p ≐ fraction (piNumerator p) (piDenominator p) :=
  GaussianGammaHalfPiName.sample_at p zero

theorem denominator_positive (p : PTm n) : Γ ⊢[PRAAx] le one (piDenominator p) :=
  GammaEulerMesh.factorial_positive _

private theorem cleared_upper (a b c d T : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] upper (fstT (fraction a b)) (fstT (fraction c d)) one T) :
    Γ ⊢[PRAAx] le (T*d*a) (T*b*c+b*d) := by
  let x := ZT.ofNat (T*d)*ZT.ofNat a
  let y := ZT.ofNat (T*b)*ZT.ofNat c+ZT.ofNat (one*b*d)
  have signed : Γ ⊢[PRAAx] zle x y :=
    RationalUpperRepresentation.upper_from_representations _ _ b d one T (ZT.ofNat a) (ZT.ofNat c)
      (fraction_first_represents a b hb) (fraction_first_represents c d hd) h
  refine le_of_eq_add (d := PolynomialBisection.slack x y) ?_
  have eq := zle_toZ signed
  apply deriveNat
  unfold PolynomialBisection.slack
  dsimp only [x,y] at eq
  simp only [ZT.toZ_mul, ZT.toZ_add, ZT.toZ_ofNat] at eq
  ipra_simps
  linear_combination -eq

theorem sample_margins (p : PTm n) : Γ ⊢[PRAAx]
    le (two*piDenominator p) (piNumerator p) ⋏ le (piNumerator p) (num 5*piDenominator p) := by
  let a := piNumerator p
  let b := piDenominator p
  let T := unit p
  let c : PTm n := GaussianArctangentPiMargins.lowerNum
  let d : PTm n := GaussianArctangentPiMargins.lowerDen
  have hd : Γ ⊢[PRAAx] le one d := by
    dsimp only [d, GaussianArctangentPiMargins.lowerDen]
    ipra_le 499
  have hT := unit_positive (Γ := Γ) p
  have hb := denominator_positive (Γ := Γ) p
  have original := GaussianArctangentPiMargins.named_margins (Γ := Γ) p zero
  have read := congrFst (sample_fraction (Γ := Γ) p)
  have lo := cleared_upper c d a b T hd hb (upper_congr (.eqRefl _) read (.eqRefl _) (.eqRefl _) original.andE₁)
  have hi := cleared_upper a b (num 7) two T hb (le_succ_self one)
    (upper_congr read (.eqRefl _) (.eqRefl _) (.eqRefl _) original.andE₂)
  refine .andI ?_ ?_
  · apply positive_cancel (c := T*d) (positive_product T d hT hd)
    dsimp only [c, d, GaussianArctangentPiMargins.lowerNum, GaussianArctangentPiMargins.lowerDen] at lo ⊢
    ipra_le sl lo + 500*𝔞(b)*sl hT + 𝔞(T)*𝔞(b)
  · apply positive_cancel (c := T*two) (positive_product T two hT (le_succ_self one))
    ipra_le sl hi + 2*𝔞(b)*sl hT + 𝔞(T)*𝔞(b)

theorem sample_bound (p : PTm n) : Γ ⊢[PRAAx] bounded (sample p) (num 5) one :=
  bound_congr (sample_fraction p).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianEulerExponentCompactBounds.fraction_bound (piNumerator p) (piDenominator p) (num 5)
      (denominator_positive p) (sample_margins p).andE₂)

theorem sample_distance (p q : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (sample p) (sample q) (unit p+unit q) (unit p*unit q) :=
  GaussianNameEquivalence.point_at P zero p q (GaussianGammaHalfPiName.name_regular zero)

theorem actual_Binet_pi_sample_margins_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      (le (two*piDenominator (var 0)) (piNumerator (var 0)) ⋏
        le (piNumerator (var 0)) (num 5*piDenominator (var 0))) :=
  closeUniv 1 (sample_margins _)

end LeanProofs.IPRA.Analysis.GaussianBinetKernelPi
