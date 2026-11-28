import GRHArticle.ProgressionFree.NumberFieldIdeals.IdealQuotientOptimization
import GRHArticle.ProgressionFree.NumberFieldIdeals.IdealRationalEnclosures
import Mathlib.Data.Nat.Find
import Mathlib.Data.Rat.Floor

/-!
# Computing the ideal density suprema from explicit order arithmetic

The input presents each residue ring of the order with executable
arithmetic and a certified reduction. For a positive rational tolerance the
algorithm chooses a prime cutoff, searches the smooth norm cutoff using
finite rational error tests, and returns rational enclosures for both
extrema with widths smaller than that tolerance.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open NumberField Ideal IsDedekindDomain Finset Filter
open scoped nonZeroDivisors

universe u v

/-- Concrete residue arithmetic for an explicitly presented number field.
An integral basis and its integer multiplication structure constants allow
each finite ring to be presented by coordinate residues. -/
structure ExplicitIdealArithmetic (K : Type u) [Field K] [NumberField K] where
  residue : ℕ → Type v
  ring (H : ℕ) : CommRing (residue H)
  enumeration (H : ℕ) : Fintype (residue H)
  decidableEq (H : ℕ) : DecidableEq (residue H)
  reduction (H : ℕ) : @FiniteIdealQuotient K _ _ (residue H) (ring H) H
  degree : ℕ
  degree_eq : degree = Module.finrank ℚ K

namespace ExplicitIdealArithmetic

variable {K : Type u} [Field K] [NumberField K]
variable (A : ExplicitIdealArithmetic.{u,v} K)

/-- Both exact smooth errors, computed without performing the optimization. -/
def smoothErrors (Y H : ℕ) : ℚ × ℚ :=
  let M := max Y H
  let R := A.residue M
  letI : CommRing R := A.ring M
  letI : Fintype R := A.enumeration M
  letI : DecidableEq R := A.decidableEq M
  let T := FiniteRing.idealTable R Y H
  let primes := FiniteRing.boundedPrimeNorms R Y
  (T.lowerError primes H, T.upperError primes H)

/-- Both density enclosures at the selected cutoffs. -/
def enclosures (integral : Bool) (Y H : ℕ) : IdealDensityEnclosures :=
  let M := max Y H
  let R := A.residue M
  letI : CommRing R := A.ring M
  letI : Fintype R := A.enumeration M
  letI : DecidableEq R := A.decidableEq M
  let T := FiniteRing.idealTable R Y H
  idealRationalEnclosures T (FiniteRing.boundedPrimeNorms R Y) integral A.degree Y H

theorem smoothErrors_eq (Y H : ℕ) :
    let S := primesThroughNorm K Y
    ((A.smoothErrors Y H).1 : ℝ) = idealSmoothDensityFactor S *
      idealReciprocalWeight (K := K) (idealSmoothNormTail S H) ∧
    ((A.smoothErrors Y H).2 : ℝ) = idealSmoothDensityFactor S * idealSmoothFullCountTail S H := by
  let M := max Y H
  let R := A.residue M
  letI : CommRing R := A.ring M
  letI : Fintype R := A.enumeration M
  letI : DecidableEq R := A.decidableEq M
  let Q : FiniteIdealQuotient K R M := A.reduction M
  unfold smoothErrors
  dsimp only
  rw [FiniteRing.boundedPrimeNorms_eq Q]
  exact IdealCutoffTable.error_eval_eq (FiniteRing.idealTable_correct Q)

theorem enclosures_sound (integral : Bool) {Y : ℕ} (hY : 0 < Y) (H : ℕ) :
    (A.enclosures integral Y H).Sound K integral := by
  let M := max Y H
  let R := A.residue M
  letI : CommRing R := A.ring M
  letI : Fintype R := A.enumeration M
  letI : DecidableEq R := A.decidableEq M
  let Q : FiniteIdealQuotient K R M := A.reduction M
  unfold enclosures
  dsimp only
  rw [FiniteRing.boundedPrimeNorms_eq Q]
  exact idealRationalEnclosures_sound (FiniteRing.idealTable_correct Q) hY A.degree_eq integral

private theorem existsPrimeCutoff (n : ℕ) {δ : ℚ} (hδ : 0 < δ) :
    ∃ Y : ℕ, 0 < Y ∧ (n : ℚ)/Y < δ := by
  obtain ⟨Y,hY⟩ := exists_nat_gt (max (1 : ℚ) ((n : ℚ)/δ))
  have hY' : (0 : ℚ) < Y := zero_lt_one.trans ((le_max_left _ _).trans_lt hY)
  refine ⟨Y,by exact_mod_cast hY', (div_lt_iff₀ hY').mpr ?_⟩
  simpa only [mul_comm] using (div_lt_iff₀ hδ).mp ((le_max_right _ _).trans_lt hY)

private theorem existsNormCutoff (Y : ℕ) {δ : ℚ} (hδ : 0 < δ) :
    ∃ H : ℕ, (A.smoothErrors Y H).1 < δ ∧ (A.smoothErrors Y H).2 < δ := by
  have hδ' : 0 < (δ : ℝ) := by exact_mod_cast hδ
  obtain ⟨H,hH⟩ := (eventually_idealSmoothApproximation_errors_lt (primesThroughNorm K Y) hδ').exists
  have he := A.smoothErrors_eq Y H
  dsimp only at he
  have hL : ((A.smoothErrors Y H).1 : ℝ) < (δ : ℝ) := he.1.trans_lt hH.1
  have hU : ((A.smoothErrors Y H).2 : ℝ) < (δ : ℝ) := he.2.trans_lt hH.2
  exact ⟨H,by exact_mod_cast hL,by exact_mod_cast hU⟩

/-- The prime and norm cutoffs computed by terminating exact searches. -/
def findCutoffs (ε : ℚ) (hε : 0 < ε) : ℕ × ℕ :=
  let hδ : 0 < ε/2 := by positivity
  let Y := Nat.find (existsPrimeCutoff A.degree hδ)
  (Y,Nat.find (A.existsNormCutoff Y hδ))

/-- Executable arbitrarily narrow rational enclosures, for either ratio convention. -/
def approximate (integral : Bool) (ε : ℚ) (hε : 0 < ε) : IdealDensityEnclosures :=
  let p := A.findCutoffs ε hε
  A.enclosures integral p.1 p.2

/-- The executable algorithm terminates with two sound rational intervals
of widths strictly below the requested positive rational tolerance. -/
theorem approximate_spec (integral : Bool) (ε : ℚ) (hε : 0 < ε) :
    let B := A.approximate integral ε hε
    B.Sound K integral ∧ B.naturalUpper - B.naturalLower < ε ∧ B.upperUpper - B.upperLower < ε := by
  let hδ : 0 < ε/2 := by positivity
  let Y := Nat.find (existsPrimeCutoff A.degree hδ)
  let H := Nat.find (A.existsNormCutoff Y hδ)
  have hY : 0 < Y ∧ (A.degree : ℚ)/Y < ε/2 := Nat.find_spec (existsPrimeCutoff A.degree hδ)
  have hh : (A.smoothErrors Y H).1 < ε/2 ∧ (A.smoothErrors Y H).2 < ε/2 :=
    Nat.find_spec (A.existsNormCutoff Y hδ)
  change (A.enclosures integral Y H).Sound K integral ∧ _
  refine ⟨A.enclosures_sound integral hY.1 H,?_⟩
  let M := max Y H
  let R := A.residue M
  letI : CommRing R := A.ring M
  letI : Fintype R := A.enumeration M
  letI : DecidableEq R := A.decidableEq M
  exact idealRationalEnclosures_width_lt (FiniteRing.idealTable R Y H) (FiniteRing.boundedPrimeNorms R Y)
    integral hY.2 hh.1 hh.2

end ExplicitIdealArithmetic
end GRHArticle.ProgressionFree.NumberFieldIdeals
