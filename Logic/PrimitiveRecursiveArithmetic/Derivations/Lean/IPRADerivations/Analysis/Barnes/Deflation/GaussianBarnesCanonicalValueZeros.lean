import IPRADerivations.Analysis.Barnes.CanonicalProducts.GaussianBarnesCanonicalValue
import IPRADerivations.Analysis.Barnes.HeadProducts.GaussianBarnesCanonicalHeadApartness
import IPRADerivations.Analysis.Barnes.Prefactors.GaussianBarnesCanonicalPrefactorInverse
import IPRADerivations.Analysis.Barnes.TailControl.GaussianBarnesCanonicalTailApartness
import IPRADerivations.Analysis.Names.FiniteOperations.Products.GaussianNamedProductApartness
import IPRADerivations.Analysis.Gamma.Poles.GaussianGammaPoleSearch

/-!
# Rational zero classification of the original Barnes value

The prefactor and the cofinal tail are apart on every admitted rational
disk. The finite original head decides the full value: the same head
zero persists in every observation, and separation of the head gives
an explicit original multiplication observation separated from zero.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalValueZeros

open_ipra
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial initial_radius)
open GaussianBarnesCanonicalValue (nameF data prefixF prefixData prefix_regular)
open GaussianBarnesCanonicalHeadApartness (search hit negative_integer_index initial_negative_integer_at)
open GaussianNameReciprocal (apart)
open GaussianNamedSmallPerturbationTransport (productClock product_at)
open GaussianGeneralPolynomialValueName (programZero)
open GaussianGammaPoleZeros (poleNumerator)
open GaussianRationalHorner (qzero)
open GaussianRationalSyntheticDivision (qmul_congr qmul_zero_right qmul_zero_left)
open GaussianRootAlgebra (equal)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "P" => GaussianBarnesCanonicalPrefactor.nameF
local notation "Pd" => GaussianBarnesCanonicalPrefactor.data
local notation "H" => GaussianBarnesCanonicalHead.nameF
local notation "T" => GaussianBarnesCanonicalTailExponential.nameF
local notation "Td" => GaussianBarnesCanonicalTailExponential.data
local notation "apartProductHeight" => GaussianNamedProductApartness.height

def zeroIndex (z R B : PTm n) : PTm n := succ (zero+search z B zero (initial R))

def zeroCertificate (z R B : PTm n) : Fm PTm n :=
  le one (zeroIndex z R B) ⋏ (le (zeroIndex z R B) R ⋏ equal z (poleNumerator B (zeroIndex z R B)))

def allZero (z R B : PTm n) : Fm PTm n := .all (ap2 nameF (var 0) (data (Syn.shift z) (Syn.shift R) (Syn.shift B)) ≐ qzero)

def height (z R B : PTm n) : PTm n :=
  apartProductHeight (apartProductHeight (GaussianBarnesCanonicalPrefactorInverse.height z B)
    (GaussianBarnesCanonicalHeadApartness.clock R B zero (initial R))) (GaussianBarnesCanonicalTailApartness.height R)

private theorem radius_le_initial (R : PTm n) : Γ ⊢[PRAAx] le R (initial R) :=
  le_trans (le_congr (one_mul R) (.eqRefl _) (mul_le_mul_right R (le_succ_self one))) (initial_radius R)

private theorem zero_of_head_samples (p z R B : PTm n)
    (hz : ∀ t : PTm n, Γ ⊢[PRAAx] ap2 H t (GaussianBarnesCanonicalHead.headData z R B (initial R)) ≐ qzero) :
    Γ ⊢[PRAAx] ap2 nameF p (data z R B) ≐ qzero := by
  let x := Pd z B
  let y := GaussianBarnesCanonicalHead.headData z R B (initial R)
  let a := prefixData z R B
  let b := Td z R B
  let t := productClock prefixF T a b p
  let s := productClock P H x y t
  have prefixZero : Γ ⊢[PRAAx] ap2 prefixF t a ≐ qzero :=
    (product_at P H x y t).eqTrans ((qmul_congr (.eqRefl _) (hz s)).eqTrans (qmul_zero_right _))
  exact (product_at prefixF T a b p).eqTrans
    ((qmul_congr prefixZero (.eqRefl _)).eqTrans (qmul_zero_left _))

theorem negative_integer_zero (p z R B k : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (hk : Γ ⊢[PRAAx] le one k) (hz : Γ ⊢[PRAAx] equal z (poleNumerator B k)) :
    Γ ⊢[PRAAx] ap2 nameF p (data z R B) ≐ qzero :=
  zero_of_head_samples p z R B (fun t => initial_negative_integer_at t z R B (initial R) k h (radius_le_initial R) hk hz)

theorem apart_of_head (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (ha : Γ ⊢[PRAAx] apart H (GaussianBarnesCanonicalHeadApartness.clock R B zero (initial R))
      (GaussianBarnesCanonicalHead.headData z R B (initial R))) :
    Γ ⊢[PRAAx] apart nameF (height z R B) (data z R B) := by
  have hhead := GaussianBarnesCanonicalHead.regular z R B zero (initial R) h
  have hprefix := GaussianNamedProductApartness.original_apart P H (Pd z B) _ _ _
    (GaussianBarnesCanonicalPrefactor.regular z B) hhead (GaussianBarnesCanonicalPrefactorInverse.apart z B) ha
  exact GaussianNamedProductApartness.original_apart prefixF T (prefixData z R B) (Td z R B) _ _
    (prefix_regular z R B h) (GaussianBarnesCanonicalTailExponential.regular z R B h) hprefix
    (GaussianBarnesCanonicalTailApartness.original_apart z R B h)

private theorem certificate_of_hit (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] hit z B zero (initial R)) :
    Γ ⊢[PRAAx] zeroCertificate z R B := by
  let k := zeroIndex z R B
  have hk : Γ ⊢[PRAAx] le one k := zero_lt_succ _
  have eq := GaussianBarnesCanonicalBase.base_zero z B k h.andE₁ hk hh.andE₂
  have ez := GaussianBarnesCanonicalBase.zero_is_negative_integer z B k h.andE₁ hk eq
  exact .andI hk (.andI (negative_integer_index z R B k h ez) ez)

private theorem subst_head_allZero {m : ℕ} (σ : Fin n → PTm m) (z R B N r : PTm n) :
    (GaussianBarnesCanonicalHeadApartness.allZero z R B N r).subst σ =
      GaussianBarnesCanonicalHeadApartness.allZero
        (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ r) := by
  simp [GaussianBarnesCanonicalHeadApartness.allZero,Syn.subst_shift,Syn.shift_subst]

private theorem all_zero_of_head (z R B : PTm n)
    (hh : Γ ⊢[PRAAx] GaussianBarnesCanonicalHeadApartness.allZero z R B zero (initial R)) :
    Γ ⊢[PRAAx] allZero z R B := by
  refine .allI ?_
  let s (a : PTm n) := Syn.shift a
  let Δ := Γ.map Fm.shift
  have hz : Δ ⊢[PRAAx] GaussianBarnesCanonicalHeadApartness.allZero (s z) (s R) (s B) zero (initial (s R)) := by
    simpa [subst_head_allZero,Fm.shift,Syn.shift,s,Δ] using hh.shift
  exact zero_of_head_samples (var 0) (s z) (s R) (s B) (fun t => by
    simpa [GaussianBarnesCanonicalHeadApartness.allZero,GaussianBarnesCanonicalHead.headData] using hz.allE t)

theorem original_zero_or_apart (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] ((zeroCertificate z R B ⋏ allZero z R B) ⋎ apart nameF (height z R B) (data z R B)) := by
  refine .orE (GaussianBarnesCanonicalHeadApartness.original_zero_or_apart z R B zero (initial R) h) ?_ ?_
  · exact .orI₁ (.andI (certificate_of_hit z R B h.wk Prf.hyp0.andE₁) (all_zero_of_head z R B Prf.hyp0.andE₂))
  · exact .orI₂ (apart_of_head z R B h.wk Prf.hyp0)

/-- Even the usual Cauchy-name zero bound forces the exact negative integer witness. -/
theorem only_negative_integer (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (hz : Γ ⊢[PRAAx] programZero nameF (data z R B)) : Γ ⊢[PRAAx] zeroCertificate z R B := by
  refine .orE (original_zero_or_apart z R B h) Prf.hyp0.andE₁ ?_
  exact .botE _ (GaussianGammaPoleSearch.apart_excludes_zero nameF (data z R B) (height z R B) Prf.hyp0 hz.wk)

theorem actual_Barnes_value_zero_or_apart_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) (var 2) ⟶
      ((zeroCertificate (var 0) (var 1) (var 2) ⋏ allZero (var 0) (var 1) (var 2)) ⋎
        apart nameF (height (var 0) (var 1) (var 2)) (data (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.impI (original_zero_or_apart _ _ _ Prf.hyp0))

theorem actual_Barnes_value_only_negative_integer_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((source (var 0) (var 1) (var 2) ⋏ programZero nameF (data (var 0) (var 1) (var 2))) ⟶
      zeroCertificate (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (only_negative_integer _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalValueZeros
