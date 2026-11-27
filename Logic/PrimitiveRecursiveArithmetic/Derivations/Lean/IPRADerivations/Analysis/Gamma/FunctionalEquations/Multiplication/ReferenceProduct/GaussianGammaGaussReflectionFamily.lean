import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.ReferenceProduct.GaussianGammaGaussReflectionRow
import IPRADerivations.Analysis.Names.FiniteOperations.Products.Families.GaussianNamedFiniteProductFamilyCongruence
import IPRADerivations.Analysis.Trigonometry.Cyclic.SineProducts.GaussianCyclicSineProductSquare

/-!
# The finite reflection family in the original cyclic sine order

At modulus `N+1`, row `i<N` uses the sine and first Gamma operand
at `(N-i)/(N+1)`. The complementary Gamma operand is exactly the
reference at `(i+1)/(N+1)`. The product of these actual cleared
reflection rows agrees with the product of the same `N` copies of π.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 750000

namespace LeanProofs.IPRA.Analysis.GaussianGammaGaussReflectionFamily

open_ipra
open GaussianGammaGaussReflectionDomain (source referenceData complement pairData pair_regular reference_regular)
open GaussianGammaGaussReflectionRow (rowF rowData row_regular reflection_row cyclic_source)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianGammaReflectionProduct (gammaPairF)
open GaussianGammaFactorialValues (gamma_fields_congr)
open GaussianCyclicFullHalfAngle (sineData sine_regular)
open GaussianCyclicSineProductSquare (index data)
open GaussianNamedFiniteProductFamily (regularRows productData)
open GaussianNamedFiniteProductFamilyCongruence (equalRows family_product_cross)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNameArithmetic (multiplyData)
open GaussianRootAlgebra (equal_of_values)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "P" => GaussianGammaHalfPiName.nameF
local notation "S" => GaussianNamedSineFromExponential.sineF GaussianCyclicExponentialRoots.angleF
local notation "FamilyRow" => GaussianNamedFiniteProductFamily.rowF
local notation "ProductName" => GaussianNamedFiniteProductName.nameF

def numerator (N i : PTm n) : PTm n := succ (index N i)
def reflectionBody : PTm 2 := rowData (numerator (fstT (var 1)) (var 0)) (succ (fstT (var 1))) (sndT (var 1))
def sineBody : PTm 2 := sineData (numerator (fstT (var 1)) (var 0)) (succ (fstT (var 1))) (sndT (var 1))
def leftBody : PTm 2 := referenceData (numerator (fstT (var 1)) (var 0)) (succ (fstT (var 1)))
def rightBody : PTm 2 := referenceData (complement (numerator (fstT (var 1)) (var 0)) (succ (fstT (var 1)))) (succ (fstT (var 1)))
def pairBody : PTm 2 := multiplyData gammaF gammaF leftBody rightBody
def piBody : PTm 2 := sndT (var 1)

ipra_subst numerator

theorem reflection_body_eq : reflectionBody = multiplyData S gammaPairF sineBody pairBody := rfl

private theorem readback (g : PTm 3) (N x i : PTm n) :
    Γ ⊢[PRAAx] Syn.subst ![i,fstT (data N x),sndT (data N x)] g ≐ Syn.subst ![i,N,x] g :=
  Prf.eqCongr g (σ := ![i,fstT (data N x),sndT (data N x)]) (σ' := ![i,N,x])
    (fun j => by fin_cases j; exact .eqRefl _; exact fst_pair _ _; exact snd_pair _ _)

theorem reflection_at (N x i : PTm n) :
    Γ ⊢[PRAAx] inst2 reflectionBody i (data N x) ≐ rowData (numerator N i) (succ N) x := by
  simpa [reflectionBody,inst2] using
    readback (rowData (numerator (var 1) (var 0)) (succ (var 1)) (var 2)) N x i

theorem sine_at (N x i : PTm n) :
    Γ ⊢[PRAAx] inst2 sineBody i (data N x) ≐ sineData (numerator N i) (succ N) x := by
  simpa [sineBody,inst2] using
    readback (sineData (numerator (var 1) (var 0)) (succ (var 1)) (var 2)) N x i

theorem left_at (N x i : PTm n) :
    Γ ⊢[PRAAx] inst2 leftBody i (data N x) ≐ referenceData (numerator N i) (succ N) := by
  simpa [leftBody,inst2] using readback (referenceData (numerator (var 1) (var 0)) (succ (var 1))) N x i

theorem right_at (N x i : PTm n) :
    Γ ⊢[PRAAx] inst2 rightBody i (data N x) ≐ referenceData (complement (numerator N i) (succ N)) (succ N) := by
  simpa [rightBody,inst2] using
    readback (referenceData (complement (numerator (var 1) (var 0)) (succ (var 1))) (succ (var 1))) N x i

theorem pi_at (N x i : PTm n) : Γ ⊢[PRAAx] inst2 piBody i (data N x) ≐ x := by
  simpa [piBody,inst2,data] using snd_pair (Γ := Γ) N x

theorem row_source (N i : PTm n) (h : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] source (numerator N i) (succ N) := by
  have e : Γ ⊢[PRAAx] N ≐ succ i+index N i := eq_add_of_le h
  have a : Γ ⊢[PRAAx] le (numerator N i) N := le_of_eq_add (d := i) (e.eqTrans (by unfold numerator; ipra_ring))
  exact .andI (zero_lt_succ _) (lt_of_le_of_lt a (le_refl (succ N)))

theorem complementary_index (N i : PTm n) (h : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] complement (numerator N i) (succ N) ≐ succ i := by
  have e : Γ ⊢[PRAAx] N ≐ succ i+index N i := eq_add_of_le h
  have f : Γ ⊢[PRAAx] succ N ≐ numerator N i+succ i := (congrSucc e).eqTrans (by unfold numerator; ipra_ring)
  have g : Γ ⊢[PRAAx] succ N ≐ numerator N i+complement (numerator N i) (succ N) :=
    eq_add_of_le (le_of_lt (row_source N i h).andE₂)
  have h₁ := natEq f
  have h₂ := natEq g
  apply deriveNat
  simp only [IPRA.Q.mk_add,map_add] at h₁ h₂
  linear_combination h₁-h₂

theorem right_ascending_at (N x i : PTm n) (h : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] inst2 rightBody i (data N x) ≐ referenceData (succ i) (succ N) := by
  have e := complementary_index N i h
  have cast := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (GaussianGammaGaussReflectionDomain.argument (var 0) : PTm 1)
    (σ := ![complement (numerator N i) (succ N)]) (σ' := ![succ i]) (fun j => by fin_cases j; exact e)
  exact (right_at N x i).eqTrans (gamma_fields_congr (by simpa using cast) (.eqRefl _) (.eqRefl _) (.eqRefl _))

private theorem point_congr (f : PR 2) (u v : PTm n) (e : Γ ⊢[PRAAx] u ≐ v) (h : Γ ⊢[PRAAx] pointCN f u) :
    Γ ⊢[PRAAx] pointCN f v := by
  simpa using Prf.eqSubst (Ax := PRAAx) (Γ := Γ) (pointCN f (var 0) : Fm PTm 1) ![u] ![v]
    (fun j => by fin_cases j; exact e) (by simpa using h)

private theorem cross_congr (f g : PR 2) {a b u v : PTm n}
    (e : Γ ⊢[PRAAx] a ≐ u) (d : Γ ⊢[PRAAx] b ≐ v) (h : Γ ⊢[PRAAx] crossEquivalent f g a b) :
    Γ ⊢[PRAAx] crossEquivalent f g u v := by
  simpa using Prf.eqSubst (Ax := PRAAx) (Γ := Γ)
    (crossEquivalent f g (var 0) (var 1) : Fm PTm 2) ![a,b] ![u,v]
    (fun j => by fin_cases j; exact e; exact d) (by simpa using h)

theorem reflection_rows (N x : PTm n) :
    Γ ⊢[PRAAx] regularRows rowF reflectionBody N (data N x) := by
  refine .allI (.impI ?_)
  let K := Syn.shift N
  let y := Syn.shift x
  let i : PTm (n+1) := var 0
  let Δ := lt i K :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (numerator K i) (succ K) := row_source K i Prf.hyp0
  simpa [regularRows,Δ,K,y,i,Syn.shift] using
    point_congr rowF _ _ (reflection_at K y i).eqSymm (row_regular _ _ _ hs)

theorem sine_rows (N x : PTm n) :
    Γ ⊢[PRAAx] regularRows S sineBody N (data N x) := by
  refine .allI (.impI ?_)
  let K := Syn.shift N
  let y := Syn.shift x
  let i : PTm (n+1) := var 0
  let Δ := lt i K :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (numerator K i) (succ K) := row_source K i Prf.hyp0
  simpa [regularRows,Δ,K,y,i,Syn.shift] using
    point_congr S _ _ (sine_at K y i).eqSymm (sine_regular _ _ _ (cyclic_source _ _ hs))

theorem left_rows (N x : PTm n) :
    Γ ⊢[PRAAx] regularRows gammaF leftBody N (data N x) := by
  refine .allI (.impI ?_)
  let K := Syn.shift N
  let y := Syn.shift x
  let i : PTm (n+1) := var 0
  let Δ := lt i K :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (numerator K i) (succ K) := row_source K i Prf.hyp0
  simpa [regularRows,Δ,K,y,i,Syn.shift] using
    point_congr gammaF _ _ (left_at K y i).eqSymm (reference_regular _ _ hs.andE₁ (le_of_lt hs.andE₂))

theorem right_rows (N x : PTm n) :
    Γ ⊢[PRAAx] regularRows gammaF rightBody N (data N x) := by
  refine .allI (.impI ?_)
  let K := Syn.shift N
  let y := Syn.shift x
  let i : PTm (n+1) := var 0
  let Δ := lt i K :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt i K := Prf.hyp0
  simpa [regularRows,Δ,K,y,i,Syn.shift] using
    point_congr gammaF _ _ (right_ascending_at K y i hi).eqSymm (reference_regular _ _ (zero_lt_succ i) (le_trans hi (le_succ_self K)))

theorem pi_rows (N x : PTm n) :
    Γ ⊢[PRAAx] regularRows P piBody N (data N x) := by
  refine .allI (.impI ?_)
  let K := Syn.shift N
  let y := Syn.shift x
  let i : PTm (n+1) := var 0
  let Δ := lt i K :: Γ.map Fm.shift
  simpa [regularRows,Δ,K,y,i,Syn.shift] using
    point_congr P _ _ (pi_at (Γ := Δ) K y i).eqSymm (GaussianGammaHalfPiName.name_regular y)

theorem equal_rows (N x : PTm n) :
    Γ ⊢[PRAAx] equalRows rowF P reflectionBody piBody N (data N x) (data N x) := by
  refine .allI (.impI ?_)
  let K := Syn.shift N
  let y := Syn.shift x
  let i : PTm (n+1) := var 0
  let Δ := lt i K :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (numerator K i) (succ K) := row_source K i Prf.hyp0
  simpa [equalRows,Δ,K,y,i,Syn.shift] using cross_congr rowF P
    (reflection_at K y i).eqSymm (pi_at K y i).eqSymm (reflection_row _ _ _ hs)

theorem products_cross (N x : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent (ProductName (FamilyRow rowF reflectionBody)) (ProductName (FamilyRow P piBody))
      (productData rowF reflectionBody N (data N x)) (productData P piBody N (data N x)) :=
  family_product_cross _ _ _ _ _ _ _ (reflection_rows N x) (pi_rows N x) (equal_rows N x)

theorem actual_Gauss_reflection_family_product_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (crossEquivalent (ProductName (FamilyRow rowF reflectionBody)) (ProductName (FamilyRow P piBody))
        (productData rowF reflectionBody (var 1) (data (var 1) (var 0)))
        (productData P piBody (var 1) (data (var 1) (var 0)))) :=
  closeUniv 2 (products_cross _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaGaussReflectionFamily
