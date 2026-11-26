import IPRADerivations.Analysis.GaussianBarnesCanonicalValue
import IPRADerivations.Analysis.GaussianBarnesCanonicalCenteredHead
import IPRADerivations.Analysis.GaussianBarnesCanonicalHeadExponentialFactors
import IPRADerivations.Analysis.GaussianBarnesCanonicalPrefactorExponentDerivative
import IPRADerivations.Analysis.GaussianGammaFoldedApproximantBalance

/-!
# The original Barnes value as kept powers times one exponential

The exponent combines the original prefactor exponent, the finite
correction and the retained logarithm. This factorization needs no
reciprocal of the kept powers and therefore holds at their zeros.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalSingleExponential

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianBarnesCanonicalBaseProductShift (powerProduct)
open GaussianBarnesCanonicalCorrectionShift (total)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaFiniteApproximantName (exponentialInputData exponential_input)
open GaussianGammaFoldedApproximantBalance (exponential_product_equivalent)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (multiply_associative multiply_commutative)
open GaussianRationalHorner (ofGaussian)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "C" => constantF
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => GaussianRadiusExponentialName.data
local notation "er" => GaussianRadiusExponentialName.name_regular
local notation "A" => GaussianBarnesCanonicalPrefactorInverse.exponentF
local notation "L" => GaussianBarnesCanonicalLogCofinal.nameF
local notation "ld" => GaussianBarnesCanonicalLogCofinal.data
local notation "V" => GaussianBarnesCanonicalValue.nameF
local notation "vd" => GaussianBarnesCanonicalValue.data
local notation "P" => GaussianBarnesCanonicalPrefactor.nameF
local notation "pd" => GaussianBarnesCanonicalPrefactor.data
local notation "H" => GaussianBarnesCanonicalHead.nameF
local notation "hd" => GaussianBarnesCanonicalHead.headData
local notation "T" => GaussianBarnesCanonicalTailExponential.nameF
local notation "td" => GaussianBarnesCanonicalTailExponential.data

def prefactorExponentData (z B : PTm n) : PTm n :=
  GaussianBarnesCanonicalPrefactorExponentDerivative.exponentOf (ofGaussian z B)
    (GaussianBarnesCanonicalPrefactorExponentDerivative.square z B)

def prefixF : PR 2 := addF A C
def prefixData (z R B : PTm n) : PTm n := addData (prefactorExponentData z B) (total z B (initial R))
def exponentF : PR 2 := addF prefixF L
def exponentData (z R B : PTm n) : PTm n := addData (prefixData z R B) (ld z R B)
def nameF : PR 2 := multiplyF C (E exponentF)
def data (z R B : PTm n) : PTm n :=
  multiplyData C (E exponentF) (powerProduct z B (initial R)) (exponentialInputData exponentF (exponentData z R B))

@[simp] theorem subst_exponentData {m : ℕ} (σ : Fin n → PTm m) (z R B : PTm n) :
    Syn.subst σ (exponentData z R B) = exponentData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by
  simp [exponentData,prefixData,prefactorExponentData]

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z R B : PTm n) :
    Syn.subst σ (data z R B) = data (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by
  simp [data,exponentialInputData]

theorem exponent_regular (z R B : PTm n) (hs : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] pointCN exponentF (exponentData z R B) :=
  add_fast _ _ _ _ (add_fast _ _ _ _
    (GaussianBarnesCanonicalPrefactorExponentDerivative.regular _ _) (constant_regular _))
    (GaussianBarnesCanonicalLogCofinal.regular z R B hs)

private theorem exchange (f g h : PR 2) (x y z : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) (hh : Γ ⊢[PRAAx] pointCN h z) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF f (multiplyF g h)) (multiplyF g (multiplyF f h))
      (multiplyData f (multiplyF g h) x (multiplyData g h y z))
      (multiplyData g (multiplyF f h) y (multiplyData f h x z)) := by
  have e₁ := multiply_associative f g h x y z hf hg hh
  have e₂ := multiply_cross (multiplyF f g) (multiplyF g f) h h
    (multiplyData f g x y) (multiplyData g f y x) z z
    (multiply_fast _ _ _ _ hf hg) (multiply_fast _ _ _ _ hg hf) hh hh
    (multiply_commutative f g x y hf hg) (cross_refl h z hh)
  have e₃ := multiply_associative g f h y x z hg hf hh
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ e₁) (cross_trans _ _ _ _ _ _ e₂ e₃)

theorem factorization (z R B : PTm n) (hs : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] crossEquivalent V nameF (vd z R B) (data z R B) := by
  let N := initial R
  let a := prefactorExponentData z B
  let c := total z B N
  let x := ld z R B
  let w := powerProduct z B N
  let p := GaussianBarnesCanonicalPrefactorInverse.exponentRadius z B
  let k := GaussianNameBounds.U C c
  let l := GaussianBarnesCanonicalFiniteLog.radius R
  let ap := ed p a
  let cp := ed k c
  let tp := ed l x
  let F := GaussianBarnesCanonicalHeadExponentialFactors.nameF
  let f := GaussianBarnesCanonicalHeadExponentialFactors.data z B N
  let e := ed (GaussianNameBounds.U prefixF (prefixData z R B)) (prefixData z R B)
  have ai : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input A p a :=
    GaussianBarnesCanonicalPrefactorInverse.exponent_input z B
  have ci := exponential_input C c (constant_regular (Γ := Γ) c)
  have ti := GaussianBarnesCanonicalTailExponential.log_input z R B hs
  have ar : Γ ⊢[PRAAx] pointCN (E A) ap := er A _ _ ai
  have cr : Γ ⊢[PRAAx] pointCN (E C) cp := er C _ _ ci
  have tr : Γ ⊢[PRAAx] pointCN T tp := GaussianBarnesCanonicalTailExponential.regular z R B hs
  have wr := constant_regular (Γ := Γ) w
  have fr : Γ ⊢[PRAAx] pointCN F f := multiply_fast C (E C) w cp wr cr
  have pc : Γ ⊢[PRAAx] crossEquivalent P (E A) (pd z B) ap := GaussianBarnesCanonicalPrefactor.combined z B
  have hc : Γ ⊢[PRAAx] crossEquivalent H F (hd z R B N) f :=
    GaussianBarnesCanonicalHeadExponentialFactors.head_cross z R B N hs
  let h := multiplyData (E A) F ap f
  have rg : Γ ⊢[PRAAx] pointCN (multiplyF (E A) F) h := multiply_fast _ _ _ _ ar fr
  have before := multiply_cross P (E A) H F (pd z B) ap (hd z R B N) f
    (GaussianBarnesCanonicalPrefactor.regular _ _) ar
    (GaussianBarnesCanonicalHead.regular z R B zero N hs) fr pc hc
  have original := multiply_cross GaussianBarnesCanonicalValue.prefixF (multiplyF (E A) F) T T
    (GaussianBarnesCanonicalValue.prefixData z R B) h tp tp
    (GaussianBarnesCanonicalValue.prefix_regular z R B hs) rg tr tr before (cross_refl T tp tr)
  let g := multiplyF (E A) (E C)
  let y := multiplyData (E A) (E C) ap cp
  let b := multiplyData C g w y
  have gr : Γ ⊢[PRAAx] pointCN g y := multiply_fast _ _ _ _ ar cr
  have br : Γ ⊢[PRAAx] pointCN (multiplyF C g) b := multiply_fast _ _ _ _ wr gr
  have swapped := multiply_cross (multiplyF (E A) F) (multiplyF C g) T T
    h b tp tp rg br tr tr (exchange (E A) C (E C) ap w cp ar wr cr) (cross_refl T tp tr)
  have grouped := multiply_associative C g T w y tp wr gr tr
  have pr : Γ ⊢[PRAAx] pointCN prefixF (prefixData z R B) := add_fast A C a c ai.andE₁ ci.andE₁
  have pi := exponential_input prefixF (prefixData z R B) pr
  have pe := exponential_product_equivalent A C prefixF p k
    (GaussianNameBounds.U prefixF (prefixData z R B)) a c (prefixData z R B) ai ci pi (cross_refl _ _ pr)
  have prefixExponential : Γ ⊢[PRAAx] pointCN (E prefixF) e := er _ _ _ pi
  have combined := multiply_cross g (E prefixF) T T y e tp tp gr prefixExponential tr tr pe (cross_refl T tp tr)
  have xr := exponent_regular z R B hs
  have xi := exponential_input exponentF (exponentData z R B) xr
  have exp := exponential_product_equivalent prefixF L exponentF
    (GaussianNameBounds.U prefixF (prefixData z R B)) l (GaussianNameBounds.U exponentF (exponentData z R B))
    (prefixData z R B) x (exponentData z R B) pi ti xi (cross_refl _ _ xr)
  have allExp := cross_trans _ _ _ _ _ _ combined exp
  have final := multiply_cross C C (multiplyF g T) (E exponentF) w w
    (multiplyData g T y tp) (exponentialInputData exponentF (exponentData z R B))
    wr wr (multiply_fast _ _ _ _ gr tr) (er _ _ _ xi) (cross_refl C w wr) allExp
  exact cross_trans _ _ _ _ _ _ original
    (cross_trans _ _ _ _ _ _ swapped (cross_trans _ _ _ _ _ _ grouped final))

theorem actual_Barnes_kept_powers_times_single_exponential_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (let z := var 0
     let R := var 1
     let B := var 2
     source z R B ⟶ crossEquivalent V nameF (vd z R B) (data z R B)) :=
  closeUniv 3 (.impI (factorization _ _ _ Prf.hyp0))

def centeredData (z h R B : PTm n) : PTm n :=
  multiplyData C (E exponentF)
    (GaussianRationalHorner.evaluate (GaussianBarnesCanonicalCenteredHead.polynomial z B (initial R)) (ofGaussian h B))
    (exponentialInputData exponentF (exponentData (ComplexLogarithmRemainder.add z h) R B))

theorem centered_factorization (z h R B : PTm n)
    (hs : Γ ⊢[PRAAx] source (ComplexLogarithmRemainder.add z h) R B) :
    Γ ⊢[PRAAx] crossEquivalent V nameF
      (vd (ComplexLogarithmRemainder.add z h) R B) (centeredData z h R B) := by
  let w := ComplexLogarithmRemainder.add z h
  let e := exponentialInputData exponentF (exponentData w R B)
  have hp := GaussianBarnesCanonicalCenteredHead.original_evaluation z h B (initial R) hs.andE₁
  have changeHead : Γ ⊢[PRAAx] data w R B ≐ centeredData z h R B := by
    change Γ ⊢[PRAAx] multiplyData C (E exponentF) (powerProduct w B (initial R)) e ≐
      multiplyData C (E exponentF)
        (GaussianRationalHorner.evaluate (GaussianBarnesCanonicalCenteredHead.polynomial z B (initial R))
          (ofGaussian h B)) e
    ipra_congr (multiplyData C (E exponentF) (var 0) (var 1) : PTm 2) with [hp.eqSymm,.eqRefl e]
  exact GaussianGammaCompactCutoffAlignment.cross_data_congr V nameF _ _ _ _ (.eqRefl _) changeHead
    (factorization w R B hs)

theorem actual_Barnes_centered_powers_times_single_exponential_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (let z := var 0
     let h := var 1
     let R := var 2
     let B := var 3
     let w := ComplexLogarithmRemainder.add z h
     source w R B ⟶ crossEquivalent V nameF (vd w R B) (centeredData z h R B)) :=
  closeUniv 4 (.impI (centered_factorization _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalSingleExponential
