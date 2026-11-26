import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalValue
import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalCenteredHead
import IPRADerivations.Analysis.Barnes.HeadProducts.GaussianBarnesCanonicalHeadExponentialFactors
import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalPrefactorExponentDerivative
import IPRADerivations.Analysis.Gamma.GaussianGammaFoldedApproximantBalance

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

theorem prefix_regular (z R B : PTm n) : Γ ⊢[PRAAx] pointCN prefixF (prefixData z R B) :=
  add_fast A C _ _ (GaussianBarnesCanonicalPrefactorExponentDerivative.regular _ _) (constant_regular _)

/-- Separate the retained powers from the exponential of their correction and the prefactor. -/
theorem prefix_factorization (z R B : PTm n) (hs : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] crossEquivalent GaussianBarnesCanonicalValue.prefixF (multiplyF C (E prefixF))
      (GaussianBarnesCanonicalValue.prefixData z R B)
      (multiplyData C (E prefixF) (powerProduct z B (initial R))
        (exponentialInputData prefixF (prefixData z R B))) := by
  let N := initial R
  let a := prefactorExponentData z B
  let c := total z B N
  let w := powerProduct z B N
  let p := GaussianBarnesCanonicalPrefactorInverse.exponentRadius z B
  let k := GaussianNameBounds.U C c
  let ap := ed p a
  let cp := ed k c
  let F := GaussianBarnesCanonicalHeadExponentialFactors.nameF
  let f := GaussianBarnesCanonicalHeadExponentialFactors.data z B N
  let g := multiplyF (E A) (E C)
  let y := multiplyData (E A) (E C) ap cp
  let e := exponentialInputData prefixF (prefixData z R B)
  have ai := GaussianBarnesCanonicalPrefactorInverse.exponent_input (Γ := Γ) z B
  have ci := exponential_input C c (constant_regular (Γ := Γ) c)
  have ar := er A _ _ ai
  have cr := er C _ _ ci
  have wr := constant_regular (Γ := Γ) w
  have fr : Γ ⊢[PRAAx] pointCN F f := multiply_fast C (E C) w cp wr cr
  have pc := GaussianBarnesCanonicalPrefactor.combined (Γ := Γ) z B
  have hc := GaussianBarnesCanonicalHeadExponentialFactors.head_cross z R B N hs
  have first := multiply_cross P (E A) H F (pd z B) ap (hd z R B N) f
    (GaussianBarnesCanonicalPrefactor.regular _ _) ar
    (GaussianBarnesCanonicalHead.regular z R B zero N hs) fr pc hc
  have pr := prefix_regular (Γ := Γ) z R B
  have pi := exponential_input prefixF (prefixData z R B) pr
  have pe := exponential_product_equivalent A C prefixF p k (GaussianNameBounds.U prefixF (prefixData z R B))
    a c (prefixData z R B) ai ci pi (cross_refl _ _ pr)
  have last := multiply_cross C C g (E prefixF) w w y e wr wr
    (multiply_fast _ _ _ _ ar cr) (er _ _ _ pi) (cross_refl _ _ wr) pe
  exact cross_trans _ _ _ _ _ _ first
    (cross_trans _ _ _ _ _ _ (exchange (E A) C (E C) ap w cp ar wr cr) last)

theorem factorization (z R B : PTm n) (hs : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] crossEquivalent V nameF (vd z R B) (data z R B) := by
  let w := powerProduct z B (initial R)
  let e := exponentialInputData prefixF (prefixData z R B)
  let t := td z R B
  let p := multiplyData C (E prefixF) w e
  let x := exponentData z R B
  let y := exponentialInputData exponentF x
  have wr := constant_regular (Γ := Γ) w
  have pi := exponential_input prefixF (prefixData z R B) (prefix_regular (Γ := Γ) z R B)
  have erp : Γ ⊢[PRAAx] pointCN (E prefixF) e := er _ _ _ pi
  have tr := GaussianBarnesCanonicalTailExponential.regular z R B hs
  have first := multiply_cross GaussianBarnesCanonicalValue.prefixF (multiplyF C (E prefixF)) T T
    (GaussianBarnesCanonicalValue.prefixData z R B) p t t
    (GaussianBarnesCanonicalValue.prefix_regular z R B hs) (multiply_fast _ _ _ _ wr erp) tr tr
    (prefix_factorization z R B hs) (cross_refl _ _ tr)
  have grouped := multiply_associative C (E prefixF) T w e t wr erp tr
  have xr := exponent_regular z R B hs
  have xi := exponential_input exponentF x xr
  have exp := exponential_product_equivalent prefixF L exponentF
    (GaussianNameBounds.U prefixF (prefixData z R B)) (GaussianBarnesCanonicalFiniteLog.radius R)
    (GaussianNameBounds.U exponentF x) (prefixData z R B) (ld z R B) x
    pi (GaussianBarnesCanonicalTailExponential.log_input z R B hs) xi (cross_refl _ _ xr)
  have last := multiply_cross C C (multiplyF (E prefixF) T) (E exponentF) w w
    (multiplyData (E prefixF) T e t) y wr wr (multiply_fast _ _ _ _ erp tr) (er _ _ _ xi)
    (cross_refl _ _ wr) exp
  exact cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _ grouped last)

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
