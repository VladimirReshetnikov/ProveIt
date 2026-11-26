/-
A local logarithmic increment for the original Barnes evaluator.
The kept base powers use Mercator on their relative displacement. The
prefactor, finite correction and cofinal tail use their original exponents.
-/
import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalHeadRelativeLog
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalHeadExponentialFactors
import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalPrefactorExponentDerivative
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalValue
import IPRADerivations.Analysis.Gamma.GaussianGammaRationalRatioBinding
import IPRADerivations.Analysis.Gamma.GaussianGammaFoldedApproximantBalance

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalRelativeLogIncrement

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add)
open GaussianBarnesCanonicalBaseProductShift (powerProduct)
open GaussianBarnesCanonicalCorrectionShift (total)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaFiniteApproximantName (exponentialInputData exponential_input)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianRationalHorner (ofGaussian)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "C" => constantF
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => GaussianRadiusExponentialName.data
local notation "inp" => GaussianRadiusExponentialName.input
local notation "ereg" => GaussianRadiusExponentialName.name_regular
local notation "Diff" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data
local notation "Log" => GaussianBarnesCanonicalHeadRelativeLog.nameF
local notation "V" => GaussianBarnesCanonicalValue.nameF
local notation "vd" => GaussianBarnesCanonicalValue.data
local notation "P" => GaussianBarnesCanonicalPrefactor.nameF
local notation "pd" => GaussianBarnesCanonicalPrefactor.data
local notation "H" => GaussianBarnesCanonicalHead.nameF
local notation "hd" => GaussianBarnesCanonicalHead.headData
local notation "L" => GaussianBarnesCanonicalLogCofinal.nameF
local notation "ld" => GaussianBarnesCanonicalLogCofinal.data
local notation "T" => GaussianBarnesCanonicalTailExponential.nameF
local notation "td" => GaussianBarnesCanonicalTailExponential.data
local notation "tailRadius" => GaussianBarnesCanonicalFiniteLog.radius
local notation "exponentF" => GaussianBarnesCanonicalPrefactorInverse.exponentF

def exponentData (z B : PTm n) : PTm n :=
  GaussianBarnesCanonicalPrefactorExponentDerivative.exponentOf (ofGaussian z B)
    (GaussianBarnesCanonicalPrefactorExponentDerivative.square z B)

def prefactorF : PR 2 := Diff exponentF exponentF
def prefactorData (z h B : PTm n) : PTm n :=
  dd (exponentData (add z h) B) (exponentData z B)

def correctionF : PR 2 := Diff C C
def correctionData (z h B N : PTm n) : PTm n := dd (total (add z h) B N) (total z B N)

def headF : PR 2 := addF Log correctionF
def headData (z h B N : PTm n) : PTm n :=
  addData (GaussianBarnesCanonicalHeadRelativeLog.data z h B N) (correctionData z h B N)

def prefixF : PR 2 := addF prefactorF headF
def prefixData (z h R B : PTm n) : PTm n :=
  addData (prefactorData z h B) (headData z h B (initial R))

def tailF : PR 2 := Diff L L
def tailData (z h R B : PTm n) : PTm n := dd (ld (add z h) R B) (ld z R B)

def nameF : PR 2 := addF prefixF tailF
def data (z h R B : PTm n) : PTm n := addData (prefixData z h R B) (tailData z h R B)
def expData (z h R B : PTm n) : PTm n := exponentialInputData nameF (data z h R B)

def source (z h R B : PTm n) : Fm PTm n :=
  GaussianBarnesCanonicalLogCofinal.source z R B ⋏
  (GaussianBarnesCanonicalLogCofinal.source (add z h) R B ⋏
    GaussianBarnesCanonicalHeadRelativeLog.source z h B (initial R))

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z h R B : PTm n) :
    (source z h R B).subst σ = source (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) := by simp [source]

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z h R B : PTm n) :
    Syn.subst σ (data z h R B) = data (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) := by
  simp [data,prefixData,tailData,prefactorData,headData,correctionData,exponentData]

@[simp] theorem subst_expData {m : ℕ} (σ : Fin n → PTm m) (z h R B : PTm n) :
    Syn.subst σ (expData z h R B) = expData (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) := by
  simp [expData,exponentialInputData]

private theorem exponent_regular (z B : PTm n) : Γ ⊢[PRAAx] pointCN exponentF (exponentData z B) :=
  GaussianBarnesCanonicalPrefactorExponentDerivative.regular _ _

theorem prefactor_regular (z h B : PTm n) : Γ ⊢[PRAAx] pointCN prefactorF (prefactorData z h B) :=
  GaussianNamedDifference.name_regular _ _ _ _ (exponent_regular _ _) (exponent_regular _ _)

theorem correction_regular (z h B N : PTm n) : Γ ⊢[PRAAx] pointCN correctionF (correctionData z h B N) :=
  GaussianNamedDifference.name_regular _ _ _ _ (constant_regular _) (constant_regular _)

theorem head_regular (z h B N : PTm n) (hs : Γ ⊢[PRAAx] GaussianBarnesCanonicalHeadRelativeLog.source z h B N) :
    Γ ⊢[PRAAx] pointCN headF (headData z h B N) :=
  add_fast _ _ _ _ (GaussianBarnesCanonicalHeadRelativeLog.regular z h B N hs) (correction_regular _ _ _ _)

theorem prefix_regular (z h R B : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianBarnesCanonicalHeadRelativeLog.source z h B (initial R)) :
    Γ ⊢[PRAAx] pointCN prefixF (prefixData z h R B) :=
  add_fast _ _ _ _ (prefactor_regular _ _ _) (head_regular _ _ _ _ hs)

theorem tail_regular (z h R B : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianBarnesCanonicalLogCofinal.source z R B)
    (hw : Γ ⊢[PRAAx] GaussianBarnesCanonicalLogCofinal.source (add z h) R B) :
    Γ ⊢[PRAAx] pointCN tailF (tailData z h R B) :=
  GaussianNamedDifference.name_regular _ _ _ _
    (GaussianBarnesCanonicalLogCofinal.regular _ _ _ hw) (GaussianBarnesCanonicalLogCofinal.regular _ _ _ hz)

theorem regular (z h R B : PTm n) (hs : Γ ⊢[PRAAx] source z h R B) :
    Γ ⊢[PRAAx] pointCN nameF (data z h R B) :=
  add_fast _ _ _ _ (prefix_regular _ _ _ _ hs.andE₂.andE₂) (tail_regular _ _ _ _ hs.andE₁ hs.andE₂.andE₁)

private theorem difference_shift (f : PR 2) (x y R S : PTm n)
    (hx : Γ ⊢[PRAAx] inp f R x) (hy : Γ ⊢[PRAAx] inp f S y) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF (E (Diff f f)) (E f)) (E f)
      (multiplyData (E (Diff f f)) (E f) (exponentialInputData (Diff f f) (dd y x)) (ed R x))
      (ed S y) := by
  have h := GaussianNamedDifference.name_regular f f y x hy.andE₁ hx.andE₁
  exact GaussianGammaFoldedApproximantBalance.exponential_product_equivalent (Diff f f) f f
    (U (Diff f f) (dd y x)) R S (dd y x) x y (exponential_input _ _ h) hx hy
    (GaussianGammaRationalRatioBinding.difference_add_recover f f y x hy.andE₁ hx.andE₁)

private theorem product_shift (f g A B : PR 2) (x y R S K a b a' b' : PTm n)
    (hx : Γ ⊢[PRAAx] inp f R x) (hy : Γ ⊢[PRAAx] inp g S y)
    (hz : Γ ⊢[PRAAx] inp (addF f g) K (addData x y))
    (ha : Γ ⊢[PRAAx] pointCN A a) (hb : Γ ⊢[PRAAx] pointCN B b)
    (ha' : Γ ⊢[PRAAx] pointCN A a') (hb' : Γ ⊢[PRAAx] pointCN B b')
    (hA : Γ ⊢[PRAAx] crossEquivalent (multiplyF (E f) A) A (multiplyData (E f) A (ed R x) a) a')
    (hB : Γ ⊢[PRAAx] crossEquivalent (multiplyF (E g) B) B (multiplyData (E g) B (ed S y) b) b') :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF (E (addF f g)) (multiplyF A B)) (multiplyF A B)
      (multiplyData (E (addF f g)) (multiplyF A B) (ed K (addData x y)) (multiplyData A B a b))
      (multiplyData A B a' b') := by
  let ex := ed R x
  let ey := ed S y
  let ez := ed K (addData x y)
  have RX := ereg f R x hx
  have RY := ereg g S y hy
  have RZ := ereg (addF f g) K (addData x y) hz
  have HXY := multiply_fast (E f) (E g) ex ey RX RY
  have HAB := multiply_fast A B a b ha hb
  have sum := GaussianGammaFoldedApproximantBalance.exponential_product_equivalent f g (addF f g)
    R S K x y (addData x y) hx hy hz (cross_refl _ _ hz.andE₁)
  have split := multiply_cross (E (addF f g)) (multiplyF (E f) (E g)) (multiplyF A B) (multiplyF A B)
    ez (multiplyData (E f) (E g) ex ey) (multiplyData A B a b) (multiplyData A B a b)
    RZ HXY HAB HAB (cross_symm _ _ _ _ sum) (cross_refl _ _ HAB)
  have exchange := GaussianGammaReciprocalInverse.named_product_exchange (E f) (E g) A B ex ey a b RX RY ha hb
  have lift := multiply_cross (multiplyF (E f) A) A (multiplyF (E g) B) B
    (multiplyData (E f) A ex a) a' (multiplyData (E g) B ey b) b'
    (multiply_fast _ _ _ _ RX ha) ha' (multiply_fast _ _ _ _ RY hb) hb' hA hB
  exact cross_trans _ _ _ _ _ _ split (cross_trans _ _ _ _ _ _ exchange lift)

theorem prefactor_shift (z h B : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF (E prefactorF) P) P
      (multiplyData (E prefactorF) P (exponentialInputData prefactorF (prefactorData z h B)) (pd z B))
      (pd (add z h) B) := by
  let w := add z h
  let x := exponentData z B
  let y := exponentData w B
  let p := GaussianBarnesCanonicalPrefactorInverse.exponentRadius z B
  let q := GaussianBarnesCanonicalPrefactorInverse.exponentRadius w B
  let X := GaussianBarnesCanonicalPrefactor.combinedData z B
  let Y := GaussianBarnesCanonicalPrefactor.combinedData w B
  let u := exponentialInputData prefactorF (prefactorData z h B)
  have hx : Γ ⊢[PRAAx] inp exponentF p x := GaussianBarnesCanonicalPrefactorInverse.exponent_input z B
  have hy : Γ ⊢[PRAAx] inp exponentF q y := GaussianBarnesCanonicalPrefactorInverse.exponent_input w B
  have hu : Γ ⊢[PRAAx] pointCN (E prefactorF) u :=
    ereg _ _ _ (exponential_input _ _ (prefactor_regular z h B))
  have e := multiply_cross (E prefactorF) (E prefactorF) P (E exponentF) u u (pd z B) X
    hu hu (GaussianBarnesCanonicalPrefactor.regular z B) (ereg _ _ _ hx)
    (cross_refl _ _ hu) (GaussianBarnesCanonicalPrefactor.combined z B)
  exact cross_trans _ _ _ _ _ _ e (cross_trans _ _ _ _ _ _
    (difference_shift exponentF x y p q hx hy)
    (cross_symm P (E exponentF) (pd w B) Y (GaussianBarnesCanonicalPrefactor.combined w B)))

theorem head_shift (z h R B N : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianBarnesCanonicalHead.source z R B)
    (hw : Γ ⊢[PRAAx] GaussianBarnesCanonicalHead.source (add z h) R B)
    (hs : Γ ⊢[PRAAx] GaussianBarnesCanonicalHeadRelativeLog.source z h B N) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF (E headF) H) H
      (multiplyData (E headF) H (exponentialInputData headF (headData z h B N)) (hd z R B N))
      (hd (add z h) R B N) := by
  let w := add z h
  let x := GaussianBarnesCanonicalHeadRelativeLog.data z h B N
  let y := correctionData z h B N
  let u := headData z h B N
  let a := total z B N
  let b := total w B N
  let Q := GaussianBarnesCanonicalHeadExponentialFactors.nameF
  let A := GaussianBarnesCanonicalHeadExponentialFactors.data z B N
  let B' := GaussianBarnesCanonicalHeadExponentialFactors.data w B N
  have hx := GaussianBarnesCanonicalHeadRelativeLog.exp_input z h B N hs
  have hy := exponential_input correctionF y (correction_regular (Γ := Γ) z h B N)
  have hu := exponential_input headF u (head_regular z h B N hs)
  have ha := exponential_input C a (constant_regular (Γ := Γ) a)
  have hb := exponential_input C b (constant_regular (Γ := Γ) b)
  have lift := product_shift Log correctionF C (E C) x y one (U correctionF y) (U headF u)
    (powerProduct z B N) (exponentialInputData C a) (powerProduct w B N) (exponentialInputData C b)
    hx hy hu (constant_regular _) (ereg _ _ _ ha) (constant_regular _) (ereg _ _ _ hb)
    (GaussianBarnesCanonicalHeadRelativeLog.exponential_restores z h B N hs)
    (difference_shift C a b (U C a) (U C b) ha hb)
  have pre := multiply_cross (E headF) (E headF) H Q (exponentialInputData headF u) (exponentialInputData headF u)
    (hd z R B N) A (ereg _ _ _ hu) (ereg _ _ _ hu)
    (GaussianBarnesCanonicalHead.regular z R B zero N hz) (GaussianBarnesCanonicalHeadExponentialFactors.regular z B N)
    (cross_refl _ _ (ereg _ _ _ hu)) (GaussianBarnesCanonicalHeadExponentialFactors.head_cross z R B N hz)
  exact cross_trans _ _ _ _ _ _ pre (cross_trans _ _ _ _ _ _ lift
    (cross_symm H Q (hd w R B N) B' (GaussianBarnesCanonicalHeadExponentialFactors.head_cross w R B N hw)))

theorem prefix_shift (z h R B : PTm n) (hs : Γ ⊢[PRAAx] source z h R B) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF (E prefixF) GaussianBarnesCanonicalValue.prefixF)
      GaussianBarnesCanonicalValue.prefixF
      (multiplyData (E prefixF) GaussianBarnesCanonicalValue.prefixF (exponentialInputData prefixF (prefixData z h R B))
        (GaussianBarnesCanonicalValue.prefixData z R B))
      (GaussianBarnesCanonicalValue.prefixData (add z h) R B) := by
  let w := add z h
  let N := initial R
  let x := prefactorData z h B
  let y := headData z h B N
  let u := prefixData z h R B
  have hg := hs.andE₂.andE₂
  exact product_shift prefactorF headF P H x y (U prefactorF x) (U headF y) (U prefixF u)
    (pd z B) (hd z R B N) (pd w B) (hd w R B N)
    (exponential_input _ _ (prefactor_regular z h B)) (exponential_input _ _ (head_regular z h B N hg))
    (exponential_input _ _ (prefix_regular z h R B hg))
    (GaussianBarnesCanonicalPrefactor.regular z B) (GaussianBarnesCanonicalHead.regular z R B zero N hs.andE₁)
    (GaussianBarnesCanonicalPrefactor.regular w B) (GaussianBarnesCanonicalHead.regular w R B zero N hs.andE₂.andE₁)
    (prefactor_shift z h B) (head_shift z h R B N hs.andE₁ hs.andE₂.andE₁ hg)

theorem tail_shift (z h R B : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianBarnesCanonicalLogCofinal.source z R B)
    (hw : Γ ⊢[PRAAx] GaussianBarnesCanonicalLogCofinal.source (add z h) R B) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF (E tailF) T) T
      (multiplyData (E tailF) T (exponentialInputData tailF (tailData z h R B)) (td z R B))
      (td (add z h) R B) :=
  difference_shift L (ld z R B) (ld (add z h) R B) (tailRadius R) (tailRadius R)
    (GaussianBarnesCanonicalTailExponential.log_input _ _ _ hz)
    (GaussianBarnesCanonicalTailExponential.log_input _ _ _ hw)

/-- Multiplying by the exponential of the local increment shifts the literal Barnes value. -/
theorem exponential_restores (z h R B : PTm n) (hs : Γ ⊢[PRAAx] source z h R B) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF (E nameF) V) V
      (multiplyData (E nameF) V (expData z h R B) (vd z R B)) (vd (add z h) R B) := by
  let w := add z h
  let x := prefixData z h R B
  let y := tailData z h R B
  let u := data z h R B
  let Q := GaussianBarnesCanonicalValue.prefixF
  let q := @GaussianBarnesCanonicalValue.prefixData n
  have hz := hs.andE₁
  have hw := hs.andE₂.andE₁
  exact product_shift prefixF tailF Q T x y (U prefixF x) (U tailF y) (U nameF u)
    (q z R B) (td z R B) (q w R B) (td w R B)
    (exponential_input _ _ (prefix_regular z h R B hs.andE₂.andE₂))
    (exponential_input _ _ (tail_regular z h R B hz hw)) (exponential_input _ _ (regular z h R B hs))
    (GaussianBarnesCanonicalValue.prefix_regular z R B hz) (GaussianBarnesCanonicalTailExponential.regular z R B hz)
    (GaussianBarnesCanonicalValue.prefix_regular w R B hw) (GaussianBarnesCanonicalTailExponential.regular w R B hw)
    (prefix_shift z h R B hs) (tail_shift z h R B hz hw)

theorem actual_Barnes_relative_logarithm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶
      (pointCN nameF (data (var 0) (var 1) (var 2) (var 3)) ⋏
        crossEquivalent (multiplyF (E nameF) V) V
          (multiplyData (E nameF) V (expData (var 0) (var 1) (var 2) (var 3)) (vd (var 0) (var 2) (var 3)))
          (vd (add (var 0) (var 1)) (var 2) (var 3)))) :=
  closeUniv 4 (.impI (.andI (regular _ _ _ _ Prf.hyp0) (exponential_restores _ _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalRelativeLogIncrement
