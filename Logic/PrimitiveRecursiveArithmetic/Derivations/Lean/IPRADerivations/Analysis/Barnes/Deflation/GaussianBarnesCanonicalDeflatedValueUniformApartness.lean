import IPRADerivations.Analysis.Barnes.Deflation.GaussianBarnesCanonicalDeflatedValue
import IPRADerivations.Analysis.Barnes.Deflation.GaussianBarnesCanonicalDeflatedHeadUniform
import IPRADerivations.Analysis.Barnes.Prefactors.GaussianBarnesCanonicalPrefactorUniformApartness

/-!
# Uniform separation of the full deflated Barnes coefficient

The original prefactor, skipped head, isolated row multiplier and
cofinal tail supply apartness certificates depending only on the disk
radius and extracted index. They combine on the exact coefficient
program used in the rational local factorization.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDeflatedValueUniformApartness

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalFactor (source)
open GaussianBarnesCanonicalDeflatedHead (neighborhood)
open GaussianBarnesCanonicalDeflatedValue (nameF data factorizedF factorizedData regular original_factorization
  headCoefficientF headCoefficientData outerF outerData head_coefficient_regular remainingLength)
open GaussianNameArithmetic (multiply_fast)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNameReciprocal (apart anchor lower)
open GaussianNamedProductApartness (late_lower)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "U" => GaussianBarnesCanonicalDeflatedFactor.nameF
local notation "Ud" => GaussianBarnesCanonicalDeflatedFactor.data
local notation "H" => GaussianBarnesCanonicalDeflatedHead.nameF
local notation "Hd" => GaussianBarnesCanonicalDeflatedHead.data
local notation "P" => GaussianBarnesCanonicalPrefactor.nameF
local notation "Pd" => GaussianBarnesCanonicalPrefactor.data
local notation "T" => GaussianBarnesCanonicalTailExponential.nameF
local notation "Td" => GaussianBarnesCanonicalTailExponential.data
local notation "productHeight" => GaussianNamedProductApartness.height

def height (R m : PTm n) : PTm n :=
  productHeight
    (productHeight (GaussianBarnesCanonicalDeflatedFactor.height R m)
      (GaussianBarnesCanonicalDeflatedHeadUniform.height R m (remainingLength R m)))
    (productHeight (GaussianBarnesCanonicalPrefactorUniformApartness.height R)
      (GaussianBarnesCanonicalTailApartness.height R))

theorem original_apart (z R B m : PTm n) (h : Γ ⊢[PRAAx] source z R B m)
    (hn : Γ ⊢[PRAAx] neighborhood z B m) : Γ ⊢[PRAAx] apart nameF (height R m) (data z R B m) := by
  let r := remainingLength R m
  have hDisk : Γ ⊢[PRAAx] GaussianBarnesCanonicalLogCofinal.source z R B := .andI h.andE₁ h.andE₂.andE₂
  have hp := GaussianBarnesCanonicalPrefactor.regular (Γ := Γ) z B
  have ht := GaussianBarnesCanonicalTailExponential.regular z R B hDisk
  have a := GaussianNamedProductApartness.original_apart U H (Ud z R B m) (Hd z R B m r) _ _
    (GaussianBarnesCanonicalDeflatedFactor.regular z R B m h) (GaussianBarnesCanonicalDeflatedHead.regular z R B m r h)
    (GaussianBarnesCanonicalDeflatedFactor.original_apart z R B m h)
    (GaussianBarnesCanonicalDeflatedHeadUniform.original_apart z R B m r h hn)
  have b := GaussianNamedProductApartness.original_apart P T (Pd z B) (Td z R B) _ _ hp ht
    (GaussianBarnesCanonicalPrefactorUniformApartness.original_apart z R B hDisk)
    (GaussianBarnesCanonicalTailApartness.original_apart z R B hDisk)
  exact GaussianNamedProductApartness.original_apart headCoefficientF outerF _ _ _ _
    (head_coefficient_regular z R B m r h) (multiply_fast P T _ _ hp ht) a b

theorem sample_lower (p z R B m : PTm n) (h : Γ ⊢[PRAAx] source z R B m)
    (hn : Γ ⊢[PRAAx] neighborhood z B m) (hp : Γ ⊢[PRAAx] le (anchor (height R m)) p) :
    Γ ⊢[PRAAx] lower (ap2 nameF p (data z R B m)) (GaussianNameReciprocal.R (height R m)) :=
  late_lower nameF (height R m) (data z R B m) p (regular z R B m h) (original_apart z R B m h hn) hp

theorem actual_Barnes_local_deflation_uniform_apart_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (let z := var 0
     let R := var 1
     let B := var 2
     let m := var 3
     (source z R B m ⋏ neighborhood z B m) ⟶
       (crossEquivalent GaussianBarnesCanonicalValue.nameF factorizedF
         (GaussianBarnesCanonicalValue.data z R B) (factorizedData z R B m) ⋏
       apart nameF (height R m) (data z R B m))) :=
  closeUniv 4 (.impI (.andI (original_factorization _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂)
    (original_apart _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

theorem actual_Barnes_deflated_coefficient_uniform_late_lower_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (let p := var 0
     let z := var 1
     let R := var 2
     let B := var 3
     let m := var 4
     (source z R B m ⋏ (neighborhood z B m ⋏ le (anchor (height R m)) p)) ⟶
       lower (ap2 nameF p (data z R B m)) (GaussianNameReciprocal.R (height R m))) :=
  closeUniv 5 (.impI (sample_lower _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDeflatedValueUniformApartness
