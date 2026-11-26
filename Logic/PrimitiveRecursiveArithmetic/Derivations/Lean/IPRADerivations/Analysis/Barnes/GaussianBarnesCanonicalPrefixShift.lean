import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalProduct
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalHeadShift
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalPrefactorShift

/-!
# Cleared unit shift of the original literal Barnes product

The original prefactor shift and the finite head shift combine into
one exponential multiplier. The two literal truncations use the same
cutoff. No value of the plain polynomial or Barnes product is inverted.
-/

set_option autoImplicit false
set_option maxHeartbeats 1300000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPrefixShift

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalHead (source headData)
open GaussianBarnesCanonicalPolynomialShift (plain)
open GaussianBarnesCanonicalBaseProductShift (terminal)
open GaussianBarnesCanonicalProduct (literalData)
open GaussianBarnesCanonicalValue (prefixF)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaEulerHeadLower (translated)
open GaussianGammaFiniteApproximantName (exponentialInputData exponential_input)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (multiply_associative multiply_commutative)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "P" => GaussianBarnesCanonicalPrefactor.nameF
local notation "pd" => GaussianBarnesCanonicalPrefactor.data
local notation "H" => GaussianBarnesCanonicalHead.nameF
local notation "C" => constantF
local notation "Exp" => GaussianRadiusExponentialName.nameF
local notation "ed" => exponentialInputData
local notation "D" => GaussianBarnesCanonicalPrefactorShift.differenceF
local notation "dd" => GaussianBarnesCanonicalPrefactorShift.differenceData

abbrev exponentF : PR 2 := addF D C
def exponentData (z B N : PTm n) : PTm n := addData (dd z B) (GaussianBarnesCanonicalCorrectionShift.exponent z B N)
abbrev multiplierF : PR 2 := multiplyF C (Exp exponentF)
def multiplierData (z B N : PTm n) : PTm n :=
  multiplyData C (Exp exponentF) (terminal z B N) (ed exponentF (exponentData z B N))
abbrev leftF : PR 2 := multiplyF prefixF C
def leftData (z S B N : PTm n) : PTm n := multiplyData prefixF C (literalData (translated z B one) S B N) (plain z B N)
abbrev rightF : PR 2 := multiplyF prefixF multiplierF
def rightData (z R B N : PTm n) : PTm n := multiplyData prefixF multiplierF (literalData z R B N) (multiplierData z B N)

private theorem swap_first (f g h : PR 2) (x y z : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) (hh : Γ ⊢[PRAAx] pointCN h z) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF f (multiplyF g h)) (multiplyF g (multiplyF f h))
      (multiplyData f (multiplyF g h) x (multiplyData g h y z))
      (multiplyData g (multiplyF f h) y (multiplyData f h x z)) := by
  have swap := multiply_cross (multiplyF f g) (multiplyF g f) h h (multiplyData f g x y) (multiplyData g f y x) z z
    (multiply_fast _ _ _ _ hf hg) (multiply_fast _ _ _ _ hg hf) hh hh
    (multiply_commutative f g x y hf hg) (cross_refl _ _ hh)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (multiply_associative f g h x y z hf hg hh))
    (cross_trans _ _ _ _ _ _ swap (multiply_associative g f h y x z hg hf hh))

private theorem regroup (f g h k : PR 2) (x y z t : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hh : Γ ⊢[PRAAx] pointCN h z) (hk : Γ ⊢[PRAAx] pointCN k t) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF (multiplyF f g) (multiplyF h k)) (multiplyF (multiplyF f h) (multiplyF g k))
      (multiplyData (multiplyF f g) (multiplyF h k) (multiplyData f g x y) (multiplyData h k z t))
      (multiplyData (multiplyF f h) (multiplyF g k) (multiplyData f h x z) (multiplyData g k y t)) := by
  let a := multiplyF g (multiplyF h k)
  let b := multiplyF h (multiplyF g k)
  let u := multiplyData g (multiplyF h k) y (multiplyData h k z t)
  let v := multiplyData h (multiplyF g k) z (multiplyData g k y t)
  have hk' := multiply_fast (Γ := Γ) _ _ _ _ hh hk
  have hg' := multiply_fast (Γ := Γ) _ _ _ _ hg hk
  have e := multiply_cross f f a b x x u v hf hf (multiply_fast _ _ _ _ hg hk') (multiply_fast _ _ _ _ hh hg')
    (cross_refl _ _ hf) (swap_first g h k y z t hg hh hk)
  exact cross_trans _ _ _ _ _ _ (multiply_associative f g (multiplyF h k) x y (multiplyData h k z t) hf hg hk')
    (cross_trans _ _ _ _ _ _ e (cross_symm _ _ _ _
      (multiply_associative f h (multiplyF g k) x z (multiplyData g k y t) hf hh hg')))

private theorem multiplier_cross (z B N : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF (Exp D) (multiplyF C (Exp C))) multiplierF
      (multiplyData (Exp D) (multiplyF C (Exp C)) (GaussianBarnesCanonicalPrefactorShift.data z B)
        (GaussianBarnesCanonicalHeadShift.multiplierData z B N)) (multiplierData z B N) := by
  let a := dd z B
  let b := GaussianBarnesCanonicalCorrectionShift.exponent z B N
  let c := exponentData z B N
  let x := ed D a
  let y := ed C b
  let t := terminal z B N
  have ha := GaussianBarnesCanonicalPrefactorShift.difference_regular (Γ := Γ) z B
  have hb := constant_regular (Γ := Γ) b
  have hc := add_fast D C a b ha hb
  have ai := exponential_input D a ha
  have bi := exponential_input C b hb
  have ci := exponential_input exponentF c hc
  have hx := GaussianRadiusExponentialName.name_regular _ _ _ ai
  have hy := GaussianRadiusExponentialName.name_regular _ _ _ bi
  have ht := constant_regular (Γ := Γ) t
  have e := GaussianGammaFoldedApproximantBalance.exponential_product_equivalent D C exponentF (U D a) (U C b)
    (U exponentF c) a b c ai bi ci (cross_refl exponentF c hc)
  exact cross_trans _ _ _ _ _ _ (swap_first (Exp D) C (Exp C) x t y hx ht hy)
    (multiply_cross C C (multiplyF (Exp D) (Exp C)) (Exp exponentF) t t (multiplyData (Exp D) (Exp C) x y)
      (ed exponentF c) ht ht (multiply_fast _ _ _ _ hx hy) (GaussianRadiusExponentialName.name_regular _ _ _ ci)
      (cross_refl _ _ ht) e)

theorem prefix_shift (z R S B N : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source (translated z B one) S B) : Γ ⊢[PRAAx]
    crossEquivalent leftF rightF (leftData z S B N) (rightData z R B N) := by
  let w := translated z B one
  let p := pd z B
  let q := pd w B
  let x := headData z R B N
  let y := headData w S B N
  let a := plain z B N
  let d := GaussianBarnesCanonicalPrefactorShift.data z B
  let e := GaussianBarnesCanonicalHeadShift.multiplierData z B N
  let F := multiplyF C (Exp C)
  let t := GaussianBarnesCanonicalHeadShift.rightData z R B N
  let M := multiplyF (Exp D) F
  let m := multiplyData (Exp D) F d e
  have hp := GaussianBarnesCanonicalPrefactor.regular (Γ := Γ) z B
  have hq := GaussianBarnesCanonicalPrefactor.regular (Γ := Γ) w B
  have hx := GaussianBarnesCanonicalHead.regular z R B zero N h
  have hy := GaussianBarnesCanonicalHead.regular w S B zero N hw
  have ha := constant_regular (Γ := Γ) a
  have hd := GaussianBarnesCanonicalPrefactorShift.regular (Γ := Γ) z B
  have he : Γ ⊢[PRAAx] pointCN F e := multiply_fast C (Exp C) _ _ (constant_regular _)
    (GaussianRadiusExponentialName.name_regular _ _ _ (exponential_input C _ (constant_regular _)))
  have head := multiply_cross P P (multiplyF H C) (multiplyF H F) q q (multiplyData H C y a) t hq hq
    (multiply_fast _ _ _ _ hy ha) (multiply_fast _ _ _ _ hx he) (cross_refl _ _ hq)
    (GaussianBarnesCanonicalHeadShift.head_shift z R S B N h hw)
  have pref := multiply_cross P (multiplyF P (Exp D)) (multiplyF H F) (multiplyF H F) q (multiplyData P (Exp D) p d) t t
    hq (multiply_fast _ _ _ _ hp hd) (multiply_fast _ _ _ _ hx he) (multiply_fast _ _ _ _ hx he)
    (cross_symm _ _ _ _ (GaussianBarnesCanonicalPrefactorShift.prefactor_shift z B))
    (cross_refl _ _ (multiply_fast _ _ _ _ hx he))
  have he' : Γ ⊢[PRAAx] pointCN multiplierF (multiplierData z B N) := multiply_fast _ _ _ _ (constant_regular _)
    (GaussianRadiusExponentialName.name_regular _ _ _ (exponential_input _ _
      (add_fast D C _ _ (GaussianBarnesCanonicalPrefactorShift.difference_regular z B) (constant_regular _))))
  have last := multiply_cross prefixF prefixF M multiplierF (literalData z R B N) (literalData z R B N) m (multiplierData z B N)
    (multiply_fast _ _ _ _ hp hx) (multiply_fast _ _ _ _ hp hx) (multiply_fast _ _ _ _ hd he) he'
    (cross_refl _ _ (multiply_fast _ _ _ _ hp hx)) (multiplier_cross z B N)
  exact cross_trans _ _ _ _ _ _ (multiply_associative P H C q y a hq hy ha)
    (cross_trans _ _ _ _ _ _ head (cross_trans _ _ _ _ _ _ pref
      (cross_trans _ _ _ _ _ _ (regroup P (Exp D) H F p d x e hp hd hx he) last)))

theorem actual_Barnes_literal_prefix_shift_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (let z := var 0
     let R := var 1
     let S := var 2
     let B := var 3
     let N := var 4
     source z R B ⟶ source (translated z B one) S B ⟶ crossEquivalent leftF rightF (leftData z S B N) (rightData z R B N)) :=
  closeUniv 5 (.impI (.impI (prefix_shift _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPrefixShift
