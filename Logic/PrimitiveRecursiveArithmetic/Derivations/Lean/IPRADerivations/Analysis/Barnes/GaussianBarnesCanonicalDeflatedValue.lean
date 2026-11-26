import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalDeflatedFactor
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalDeflatedHead
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalValueZeros

/-!
# Exact local factorization of the original canonical Barnes value

The factor at m is extracted from the original finite head using its
actual internal index. The remaining original ranges, the deflated row,
the prefactor and the cofinal exponential tail give a regular and apart
name on the closed half-unit disk about -m.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDeflatedValue

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalFactor (source)
open GaussianBarnesCanonicalDeflatedFactor (translatedPower)
open GaussianBarnesCanonicalDeflatedHead (neighborhood center_index_bound)
open GaussianBarnesCanonicalLogSchedule (initial initial_radius)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameRingLaws (multiply_associative multiply_commutative)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCompactCutoffAlignment (cross_data_congr)
open GaussianNameReciprocal (apart)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus pred)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "H" => GaussianBarnesCanonicalHead.nameF
local notation "Hd" => GaussianBarnesCanonicalHead.data
local notation "F" => GaussianBarnesCanonicalFactor.nameF
local notation "Fd" => GaussianBarnesCanonicalFactor.data
local notation "U" => GaussianBarnesCanonicalDeflatedFactor.nameF
local notation "Ud" => GaussianBarnesCanonicalDeflatedFactor.data
local notation "C" => GaussianBarnesCanonicalDeflatedFactor.factorizedF
local notation "Cd" => GaussianBarnesCanonicalDeflatedFactor.factorizedData
local notation "S" => GaussianBarnesCanonicalDeflatedHead.nameF
local notation "Sd" => GaussianBarnesCanonicalDeflatedHead.data
local notation "P" => GaussianBarnesCanonicalPrefactor.nameF
local notation "Pd" => GaussianBarnesCanonicalPrefactor.data
local notation "T" => GaussianBarnesCanonicalTailExponential.nameF
local notation "Td" => GaussianBarnesCanonicalTailExponential.data

def headCoefficientF : PR 2 := multiplyF U S
def headCoefficientData (z R B m r : PTm n) : PTm n := multiplyData U S (Ud z R B m) (Sd z R B m r)
def remainingLength (R m : PTm n) : PTm n := monus (initial R) m
def outerF : PR 2 := multiplyF P T
def outerData (z R B : PTm n) : PTm n := multiplyData P T (Pd z B) (Td z R B)

def nameF : PR 2 := multiplyF headCoefficientF outerF
def data (z R B m : PTm n) : PTm n :=
  multiplyData headCoefficientF outerF (headCoefficientData z R B m (remainingLength R m)) (outerData z R B)
def factorizedF : PR 2 := multiplyF constantF nameF
def factorizedData (z R B m : PTm n) : PTm n := multiplyData constantF nameF (translatedPower z B m) (data z R B m)

def height (z R B m : PTm n) : PTm n :=
  GaussianNamedProductApartness.height
    (GaussianNamedProductApartness.height (GaussianBarnesCanonicalDeflatedFactor.height R m)
      (GaussianBarnesCanonicalDeflatedHead.height R B m (remainingLength R m)))
    (GaussianNamedProductApartness.height (GaussianBarnesCanonicalPrefactorInverse.height z B)
      (GaussianBarnesCanonicalTailApartness.height R))

private theorem multiply_data_congr (f g : PR 2) {x x' y y' : PTm n}
    (hx : Γ ⊢[PRAAx] x ≐ x') (hy : Γ ⊢[PRAAx] y ≐ y') :
    Γ ⊢[PRAAx] multiplyData f g x y ≐ multiplyData f g x' y' := by
  simpa only [GaussianNameArithmetic.subst_multiplyData,Syn.subst_var,Matrix.cons_val] using
    Prf.eqCongr (multiplyData f g (var 0) (var 1) : PTm 2) (σ := ![x,y]) (σ' := ![x',y'])
      (fun i => by fin_cases i; exact hx; exact hy)

private theorem head_length_congr (z R B N : PTm n) {a b : PTm n} (e : Γ ⊢[PRAAx] a ≐ b) :
    Γ ⊢[PRAAx] Hd z R B N a ≐ Hd z R B N b := by
  simpa only [GaussianBarnesCanonicalHead.subst_data,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
    Prf.eqCongr1 (Hd (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) (var 0)) e

private theorem head_start_congr (z R B r : PTm n) {a b : PTm n} (e : Γ ⊢[PRAAx] a ≐ b) :
    Γ ⊢[PRAAx] Hd z R B a r ≐ Hd z R B b r := by
  simpa only [GaussianBarnesCanonicalHead.subst_data,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
    Prf.eqCongr1 (Hd (Syn.shift z) (Syn.shift R) (Syn.shift B) (var 0) (Syn.shift r)) e

private theorem factor_index_congr (z R B : PTm n) {a b : PTm n} (e : Γ ⊢[PRAAx] a ≐ b) :
    Γ ⊢[PRAAx] Fd z R B a ≐ Fd z R B b := by
  simpa only [GaussianBarnesCanonicalFactor.subst_data,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
    Prf.eqCongr1 (Fd (Syn.shift z) (Syn.shift R) (Syn.shift B) (var 0)) e

private theorem head_source (z R B m : PTm n) (h : Γ ⊢[PRAAx] source z R B m) :
    Γ ⊢[PRAAx] GaussianBarnesCanonicalHead.source z R B := .andI h.andE₁ h.andE₂.andE₂

private theorem prefix_split (z R B m : PTm n) (hs : Γ ⊢[PRAAx] source z R B m) :
    Γ ⊢[PRAAx] crossEquivalent H (multiplyF H F) (Hd z R B zero m)
      (multiplyData H F (Hd z R B zero (pred m)) (Fd z R B m)) := by
  have e : Γ ⊢[PRAAx] m ≐ succ (pred m) := AnalyticNumberTheory.PNTStageStep.pos_of_one_le hs.andE₂.andE₁
  have factorIndex := (congrSucc (zero_add (pred m))).eqTrans e.eqSymm
  exact cross_data_congr H (multiplyF H F) _ _ _ _ (head_length_congr z R B zero e.eqSymm)
    (multiply_data_congr H F (.eqRefl _) (factor_index_congr z R B factorIndex))
    (GaussianBarnesCanonicalHead.append_cross z R B zero (pred m) (head_source z R B m hs))

theorem head_coefficient_regular (z R B m r : PTm n) (h : Γ ⊢[PRAAx] source z R B m) :
    Γ ⊢[PRAAx] pointCN headCoefficientF (headCoefficientData z R B m r) :=
  multiply_fast U S _ _ (GaussianBarnesCanonicalDeflatedFactor.regular z R B m h)
    (GaussianBarnesCanonicalDeflatedHead.regular z R B m r h)

theorem head_factorization (z R B m r : PTm n) (hs : Γ ⊢[PRAAx] source z R B m) :
    Γ ⊢[PRAAx] crossEquivalent H (multiplyF constantF headCoefficientF) (Hd z R B zero (m+r))
      (multiplyData constantF headCoefficientF (translatedPower z B m) (headCoefficientData z R B m r)) := by
  let a := Hd z R B zero (pred m)
  let b := Fd z R B m
  let c := Hd z R B m r
  let x := translatedPower z B m
  let u := Ud z R B m
  let y := Cd z R B m
  let w := Sd z R B m r
  let K := multiplyF H C
  let t := multiplyData H C a y
  let L := multiplyF C H
  let v := multiplyData C H y a
  let d := Hd z R B zero m
  have hh := head_source z R B m hs
  have ha := GaussianBarnesCanonicalHead.regular z R B zero (pred m) hh
  have hb := GaussianBarnesCanonicalFactor.regular z R B m hs
  have hc := GaussianBarnesCanonicalHead.regular z R B m r hh
  have hx : Γ ⊢[PRAAx] pointCN constantF x := constant_regular x
  have hu := GaussianBarnesCanonicalDeflatedFactor.regular z R B m hs
  have hy : Γ ⊢[PRAAx] pointCN C y := multiply_fast constantF U x u hx hu
  have hw := GaussianBarnesCanonicalDeflatedHead.regular z R B m r hs
  have cut := cross_data_congr H (multiplyF H H) _ _ _ _ (.eqRefl _)
    (multiply_data_congr H H (.eqRefl d) (head_start_congr z R B r (zero_add m)))
    (GaussianBarnesCanonicalHeadSplit.split_cross z R B zero m r hh)
  have inside := multiply_cross H H F C a a b y ha ha hb hy (cross_refl H a ha)
    (GaussianBarnesCanonicalDeflatedFactor.factor_cross z R B m hs)
  have middle := cross_trans H (multiplyF H F) K d _ t (prefix_split z R B m hs) inside
  have ordered := cross_trans H K L d t v middle (multiply_commutative H C a y ha hy)
  have first := cross_trans H (multiplyF H H) (multiplyF L H) _ _ _ cut
    (multiply_cross H L H H d v c c (GaussianBarnesCanonicalHead.regular z R B zero m hh)
      (multiply_fast C H y a hy ha) hc hc ordered (cross_refl H c hc))
  have pull := cross_trans (multiplyF L H) (multiplyF C S) (multiplyF constantF headCoefficientF) _ _ _
    (multiply_associative C H H y a c hy ha hc) (multiply_associative constantF U S x u w hx hu hw)
  exact cross_trans H (multiplyF L H) (multiplyF constantF headCoefficientF) _ _ _ first pull

theorem regular (z R B m : PTm n) (h : Γ ⊢[PRAAx] source z R B m) :
    Γ ⊢[PRAAx] pointCN nameF (data z R B m) :=
  multiply_fast headCoefficientF outerF _ _ (head_coefficient_regular z R B m (remainingLength R m) h)
    (multiply_fast P T _ _ (GaussianBarnesCanonicalPrefactor.regular z B)
      (GaussianBarnesCanonicalTailExponential.regular z R B (head_source z R B m h)))

theorem original_apart (z R B m : PTm n) (h : Γ ⊢[PRAAx] source z R B m)
    (hn : Γ ⊢[PRAAx] neighborhood z B m) : Γ ⊢[PRAAx] apart nameF (height z R B m) (data z R B m) := by
  let r := remainingLength R m
  have hh := head_source z R B m h
  have hp := GaussianBarnesCanonicalPrefactor.regular (Γ := Γ) z B
  have ht := GaussianBarnesCanonicalTailExponential.regular z R B hh
  have a := GaussianNamedProductApartness.original_apart U S (Ud z R B m) (Sd z R B m r) _ _
    (GaussianBarnesCanonicalDeflatedFactor.regular z R B m h) (GaussianBarnesCanonicalDeflatedHead.regular z R B m r h)
    (GaussianBarnesCanonicalDeflatedFactor.original_apart z R B m h) (GaussianBarnesCanonicalDeflatedHead.original_apart z R B m r h hn)
  have b := GaussianNamedProductApartness.original_apart P T (Pd z B) (Td z R B) _ _ hp ht
    (GaussianBarnesCanonicalPrefactorInverse.apart z B) (GaussianBarnesCanonicalTailApartness.original_apart z R B hh)
  exact GaussianNamedProductApartness.original_apart headCoefficientF outerF _ _ _ _
    (head_coefficient_regular z R B m r h) (multiply_fast P T _ _ hp ht) a b

theorem original_factorization (z R B m : PTm n) (hs : Γ ⊢[PRAAx] source z R B m)
    (hn : Γ ⊢[PRAAx] neighborhood z B m) :
    Γ ⊢[PRAAx] crossEquivalent GaussianBarnesCanonicalValue.nameF factorizedF
      (GaussianBarnesCanonicalValue.data z R B) (factorizedData z R B m) := by
  let r := remainingLength R m
  let d := Hd z R B zero (initial R)
  let x := translatedPower z B m
  let y := headCoefficientData z R B m r
  let A := multiplyF constantF headCoefficientF
  let a := multiplyData constantF headCoefficientF x y
  let p := Pd z B
  let t := Td z R B
  let K := multiplyF A P
  let k := multiplyData A P a p
  have hh := head_source z R B m hs
  have hp := GaussianBarnesCanonicalPrefactor.regular (Γ := Γ) z B
  have ht := GaussianBarnesCanonicalTailExponential.regular z R B hh
  have hx : Γ ⊢[PRAAx] pointCN constantF x := constant_regular x
  have hy := head_coefficient_regular z R B m r hs
  have ha : Γ ⊢[PRAAx] pointCN A a := multiply_fast constantF headCoefficientF x y hx hy
  have hr : Γ ⊢[PRAAx] le R (initial R) :=
    le_trans (le_congr (one_mul R) (.eqRefl _) (mul_le_mul_right R (le_succ_self one))) (initial_radius R)
  have e : Γ ⊢[PRAAx] initial R ≐ m+r := eq_add_of_le (le_trans (center_index_bound z R B m hs hn) hr)
  have head := cross_data_congr H A _ d _ a (head_length_congr z R B zero e.eqSymm) (.eqRefl _)
    (head_factorization z R B m r hs)
  have prefactored := multiply_cross P P H A p p d a hp hp (GaussianBarnesCanonicalHead.regular z R B zero (initial R) hh) ha
    (cross_refl P p hp) head
  have swap := cross_trans (multiplyF P H) (multiplyF P A) K _ _ k prefactored (multiply_commutative P A p a hp ha)
  have keep := multiply_cross (multiplyF P H) K T T _ k t t (GaussianBarnesCanonicalValue.prefix_regular z R B hh)
    (multiply_fast A P a p ha hp) ht ht swap (cross_refl T t ht)
  have regroup := cross_trans (multiplyF K T) (multiplyF A outerF) factorizedF _ _ _
    (multiply_associative A P T a p t ha hp ht)
    (multiply_associative constantF headCoefficientF outerF x y (outerData z R B) hx hy (multiply_fast P T p t hp ht))
  exact cross_trans GaussianBarnesCanonicalValue.nameF (multiplyF K T) factorizedF _ _ _ keep regroup

theorem actual_Barnes_value_local_deflation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (let z := var 0
     let R := var 1
     let B := var 2
     let m := var 3
     (source z R B m ⋏ neighborhood z B m) ⟶
       (crossEquivalent GaussianBarnesCanonicalValue.nameF factorizedF
        (GaussianBarnesCanonicalValue.data z R B) (factorizedData z R B m) ⋏
       apart nameF (height z R B m) (data z R B m))) :=
  closeUniv 4 (.impI (.andI (original_factorization _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂)
    (original_apart _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDeflatedValue
