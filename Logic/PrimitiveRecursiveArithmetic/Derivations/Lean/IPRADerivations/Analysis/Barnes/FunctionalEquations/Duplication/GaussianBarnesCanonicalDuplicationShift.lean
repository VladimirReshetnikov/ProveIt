import IPRADerivations.Analysis.Barnes.FunctionalEquations.Hyperfactorial.GaussianBarnesCanonicalHyperfactorialBarnesStep
import IPRADerivations.Analysis.Barnes.FunctionalEquations.Hyperfactorial.GaussianBarnesCanonicalHyperfactorialRecurrence

/-!
# The half-step of the original four-factor Barnes product

For the positive rational argument `z = A/(2B)`, the four retained
Barnes factors give `P₂(z) = (G(z) G(z+1)) G(z+1/2)²`. Exact named
algebra and the original pole-free Barnes recurrence prove the cleared
half-step `P₂(z+1/2) = P₂(z) Gamma(z) Gamma(z+1/2)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDuplicationShift

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalHyperfactorial (barnesData barnes_regular)
open GaussianBarnesCanonicalHyperfactorialBarnesStep (denominator_step)
open GaussianBarnesCanonicalHyperfactorialPowerStep (gammaPowerF gammaPowerData gamma_power_regular)
open GaussianBarnesCanonicalHyperfactorialRecurrence (regroup)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCompactCutoffAlignment (cross_data_congr)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (multiply_associative multiply_commutative)
open GaussianRationalHorner (positive_product)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "G" => GaussianBarnesCanonicalValue.nameF
local notation "L" => gammaPowerF
local notation "M" => multiplyF
local notation "Md" => multiplyData

abbrev pairF : PR 2 := M G G
abbrev nameF : PR 2 := M pairF pairF
abbrev gammaPairF : PR 2 := M L L
abbrev shiftF : PR 2 := M nameF gammaPairF

def data (A B : PTm n) : PTm n :=
  let D := two*B
  let a := barnesData A D
  let b := barnesData (A+B) D
  let c := barnesData (A+D) D
  Md pairF pairF (Md G G a c) (Md G G b b)

def gammaPairData (A B : PTm n) : PTm n :=
  Md L L (gammaPowerData A (two*B)) (gammaPowerData (A+B) (two*B))

def shiftData (A B : PTm n) : PTm n := Md nameF gammaPairF (data A B) (gammaPairData A B)

theorem regular (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] pointCN nameF (data A B) := by
  have hD := positive_product two B (le_succ_self one) hB
  have ha := barnes_regular A (two*B) hD
  have hb := barnes_regular (A+B) (two*B) hD
  have hc := barnes_regular (A+two*B) (two*B) hD
  exact multiply_fast _ _ _ _ (multiply_fast _ _ _ _ ha hc) (multiply_fast _ _ _ _ hb hb)

private theorem swap_trailing (f g h : PR 2) (x y z : PTm n)
    (hx : Γ ⊢[PRAAx] pointCN f x) (hy : Γ ⊢[PRAAx] pointCN g y) (hz : Γ ⊢[PRAAx] pointCN h z) :
    Γ ⊢[PRAAx] crossEquivalent (M (M f g) h) (M (M f h) g)
      (Md (M f g) h (Md f g x y) z) (Md (M f h) g (Md f h x z) y) := by
  have join := multiply_cross f f (M g h) (M h g) x x (Md g h y z) (Md h g z y)
    hx hx (multiply_fast _ _ _ _ hy hz) (multiply_fast _ _ _ _ hz hy)
    (cross_refl _ _ hx) (multiply_commutative g h y z hy hz)
  exact cross_trans _ _ _ _ _ _ (multiply_associative f g h x y z hx hy hz)
    (cross_trans _ _ _ _ _ _ join (cross_symm _ _ _ _ (multiply_associative f h g x z y hx hz hy)))

theorem half_step (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] crossEquivalent nameF shiftF (data (A+B) B) (shiftData A B) := by
  let D := two*B
  let a := barnesData A D
  let b := barnesData (A+B) D
  let c := barnesData (A+D) D
  let d := barnesData ((A+B)+D) D
  let aGamma := gammaPowerData A D
  let bGamma := gammaPowerData (A+B) D
  let ac := Md G G a c
  let bb := Md G G b b
  let cc := Md G G c c
  let bd := Md G G b d
  have hD : Γ ⊢[PRAAx] le one D := positive_product two B (le_succ_self one) hB
  have hB' := le_trans hA (le_add_right A B)
  have ha := barnes_regular A D hD
  have hb := barnes_regular (A+B) D hD
  have hc := barnes_regular (A+D) D hD
  have hd := barnes_regular ((A+B)+D) D hD
  have hag := gamma_power_regular A D hA hD
  have hbg := gamma_power_regular (A+B) D hB' hD
  have hac := multiply_fast G G a c ha hc
  have hbb := multiply_fast G G b b hb hb
  have hcc := multiply_fast G G c c hc hc
  have hbd := multiply_fast G G b d hb hd
  have eq : Γ ⊢[PRAAx] (A+B)+B ≐ A+D := by dsimp [D]; ipra_ring
  have middle : Γ ⊢[PRAAx] barnesData ((A+B)+B) D ≐ c := by
    change Γ ⊢[PRAAx] barnesData ((A+B)+B) D ≐ barnesData (A+D) D
    ipra_congr (barnesData (var 0) (var 1) : PTm 2) with [eq, .eqRefl D]
  have shifted : Γ ⊢[PRAAx] data (A+B) B ≐ Md pairF pairF bd cc := by
    change Γ ⊢[PRAAx]
      Md pairF pairF bd (Md G G (barnesData ((A+B)+B) D) (barnesData ((A+B)+B) D)) ≐
        Md pairF pairF bd (Md G G c c)
    have inner : Γ ⊢[PRAAx]
        Md G G (barnesData ((A+B)+B) D) (barnesData ((A+B)+B) D) ≐ cc := by
      change Γ ⊢[PRAAx] _ ≐ Md G G c c
      ipra_congr (Md G G (var 0) (var 1) : PTm 2) with [middle, middle]
    ipra_congr (Md pairF pairF (var 0) (var 1) : PTm 2) with [.eqRefl bd, inner]
  let ag := Md G L a aGamma
  let bg := Md G L b bGamma
  have exA : Γ ⊢[PRAAx] crossEquivalent G (M G L) c ag := denominator_step A D hA hD
  have exB : Γ ⊢[PRAAx] crossEquivalent G (M G L) d bg := denominator_step (A+B) D hB' hD
  have bgRegular := multiply_fast G L b bGamma hb hbg
  let bbg := Md G (M G L) b bg
  have bdTo : Γ ⊢[PRAAx] crossEquivalent pairF (M G (M G L)) bd bbg :=
    multiply_cross G G G (M G L) b b d bg
    hb hb hd bgRegular (cross_refl _ _ hb) exB
  let bbf := Md pairF L bb bGamma
  let fbb := Md L pairF bGamma bb
  have reduceB : Γ ⊢[PRAAx] crossEquivalent (M G (M G L)) (M L pairF) bbg fbb :=
    cross_trans _ _ _ bbg bbf fbb
    (cross_symm (M pairF L) (M G (M G L)) bbf bbg (multiply_associative G G L b b bGamma hb hb hbg))
    (multiply_commutative pairF L bb bGamma hbb hbg)
  have collapseB : Γ ⊢[PRAAx] crossEquivalent pairF (M L pairF) bd fbb :=
    cross_trans pairF (M G (M G L)) (M L pairF) bd bbg fbb bdTo reduceB
  have htail := multiply_fast L pairF bGamma bb hbg hbb
  have lhs := cross_trans _ _ _ _ _ _ (multiply_commutative pairF pairF bd cc hbd hcc)
    (multiply_cross pairF pairF pairF (M L pairF) cc cc bd fbb
      hcc hcc hbd htail (cross_refl _ _ hcc) collapseB)
  let common := Md pairF (M L pairF) cc fbb
  have lhs' := cross_data_congr nameF (M pairF (M L pairF)) (Md pairF pairF bd cc) (data (A+B) B)
    common common shifted.eqSymm (.eqRefl _) lhs
  have right := regroup pairF pairF L L ac bb aGamma bGamma hac hbb hag hbg
  have aPart := swap_trailing G G L a c aGamma ha hc hag
  have aReduce := multiply_cross (M G L) G G G ag c c c
    (multiply_fast G L a aGamma ha hag) hc hc hc (cross_symm G (M G L) c ag exA) (cross_refl _ _ hc)
  have first := cross_trans _ _ _ _ _ _ aPart aReduce
  have toCommon := multiply_cross (M pairF L) pairF (M L pairF) (M L pairF)
    (Md pairF L ac aGamma) cc fbb fbb (multiply_fast _ _ _ _ hac hag) hcc htail htail
    first (cross_refl _ _ htail)
  have rhs := cross_trans _ _ _ _ _ _ right toCommon
  exact cross_trans _ _ _ _ _ _ lhs' (cross_symm _ _ _ _ rhs)

theorem actual_Barnes_duplication_four_factor_half_step_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (let A := var 0; let B := var 1
       le one A ⟶ le one B ⟶ crossEquivalent nameF shiftF (data (A+B) B) (shiftData A B)) :=
  closeUniv 2 (.impI (.impI (half_step _ _ Prf.hyp0.wk Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDuplicationShift
