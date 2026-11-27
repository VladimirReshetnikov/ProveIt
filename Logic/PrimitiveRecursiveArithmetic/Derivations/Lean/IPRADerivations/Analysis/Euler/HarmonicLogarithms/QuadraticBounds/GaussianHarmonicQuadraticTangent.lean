import IPRADerivations.Analysis.Gamma.EulerProducts.GammaEulerMesh
import IPRADerivations.AnalyticNumberTheory.PhiLower

/-!
# Quadratic tangent bounds on the finite harmonic mesh

For positive mesh indices `v`, `v+j ≤ u ≤ M` and a factorial covering
`M`, these two polynomial inequalities compare the harmonic increment
with the tangent reciprocals. The lower tangent has precisely the
one-mesh endpoint correction needed for the sharp limiting coefficient.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianHarmonicQuadraticTangent

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogSquareSum (S_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Products (fact)
open GammaEulerMesh (factorial_quotient)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def scale (M : PTm n) : PTm n := two*M*M

def upperTangent (j v M L : PTm n) : Fm PTm n :=
  le (scale M*v*S (v+j) (fact L)+v*j*j*fact L)
    (scale M*v*S v (fact L)+scale M*j*fact L)

def lowerTangent (j v u M L : PTm n) : Fm PTm n :=
  le (scale M*u*S v (fact L)+scale M*j*fact L+u*fact L*(two*u*j))
    (scale M*u*S (v+j) (fact L)+u*fact L*(j*(j+one)+two*v*j))

def law (j v u M L : PTm n) : Fm PTm n :=
  le (v+j) u ⟶ upperTangent j v M L ⋏ lowerTangent j v u M L

ipra_subst law [upperTangent, lowerTangent, scale, S]

private theorem base (v u M L : PTm n) : Γ ⊢[PRAAx] law zero v u M L := by
  have eq : Γ ⊢[PRAAx] S (v+zero) (fact L) ≐ S v (fact L) :=
    congrAp2 (sumF hB) (add_zero v) (.eqRefl _)
  have e := natEq eq
  have a : Γ ⊢[PRAAx] upperTangent zero v M L := by
    unfold upperTangent
    ipra_le 0 using rw [e]; ring
  have b : Γ ⊢[PRAAx] lowerTangent zero v u M L := by
    unfold lowerTangent
    ipra_le 0 using rw [e]; ring
  exact .impI (.andI a.wk b.wk)

private theorem upper_step (j v u M L : PTm n)
    (hM : Γ ⊢[PRAAx] le u M) (hL : Γ ⊢[PRAAx] le M L) (h : Γ ⊢[PRAAx] le (v+succ j) u)
    (old : Γ ⊢[PRAAx] upperTangent j v M L) : Γ ⊢[PRAAx] upperTangent (succ j) v M L := by
  let F := fact L
  let V := v+succ j
  let q := quo F V
  have hv : Γ ⊢[PRAAx] le one V := le_trans (zero_lt_succ j) (le_add_left _ _)
  have hVM := le_trans h hM
  have hprod : Γ ⊢[PRAAx] le (v*V) (M*M) := le_mul_mono (le_trans (le_add_right v (succ j)) hVM) hVM
  have se := natEq ((congrAp2 (sumF hB) (add_succ v j) (.eqRefl F)).eqTrans
    ((S_succ (Γ := Γ) (v+j) F).eqTrans (congrAdd (.eqRefl _)
      (congrAp2 quoF (.eqRefl F) (add_succ v j).eqSymm))))
  have fe := natEq (factorial_quotient V L hv (le_trans hVM hL))
  have gap := natEq (eq_add_of_le hprod)
  dsimp only [upperTangent,scale] at old ⊢
  dsimp only [V,F] at fe
  ipra_le sl old+𝔞 q*(2*(𝔞 j+1)*𝔞 (monus (M*M) (v*V))+𝔞 v*𝔞 V) using
    dsimp only [V,F,q] at *
    ipra_simps
    rw [se,←fe] at *
    linear_combination 2*𝔞 (quo (fact L) (v+succ j))*(𝔞 j+1)*gap

private theorem lower_step (j v u M L : PTm n)
    (hM : Γ ⊢[PRAAx] le u M) (hL : Γ ⊢[PRAAx] le M L) (h : Γ ⊢[PRAAx] le (v+succ j) u)
    (old : Γ ⊢[PRAAx] lowerTangent j v u M L) : Γ ⊢[PRAAx] lowerTangent (succ j) v u M L := by
  let F := fact L
  let V := v+succ j
  let q := quo F V
  have hv : Γ ⊢[PRAAx] le one V := le_trans (zero_lt_succ j) (le_add_left _ _)
  have hVM := le_trans h hM
  have hprod : Γ ⊢[PRAAx] le (u*V) (M*M) := le_mul_mono hM hVM
  have se := natEq ((congrAp2 (sumF hB) (add_succ v j) (.eqRefl F)).eqTrans
    ((S_succ (Γ := Γ) (v+j) F).eqTrans (congrAdd (.eqRefl _)
      (congrAp2 quoF (.eqRefl F) (add_succ v j).eqSymm))))
  have fe := natEq (factorial_quotient V L hv (le_trans hVM hL))
  have gu := natEq (eq_add_of_le h)
  have gm := natEq (eq_add_of_le hprod)
  dsimp only [lowerTangent,scale] at old ⊢
  dsimp only [V,F] at fe
  ipra_le sl old+2*𝔞 q*𝔞 (monus (M*M) (u*V))*𝔞 (monus u V) using
    dsimp only [V,F,q] at *
    ipra_simps
    rw [se,←fe] at *
    linear_combination 2*𝔞 (quo (fact L) (v+succ j))*
      ((𝔞 M*𝔞 M-𝔞 u*(𝔞 v+𝔞 j+1))*gu+𝔞 (monus u (v+succ j))*gm)

theorem tangents (j v u M L : PTm n) (hM : Γ ⊢[PRAAx] le u M) (hL : Γ ⊢[PRAAx] le M L)
    (hj : Γ ⊢[PRAAx] le (v+j) u) :
    Γ ⊢[PRAAx] upperTangent j v M L ⋏ lowerTangent j v u M L := by
  let Δ := Γ.map Fm.shift
  let sh (x : PTm n) := Syn.shift x
  have hM' : Δ ⊢[PRAAx] le (sh u) (sh M) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hM.shift
  have hL' : Δ ⊢[PRAAx] le (sh M) (sh L) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hL.shift
  have all : Γ ⊢[PRAAx] .all (law (var 0) (sh v) (sh u) (sh M) (sh L)) := by
    ipra_qfind (by simp [law,upperTangent,lowerTangent,Fm.QF,le]) [subst_law, sh]
    · exact base (Γ := Γ) v u M L
    · refine .impI ?_
      have hprev : le (sh v+succ (var 0)) (sh u) :: law (var 0) (sh v) (sh u) (sh M) (sh L) :: Δ ⊢[PRAAx]
          le (sh v+var 0) (sh u) :=
        le_trans (le_congr (.eqRefl _) (add_succ _ _).eqSymm (le_succ_self _)) Prf.hyp0
      have ih := Prf.hyp1.impE hprev
      exact .andI (upper_step _ _ _ _ _ hM'.wk.wk hL'.wk.wk Prf.hyp0 ih.andE₁)
        (lower_step _ _ _ _ _ hM'.wk.wk hL'.wk.wk Prf.hyp0 ih.andE₂)
  have that : Γ ⊢[PRAAx] law j v u M L := by
    simpa only [subst_law,sh,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
  exact that.impE hj

end LeanProofs.IPRA.Analysis.GaussianHarmonicQuadraticTangent
