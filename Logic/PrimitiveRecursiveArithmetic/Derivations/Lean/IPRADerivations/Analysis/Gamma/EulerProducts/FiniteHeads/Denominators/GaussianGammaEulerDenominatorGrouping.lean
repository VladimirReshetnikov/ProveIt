import IPRADerivations.Analysis.Gamma.EulerProducts.FiniteHeads.Denominators.GaussianGammaEulerDenominator
import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.FactorOperations.GaussianRationalRectangularProduct

/-!
# Gauss grouping at arbitrary finite Euler cutoffs

For a positive integer multiplier (m), the (m) denominators
at (z/B+r/m), each with (K) factors, group into the original
(mK) factors at (mz/B) with an explicit factor of (m^{mK}).
The cleared identity also holds when a denominator vanishes.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerDenominatorGrouping

open_ipra
open ComplexLogarithmRemainder (scale)
open GaussianGammaEulerDenominator (denominator linearBody linear_at)
open GaussianGammaEulerHeadLower (translated)
open GaussianGammaEulerHeadShift (linear)
open GaussianRationalFiniteProduct (qprod product_zero product_succ product_congr_bounded product_index_congr)
open GaussianRationalFiniteSum (termsEqual)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical ofGaussian_represents qmul canonical_unique
  represents_congr represents_rescale positive_product)
open GaussianRationalNaturalScale (natScale_canonical natScale_as_product natScale_represents naturalPoint)
open GaussianRationalPowerAlgebra (power_composition qmul_shuffle)
open GaussianRationalReciprocal (power power_zero power_succ powerF)
open GaussianRationalRectangularProduct (blockEntry block_entry_at swap swap_at row rowBody row_at rectangle
  rectangleBody rectangle_at transpose blocks)
open GaussianRationalSyntheticDivision (qone qone_canonical qmul_congr)
open GaussianRootAlgebra (equal_of_values re_add im_add re_scale im_scale)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def scaledBody (t : PTm 2) : PTm 2 :=
  qmul (fstT (var 1)) (inst2 t (var 0) (sndT (var 1)))

theorem scaled_at (t : PTm 2) (i c x : PTm n) : Γ ⊢[PRAAx]
    inst2 (scaledBody t) i (pairT c x) ≐ qmul c (inst2 t i x) := by
  change Γ ⊢[PRAAx] Syn.subst ![i,pairT c x]
    (qmul (fstT (var 1)) (inst2 t (var 0) (sndT (var 1)))) ≐ qmul c (inst2 t i x)
  rw [GaussianRationalHorner.subst_qmul,subst_fstT,subst_inst2,subst_sndT]
  exact qmul_congr (fst_pair c x) (congrInst2 t (.eqRefl i) (snd_pair c x))

def scaleLaw (t : PTm 2) (N c x : PTm n) : Fm PTm n :=
  qprod (scaledBody t) N (pairT c x) ≐ qmul (power c N) (qprod t N x)

ipra_subst scaleLaw [power]

theorem scaled_product (t : PTm 2) (N c x : PTm n) : Γ ⊢[PRAAx] scaleLaw t N c x := by
  have all : Γ ⊢[PRAAx] .all (scaleLaw t (var 0) (Syn.shift c) (Syn.shift x)) := by
    ipra_qfind [subst_scaleLaw]
    · exact (product_zero (scaledBody t) (pairT c x)).eqTrans
        ((qmul_congr (power_zero c) (product_zero t x)).eqTrans
          (GaussianReciprocalHorner.qmul_one_right qone qone_canonical)).eqSymm
    · exact (product_succ (scaledBody t) (var 0) (pairT (Syn.shift c) (Syn.shift x))).eqTrans
        ((qmul_congr Prf.hyp0 (scaled_at t (var 0) (Syn.shift c) (Syn.shift x))).eqTrans
          ((qmul_shuffle _ _ _ _).eqTrans
            (qmul_congr (power_succ _ _).eqSymm (product_succ t _ _).eqSymm)))
  simpa only [subst_scaleLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

def shiftedNumerator (z B m r : PTm n) : PTm n := translated (scale m z) B r
def shiftedData (z B m K : PTm n) : PTm n := pairT K (pairT m (pairT z B))
def shiftedBody : PTm 2 := denominator
  (shiftedNumerator (fstT (sndT (sndT (var 1)))) (sndT (sndT (sndT (var 1))))
    (fstT (sndT (var 1))) (var 0))
  (sndT (sndT (sndT (var 1)))*fstT (sndT (var 1))) (fstT (var 1))
def grouped (z B m K : PTm n) : PTm n := qprod shiftedBody m (shiftedData z B m K)

ipra_subst shiftedData

theorem shifted_at (r z B m K : PTm n) : Γ ⊢[PRAAx]
    inst2 shiftedBody r (shiftedData z B m K) ≐ denominator (shiftedNumerator z B m r) (B*m) K := by
  let X := shiftedData z B m K
  have p := snd_pair (Γ := Γ) K (pairT m (pairT z B))
  have v := p.sndE
  have e := Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
    (denominator (shiftedNumerator (var 0) (var 1) (var 2) (var 3)) (var 1*var 2) (var 4) : PTm 5)
    (σ := ![fstT (sndT (sndT X)),sndT (sndT (sndT X)),fstT (sndT X),r,fstT X])
    (σ' := ![z,B,m,r,K]) (fun i => by
      fin_cases i
      · exact v.fstE
      · exact v.sndE
      · exact p.fstE
      · exact .eqRefl _
      · exact fst_pair _ _)
  simpa [shiftedBody,shiftedNumerator,inst2,X] using e

theorem translated_shift (z B m r j : PTm n) : Γ ⊢[PRAAx] GaussianRootAlgebra.equal
    (translated (shiftedNumerator z B m r) (B*m) j) (translated (scale m z) B (m*j+r)) := by
  apply equal_of_values <;>
    simp only [shiftedNumerator,translated,re_add,im_add,re_scale,im_scale] <;> ipra_simps <;> ring

theorem factor_group (z B m r j : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] qmul (naturalPoint m) (linear (shiftedNumerator z B m r) (B*m) j) ≐
      linear (scale m z) B (m*j+r) := by
  let a := translated (shiftedNumerator z B m r) (B*m) j
  let b := translated (scale m z) B (m*j+r)
  let q := linear (shiftedNumerator z B m r) (B*m) j
  let v := linear (scale m z) B (m*j+r)
  have hd := positive_product B m hB hm
  have lhs := natScale_represents m q a (B*m) hd (ofGaussian_represents _ _ hd)
  have rhs := represents_rescale v b B m (ofGaussian_represents _ _ hB)
  have eq : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (scale m a) (scale m b) := by
    have h := translated_shift (Γ := Γ) z B m r j
    exact equal_of_values (by rw [re_scale,re_scale,GaussianRootAlgebra.equal_re h])
      (by rw [im_scale,im_scale,GaussianRootAlgebra.equal_im h])
  exact (natScale_as_product m q).eqSymm.eqTrans
    (canonical_unique _ _ _ _ (natScale_canonical _ _) (ofGaussian_canonical _ _ hB) hd
      (represents_congr (.eqRefl _) eq (.eqRefl _) lhs) rhs)

theorem column_group (z B m r K : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] row (swap (blockEntry linearBody)) r K (pairT m (pairT (scale m z) B)) ≐
      qmul (power (naturalPoint m) K) (denominator (shiftedNumerator z B m r) (B*m) K) := by
  let v := swap (blockEntry linearBody)
  let Q := pairT m (pairT (scale m z) B)
  let W := pairT (shiftedNumerator z B m r) (B*m)
  have same : Γ ⊢[PRAAx] termsEqual (rowBody v) (scaledBody linearBody) K (pairT r Q) (pairT (naturalPoint m) W) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift K) :: Γ.map Fm.shift
    let a := Syn.shift z
    let b := Syn.shift B
    let M := Syn.shift m
    let j := Syn.shift r
    have hb : Δ ⊢[PRAAx] le one b := by simpa [Δ,b,Fm.shift,Syn.shift,one] using hB.shift.wk
    have hM : Δ ⊢[PRAAx] le one M := by simpa [Δ,M,Fm.shift,Syn.shift,one] using hm.shift.wk
    have entry : Δ ⊢[PRAAx] inst3 v j (var 0) (pairT M (pairT (scale M a) b)) ≐
        inst2 linearBody (M*var 0+j) (pairT (scale M a) b) := by
      dsimp only [v]
      rw [swap_at]
      exact block_entry_at linearBody M (var 0) j (pairT (scale M a) b)
    have e := (row_at (Γ := Δ) v j (var 0) (pairT M (pairT (scale M a) b))).eqTrans
      (entry.eqTrans (linear_at _ _ _))
    have f := (scaled_at (Γ := Δ) linearBody (var 0) (naturalPoint M) (pairT (shiftedNumerator a b M j) (b*M))).eqTrans
      ((qmul_congr (.eqRefl _) (linear_at _ _ _)).eqTrans (factor_group a b M j (var 0) hb hM))
    simpa [termsEqual,Syn.shift,Δ,Q,W,shiftedNumerator,a,b,M,j] using e.eqTrans f.eqSymm
  exact (product_congr_bounded _ _ _ _ _ same).eqTrans (scaled_product linearBody K (naturalPoint m) W)

theorem denominator_grouping (z B m K : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] denominator (scale m z) B (m*K) ≐ qmul (power (naturalPoint m) (m*K)) (grouped z B m K) := by
  let t := blockEntry linearBody
  let Q := pairT m (pairT (scale m z) B)
  let c := power (naturalPoint m) K
  have same : Γ ⊢[PRAAx] termsEqual (rectangleBody (swap t)) (scaledBody shiftedBody) m (pairT K Q)
      (pairT c (shiftedData z B m K)) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
    let a := Syn.shift z
    let b := Syn.shift B
    let M := Syn.shift m
    let L := Syn.shift K
    have hb : Δ ⊢[PRAAx] le one b := by simpa [Δ,b,Fm.shift,Syn.shift,one] using hB.shift.wk
    have hM : Δ ⊢[PRAAx] le one M := by simpa [Δ,M,Fm.shift,Syn.shift,one] using hm.shift.wk
    have e := (rectangle_at (Γ := Δ) (swap t) (var 0) L (pairT M (pairT (scale M a) b))).eqTrans
      (column_group a b M (var 0) L hb hM)
    have f := (scaled_at (Γ := Δ) shiftedBody (var 0) (power (naturalPoint M) L) (shiftedData a b M L)).eqTrans
      (qmul_congr (.eqRefl _) (shifted_at _ _ _ _ _))
    simpa [termsEqual,Syn.shift,Δ,Q,c,power,a,b,M,L] using e.eqTrans f.eqSymm
  have exponent := (power_composition (Γ := Γ) (naturalPoint m) K m).eqTrans
    (congrAp2 powerF (mul_comm K m) (.eqRefl _))
  exact (blocks linearBody m K (pairT (scale m z) B)).eqSymm.eqTrans
    ((transpose t K m Q).eqTrans ((product_congr_bounded _ _ _ _ _ same).eqTrans
      ((scaled_product shiftedBody m c (shiftedData z B m K)).eqTrans (qmul_congr exponent (.eqRefl _)))))

theorem original_Gauss_Euler_denominator_grouping_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ le one (var 2) ⟶ denominator (scale (var 2) (var 0)) (var 1) (var 2*var 3) ≐
      qmul (power (naturalPoint (var 2)) (var 2*var 3)) (grouped (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (denominator_grouping _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaEulerDenominatorGrouping
