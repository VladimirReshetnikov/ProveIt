import IPRADerivations.Analysis.Gamma.EulerProducts.FiniteHeads.GaussianGammaEulerDenominatorGrouping

/-!
# Exact grouping of the maintained finite Euler heads

At cutoff (L=m(N+1)-1), the head at (mz/B) times (L!) is the
product of shifted heads at cutoff (N) times (m^{m(N+1)}(N!)^m).
This rational identity requires no pole guard.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaGaussEulerHeads

open_ipra
open ComplexLogarithmRemainder (scale)
open GaussianGammaEulerDenominator (denominator_normalization linearBody)
open GaussianGammaEulerDenominatorGrouping (shiftedNumerator shiftedData shiftedBody shifted_at grouped
  scaledBody scaled_at scaled_product denominator_grouping)
open GaussianGammaEulerHead (run program_at)
open GaussianRationalFiniteProduct (qprod product_congr_bounded product_index_congr)
open GaussianRationalFiniteSum (termsEqual)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianRationalReciprocal (power)
open GaussianRationalSyntheticDivision (qmul_congr)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def cutoff (m N : PTm n) : PTm n := pred (m*succ N)

ipra_subst cutoff

theorem cutoff_count (m N : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] m*succ N ≐ succ (cutoff m N) := by
  let d := m*succ N
  have hd : Γ ⊢[PRAAx] le one d := positive_product _ _ hm (zero_lt_succ N)
  have e : Γ ⊢[PRAAx] d ≐ succ (monus d one) := (eq_add_of_le hd).eqTrans
    ((add_comm _ _).eqTrans (succ_eq_add_one _).eqSymm)
  exact e.eqTrans (congrSucc ((pred_succ _).eqSymm.eqTrans (congrPred e.eqSymm)))

def shiftedHeadBody : PTm 2 := run
  (shiftedNumerator (fstT (sndT (sndT (var 1)))) (sndT (sndT (sndT (var 1))))
    (fstT (sndT (var 1))) (var 0))
  (sndT (sndT (sndT (var 1)))*fstT (sndT (var 1))) (fstT (var 1))
def shiftedHeads (z B m N : PTm n) : PTm n := qprod shiftedHeadBody m (shiftedData z B m N)

@[simp] theorem subst_head_run {l : ℕ} (σ : Fin n → PTm l) (z B N : PTm n) :
    Syn.subst σ (run z B N) = run (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) :=
  subst_ap3 σ GaussianGammaEulerHead.headF z B N

theorem shifted_head_at (r z B m N : PTm n) : Γ ⊢[PRAAx]
    inst2 shiftedHeadBody r (shiftedData z B m N) ≐ run (shiftedNumerator z B m r) (B*m) N := by
  let X := shiftedData z B m N
  have p := snd_pair (Γ := Γ) N (pairT m (pairT z B))
  have v := p.sndE
  have e := Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
    (run (shiftedNumerator (var 0) (var 1) (var 2) (var 3)) (var 1*var 2) (var 4) : PTm 5)
    (σ := ![fstT (sndT (sndT X)),sndT (sndT (sndT X)),fstT (sndT X),r,fstT X])
    (σ' := ![z,B,m,r,N]) (fun i => by
      fin_cases i
      · exact v.fstE
      · exact v.sndE
      · exact p.fstE
      · exact .eqRefl _
      · exact fst_pair _ _)
  simpa [shiftedHeadBody,shiftedNumerator,inst2,X] using e

theorem grouped_normalization (z B m N : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] grouped z B m (succ N) ≐ qmul (power (naturalPoint (fact N)) m) (shiftedHeads z B m N) := by
  have same : Γ ⊢[PRAAx] termsEqual shiftedBody (scaledBody shiftedHeadBody) m
      (shiftedData z B m (succ N)) (pairT (naturalPoint (fact N)) (shiftedData z B m N)) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
    let a := Syn.shift z
    let b := Syn.shift B
    let M := Syn.shift m
    let L := Syn.shift N
    let w := shiftedNumerator a b M (var 0)
    have hb : Δ ⊢[PRAAx] le one b := by simpa [Δ,b,Fm.shift,Syn.shift,one] using hB.shift.wk
    have hM : Δ ⊢[PRAAx] le one M := by simpa [Δ,M,Fm.shift,Syn.shift,one] using hm.shift.wk
    have e := (shifted_at (Γ := Δ) (var 0) a b M (succ L)).eqTrans
      (denominator_normalization w (b*M) L (positive_product _ _ hb hM))
    have f := (scaled_at (Γ := Δ) shiftedHeadBody (var 0) (naturalPoint (fact L)) (shiftedData a b M L)).eqTrans
      (qmul_congr (.eqRefl _) ((shifted_head_at _ _ _ _ _).eqTrans (program_at _ _ _)))
    simpa [termsEqual,Syn.shift,Δ,a,b,M,L,fact] using e.eqTrans f.eqSymm
  exact (product_congr_bounded _ _ _ _ _ same).eqTrans (scaled_product _ _ _ _)

theorem grouped_euler_heads (z B m N : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] qmul (naturalPoint (fact (cutoff m N))) (run (scale m z) B (cutoff m N)) ≐
      qmul (qmul (power (naturalPoint m) (m*succ N)) (power (naturalPoint (fact N)) m)) (shiftedHeads z B m N) := by
  let L := cutoff m N
  let a := scale m z
  have norm := (denominator_normalization a B L hB).eqTrans (qmul_congr (.eqRefl _) (program_at a B L).eqSymm)
  exact norm.eqSymm.eqTrans ((product_index_congr linearBody (cutoff_count m N hm).eqSymm (.eqRefl _)).eqTrans
    ((denominator_grouping z B m (succ N) hB hm).eqTrans
      ((qmul_congr (.eqRefl _) (grouped_normalization z B m N hB hm)).eqTrans
        (GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm)))

theorem original_Gauss_grouped_Euler_heads_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ le one (var 2) ⟶
      qmul (naturalPoint (fact (cutoff (var 2) (var 3)))) (run (scale (var 2) (var 0)) (var 1) (cutoff (var 2) (var 3))) ≐
        qmul (qmul (power (naturalPoint (var 2)) (var 2*succ (var 3))) (power (naturalPoint (fact (var 3))) (var 2)))
          (shiftedHeads (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (grouped_euler_heads _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaGaussEulerHeads
