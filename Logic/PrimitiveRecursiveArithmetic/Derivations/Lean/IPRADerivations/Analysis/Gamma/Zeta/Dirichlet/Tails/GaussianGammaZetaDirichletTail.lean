import IPRADerivations.Analysis.Gamma.Zeta.Dirichlet.Tails.GaussianGammaZetaDirichletBlock
import IPRADerivations.Probability.FiniteLaws

/-!
# A quantitative tail on arbitrary finite Dirichlet prefixes

Clipping each dyadic boundary at M retains exactly the original first
M terms, including the last partial block. The geometric majorants
telescope in a quantifier-free induction on the number of blocks.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaDirichletTail

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEulerPositiveScalingConstant (inverseF)
open GaussianGammaEulerHeadShift (shifted)
open GaussianGammaZetaDirichletRowDecay (block block_positive subst_block)
open GaussianGammaZetaDirichletBlock (value block_succ block_error)
open GaussianGammaZetaMellinDampedImproper (dirichletBody parameters)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "S" => GaussianEulerIntegralGammaIdentification.source
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def clip (M J : PTm n) : PTm n := monus M (monus M J)

ipra_subst clip

theorem clip_eq_left (M J : PTm n) (h : Γ ⊢[PRAAx] le M J) : Γ ⊢[PRAAx] clip M J ≐ M :=
  (congrMonus (.eqRefl _) h).eqTrans (monus_zero _)

theorem clip_eq_right (M J : PTm n) (h : Γ ⊢[PRAAx] le J M) : Γ ⊢[PRAAx] clip M J ≐ J :=
  (congrMonus (eq_add_of_le h) (.eqRefl _)).eqTrans (add_monus _ _)

theorem prefix_index_congr (p L M z R B A : PTm n) (h : Γ ⊢[PRAAx] L ≐ M) :
    Γ ⊢[PRAAx] value p L z R B A ≐ value p M z R B A :=
  GaussianRationalFiniteSum.sum_index_congr (GaussianNamedFiniteSumFamily.body inverseF dirichletBody) h (.eqRefl _)

private theorem block_monotone (A h j : PTm n) (leq : Γ ⊢[PRAAx] le h j) :
    Γ ⊢[PRAAx] le (block A h) (block A j) :=
  pw_le_pw A (GaussianExponentialReference.unit_monotone leq)

private theorem clipped_step (p M z R B A h : PTm n) (hz : Γ ⊢[PRAAx] S z R B A) :
    Γ ⊢[PRAAx] distanceBounded
      (value p (clip M (block A (succ h))) z R B A) (value p (clip M (block A h)) z R B A)
      (unit A*unit p+num 3*M*unit h) (unit h*unit p) := by
  let J := block A h
  let K := block A (succ h)
  let H := unit h
  let P := unit p
  let C := unit A
  have hd := positive_product H P (unit_positive (Γ := Γ) h) (unit_positive p)
  have up := block_monotone (Γ := Γ) A h (succ h) (le_succ_self h)
  refine .orE (le_total M J) ?_ ?_
  · let Δ := le M J::Γ
    have h1 := clip_eq_left (Γ := Δ) M J Prf.hyp0
    have h2 := clip_eq_left (Γ := Δ) M K (le_trans Prf.hyp0 up.wk)
    exact distance_radius_mono _ _ _ _ _ _ hd.wk hd.wk
      (le_congr (zero_mul _).eqSymm (.eqRefl _) (zero_le _))
      (distance_congr (prefix_index_congr p _ _ z R B A h2).eqSymm
        (prefix_index_congr p _ _ z R B A h1).eqSymm (.eqRefl _) (.eqRefl _)
        (GaussianRationalPowerDifference.distance_refl_zero (value p M z R B A) _ hd.wk))
  · let Δ := le J M::Γ
    let N := clip M K
    let r := monus N J
    have h1 : Δ ⊢[PRAAx] clip M J ≐ J := clip_eq_right M J Prf.hyp0
    have hN : Δ ⊢[PRAAx] le J N := by
      refine .orE (le_total M K) ?_ ?_
      · exact le_congr (.eqRefl _) (clip_eq_left M K Prf.hyp0).eqSymm Prf.hyp1
      · exact le_congr (.eqRefl _) (clip_eq_right M K Prf.hyp0).eqSymm up.wk.wk
    have sum : Δ ⊢[PRAAx] J+r ≐ N := (eq_add_of_le hN).eqSymm
    have hrK : Δ ⊢[PRAAx] le r K :=
      le_trans (le_congr (.eqRefl _) sum (le_add_left r J)) (Probability.FiniteLaws.min_le_right M K)
    have hrM : Δ ⊢[PRAAx] le r M :=
      le_trans (le_congr (.eqRefl _) sum (le_add_left r J)) (Probability.FiniteLaws.min_le_left M K)
    have hr : Δ ⊢[PRAAx] le r (J*C) :=
      le_congr (.eqRefl _) (block_succ A h) hrK
    have e := block_error p J r z R B A h hz.wk (le_refl J) hr
    have near := distance_congr (prefix_index_congr p _ _ z R B A sum)
      (prefix_index_congr p _ _ z R B A h1.eqSymm) (.eqRefl _) (.eqRefl _) e
    exact distance_radius_mono _ _ _ _ _ _ hd.wk hd.wk (by
      change Δ ⊢[PRAAx] le ((C*P+num 3*r*H)*(H*P)) ((C*P+num 3*M*H)*(H*P))
      ipra_le (Groth.ι (IPRA.Q.mk Δ (num 3*H*H*P)))*sl hrM) near

def cost (p M A h j : PTm n) : PTm n :=
  two*unit A*pred (unit j)*unit p+num 3*M*j*(unit h*unit j)
def denominator (p h j : PTm n) : PTm n := unit h*unit j*unit p

ipra_subst cost [two]
ipra_subst denominator

def inductionBound (p M z R B A h j : PTm n) : Fm PTm n :=
  distanceBounded (value p (clip M (block A (h+j))) z R B A) (value p (clip M (block A h)) z R B A)
    (cost p M A h j) (denominator p h j)

ipra_subst inductionBound

private theorem denominator_positive (p h j : PTm n) : Γ ⊢[PRAAx] le one (denominator p h j) :=
  positive_product _ _ (positive_product _ _ (unit_positive h) (unit_positive j)) (unit_positive p)

private theorem induction_base (p M z R B A h : PTm n) : Γ ⊢[PRAAx] inductionBound p M z R B A h zero := by
  let L := clip M (block A h)
  let d := denominator p h zero
  have hd := denominator_positive (Γ := Γ) p h zero
  have e : Γ ⊢[PRAAx] clip M (block A (h+zero)) ≐ L := by
    simpa only [subst_clip,subst_block,PTm.subst_add,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      using Prf.eqCongr1 (clip (Syn.shift M) (block (Syn.shift A) (var 0))) (add_zero (Γ := Γ) h)
  exact distance_radius_mono _ _ _ _ _ _ hd hd
    (le_congr (zero_mul _).eqSymm (.eqRefl _) (zero_le _))
    (distance_congr (prefix_index_congr p _ _ z R B A e).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (GaussianRationalPowerDifference.distance_refl_zero (value p L z R B A) d hd))

private theorem pred_unit (j : PTm n) : Γ ⊢[PRAAx] unit j ≐ pred (unit j)+one :=
  (pos_of_eq_succ ((eq_add_of_le (unit_positive (Γ := Γ) j)).eqTrans
    ((add_comm _ _).eqTrans (succ_eq_add_one _).eqSymm))).eqTrans (succ_eq_add_one _)

private theorem induction_step (p M z R B A h j : PTm n) (hz : Γ ⊢[PRAAx] S z R B A)
    (ih : Γ ⊢[PRAAx] inductionBound p M z R B A h j) :
    Γ ⊢[PRAAx] inductionBound p M z R B A h (succ j) := by
  let P := unit p
  let C := unit A
  let H := unit h
  let U := unit j
  let V := unit (succ j)
  let d := denominator p h j
  let r := cost p M A h j
  let e := C*P+num 3*M*(H*U)
  have hd := denominator_positive (Γ := Γ) p h j
  have un : Γ ⊢[PRAAx] unit (h+j) ≐ H*U := pw_add two h j
  have next : Γ ⊢[PRAAx] clip M (block A (succ (h+j))) ≐ clip M (block A (h+succ j)) := by
    simpa only [subst_clip,subst_block,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      using Prf.eqCongr1 (clip (Syn.shift M) (block (Syn.shift A) (var 0))) (add_succ (Γ := Γ) h j).eqSymm
  have localBound := distance_congr (prefix_index_congr p _ _ z R B A next) (.eqRefl _)
    (congrAdd (.eqRefl (C*P)) (congrMul (.eqRefl (num 3*M)) un))
    (congrMul un (.eqRefl P)) (clipped_step p M z R B A (h+j) hz)
  have combined := distance_triangle_same _ _ _ e r d hd localBound ih
  apply distance_radius_mono _ _ _ _ _ _ hd (denominator_positive p h (succ j)) _ combined
  have v : Γ ⊢[PRAAx] V ≐ two*U := GaussianRationalHalfAngleRecovery.unit_succ j
  have pv : Γ ⊢[PRAAx] pred V ≐ two*pred U+one := by
    have h : Γ ⊢[PRAAx] pred V+one ≐ two*U := (pred_unit (Γ := Γ) (succ j)).eqSymm.eqTrans v
    have hu : Γ ⊢[PRAAx] U ≐ pred U+one := pred_unit (Γ := Γ) j
    exact add_right_cancel (c := one) (by
      apply deriveNat
      have hh := natEq h
      have uu := natEq hu
      ipra_simps
      linear_combination hh+2*uu)
  change Γ ⊢[PRAAx] le ((e+r)*(H*V*P)) ((two*C*pred V*P+num 3*M*succ j*(H*V))*d)
  apply le_of_eq_add (d := zero)
  apply deriveNat
  have v' := natEq v
  have p' := natEq pv
  simp only [e,r,cost,d,denominator]
  change Groth.ι (IPRA.Q.mk Γ ((two*C*pred V*P+num 3*M*succ j*(H*V))*(H*U*P))) =
    Groth.ι (IPRA.Q.mk Γ ((C*P+num 3*M*(H*U)+
      (two*C*pred U*P+num 3*M*j*(H*U)))*(H*V*P)+zero))
  ipra_simps
  rw [v',p']
  ring

private theorem accumulated (p M z R B A h j : PTm n) (hz : Γ ⊢[PRAAx] S z R B A) :
    Γ ⊢[PRAAx] inductionBound p M z R B A h j := by
  let sh (v : PTm n) := Syn.shift v
  have hs : Γ.map Fm.shift ⊢[PRAAx] S (sh z) (sh R) (sh B) (sh A) :=
    by simpa [Fm.shift,sh,Syn.shift] using hz.shift
  have all : Γ ⊢[PRAAx] .all (inductionBound (sh p) (sh M) (sh z) (sh R) (sh B) (sh A) (sh h) (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simpa only [subst_inductionBound,sh,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
        using induction_base (Γ := Γ) p M z R B A h
    · simpa only [subst_inductionBound,sh,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        induction_step (sh p) (sh M) (sh z) (sh R) (sh B) (sh A) (sh h) (var 0) hs.wk Prf.hyp0
  simpa only [subst_inductionBound,sh,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j

private theorem block_dominates (A h M : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] le M (block A (h+M)) := by
  let V := unit (h+M)
  have hx : Γ ⊢[PRAAx] le M (unit M) := le_trans (le_succ_self M) (RationalClosure.succ_le_two_pow M)
  have hV := unit_positive (Γ := Γ) (h+M)
  have keep : Γ ⊢[PRAAx] le V (block A (h+M)) := by
    have e : Γ ⊢[PRAAx] block A (h+M) ≐ V*pw V (monus A one) :=
      (congrAp2 powF (eq_add_of_le hA) (.eqRefl V)).eqTrans
        ((pw_add V one (monus A one)).eqTrans (congrMul (pw_one V) (.eqRefl _)))
    exact le_congr (one_mul V) ((mul_comm _ _).eqTrans e.eqSymm)
      (mul_le_mul_right V (GaussianPolynomialPerturbation.power_positive V (monus A one) hV))
  exact le_trans hx (le_trans (GaussianExponentialReference.unit_monotone (le_add_left M h)) keep)

theorem tail_error (p M z R B A h : PTm n) (hz : Γ ⊢[PRAAx] S z R B A)
    (hM : Γ ⊢[PRAAx] le (block A h) M) :
    Γ ⊢[PRAAx] distanceBounded (value p M z R B A) (value p (block A h) z R B A)
      (two*unit A*unit p+num 3*M*M*unit h) (unit h*unit p) := by
  let C := unit A
  let H := unit h
  let P := unit p
  let U := unit M
  let L := block A h
  have a := accumulated p M z R B A h M hz
  have left := prefix_index_congr p _ _ z R B A (clip_eq_left M (block A (h+M)) (block_dominates A h M hz.andE₁.andE₁))
  have right := prefix_index_congr p _ _ z R B A (clip_eq_right M L hM)
  have near := distance_congr left right (.eqRefl _) (.eqRefl _) a
  apply distance_radius_mono _ _ _ _ _ _ (denominator_positive p h M)
    (positive_product _ _ (unit_positive h) (unit_positive p)) _ near
  have pred_le : Γ ⊢[PRAAx] le (pred U) U := le_of_eq_add (d := one) (pred_unit M)
  change Γ ⊢[PRAAx] le ((two*C*pred U*P+num 3*M*M*(H*U))*(H*P))
    ((two*C*P+num 3*M*M*H)*(H*U*P))
  ipra_le 𝔞(two*C*H*P*P)*sl pred_le

end LeanProofs.IPRA.Analysis.GaussianGammaZetaDirichletTail
