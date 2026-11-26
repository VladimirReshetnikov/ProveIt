import IPRADerivations.Analysis.Euler.ExponentialSubstitution.GaussianEulerExponentialLogGrid
import IPRADerivations.Analysis.Logarithm.PositiveAxis.GaussianPositiveRationalLogarithmSign
import IPRADerivations.Analysis.Series.GaussianRationalParameterTelescope

/-!
# Order, mesh size, and total width of the logarithmic partition

At a common query the original denominator logarithm cancels exactly.
The remaining original harmonic interval is nonnegative and satisfies
the upper rectangle bound. Thus even the finite sampled widths are
ordered and the largest width is at most C/N. The same actual widths
telescope to the difference of the actual logarithmic endpoint queries.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerExponentialLogPartition

open_ipra
open GaussianPositiveRationalLogarithm (sample)
open GaussianPositiveRationalLogarithmIncrement (increment)
open RationalHarmonicInterval (interval horizon numerator common_value)
open RationalGaussianEmbedding (embed native)
open GaussianGammaFiniteApproximantName (log_sample_at)
open GammaEulerConstantName (mesh mesh_positive)
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (S_mono)
open Products (fact)
open GaussianRationalHorner (qadd qadd_canonical)
open GaussianRationalMetric (qsub qsub_canonical bounded)
open GaussianRationalSyntheticDivision (qsub_congr qadd_congr qadd_sub_cancel)
open GaussianRationalSumAlgebra (qadd_associative)
open GaussianRationalLinearProduct (qadd_commutative add_sub_right)
open RationalArgmin (rationalLE rationalLE_congr)
open GaussianRationalSyntheticBounds (natCode)
open ComplexLogarithmRemainder (normSq)
open GaussianCompactRiemannName (sampleData field0 field1 field2 field3 field4)
open GaussianRationalParameterTelescope (forward forward_at forward_sum)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def harmonicMesh (p : PTm n) : PTm n := mesh (GaussianFastValueCut.exponent two p)

theorem original_same_clock_width (p a b c : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] increment p p a b c ≐ embed (interval (a+c) a (harmonicMesh p)) := by
  let k := GaussianFastValueCut.exponent two p
  let X := ap2 GaussianPositiveRationalLogarithm.baseF k (a+c)
  let Y := ap2 GaussianPositiveRationalLogarithm.baseF k a
  let Z := ap2 GaussianPositiveRationalLogarithm.negativeF k (GaussianGammaEulerShift.negativeLogData b)
  have xEq : Γ ⊢[PRAAx] X ≐ embed (GammaMeshRobinLogBridge.harmonicLog (a+c) (mesh k)) := log_sample_at k (a+c)
  have canX := GaussianRationalHorner.canonical_congr xEq (RationalGaussianEmbedding.embed_canonical _)
  have readA : Γ ⊢[PRAAx] sample p (a+c) b ≐ qadd X Z :=
    (GaussianPositiveRationalLogarithm.sample_at p (a+c) b).eqTrans
      (GaussianExponentialReference.recode_fixed _ (qadd_canonical _ _))
  have readB : Γ ⊢[PRAAx] sample p a b ≐ qadd Y Z :=
    (GaussianPositiveRationalLogarithm.sample_at p a b).eqTrans
      (GaussianExponentialReference.recode_fixed _ (qadd_canonical _ _))
  have addBack : Γ ⊢[PRAAx] qadd (qadd Y Z) (qsub X Y) ≐ qadd X Z :=
    (qadd_congr (qadd_commutative Y Z) (.eqRefl _)).eqTrans
      ((qadd_associative Z Y (qsub X Y)).eqTrans
        ((qadd_congr (.eqRefl _) (add_sub_right Y X canX)).eqTrans (qadd_commutative Z X)))
  exact (qsub_congr readA readB).eqTrans
    ((qsub_congr addBack.eqSymm (.eqRefl _)).eqTrans
      ((qadd_sub_cancel _ _ (qsub_canonical _ _)).eqTrans
        ((qsub_congr xEq (log_sample_at k a)).eqTrans
          (GaussianPositiveRationalLogarithmProperness.original_finite_difference (a+c) a (mesh k)
            (le_trans ha (le_add_right _ _)) ha))))

theorem original_width_nonnegative (p a b c : PTm n) (ha : Γ ⊢[PRAAx] le one a) : Γ ⊢[PRAAx]
    rationalLE (natCode zero) (fstT (increment p p a b c)) :=
  rationalLE_congr (.eqRefl _) (congrFst (original_same_clock_width p a b c ha)).eqSymm
    (GaussianPositiveRationalLogarithmSign.embedded_interval_nonnegative (a+c) a (harmonicMesh p) (le_add_right _ _))

theorem original_width_bound (p a b c N : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hN : Γ ⊢[PRAAx] le one N) (hn : Γ ⊢[PRAAx] le N a) : Γ ⊢[PRAAx] bounded (increment p p a b c) c N := by
  let Q := harmonicMesh p
  let L := horizon (a+c) a Q
  let F := fact L
  let U := S (Q*(a+c)) F
  let V := S (Q*a) F
  let w := monus U V
  let g := native (numerator (a+c) a Q L)
  have hF := GammaEulerMesh.factorial_positive (Γ := Γ) L
  have mono := S_mono F (le_congr (by ipra_ring : Γ ⊢[PRAAx] a*Q ≐ Q*a)
    (by ipra_ring : Γ ⊢[PRAAx] (a+c)*Q ≐ Q*(a+c)) (mul_le_mul_right Q (le_add_right a c)))
  have wEq : Γ ⊢[PRAAx] U ≐ V+w := eq_add_of_le mono
  have rectangle := (GaussianHarmonicIntervalLinearRemainder.rectangles a c Q L ha (mesh_positive _)
    (RationalHarmonicInterval.left_horizon (a+c) a Q)).andE₂
  have upper : Γ ⊢[PRAAx] le (a*w) (c*F) := by
    have e := natEq wEq
    ipra_le sl rectangle using
      dsimp only [U,V,F] at e ⊢
      try ipra_simps
      linear_combination (𝔞 a)*e
  have short := le_trans (mul_le_mul_right w hn) upper
  have norm : Γ ⊢[PRAAx] normSq g ≐ w*w := by
    have e := natEq wEq
    apply deriveNat
    rw [ComplexLogarithmRemainder.normSq_eval]
    simp only [g,native,ComplexLogarithmRemainder.eval_re_code,ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat]
    simp only [numerator,ZT.toZ]
    dsimp only [U,V] at e
    ipra_simps
    rw [e]
    ring
  have rep := RationalGaussianEmbedding.embed_from_representation (Γ := Γ) (interval (a+c) a Q)
    (numerator (a+c) a Q L) F (common_value (a+c) a Q L)
  have cleared : Γ ⊢[PRAAx] le ((N*N)*normSq g) ((c*c)*(F*F)) :=
    le_congr ((by ipra_ring : Γ ⊢[PRAAx] (N*w)*(N*w) ≐ (N*N)*(w*w)).eqTrans
        (congrMul (.eqRefl _) norm.eqSymm)) (by ipra_ring)
      (LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono short short)
  exact GaussianRationalReciprocal.bound_congr (original_same_clock_width p a b c ha).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ hF hN rep cleared)

def chartData (p N a C E : PTm n) : PTm n := sampleData p N a C E zero
def node (i y : PTm n) : PTm n :=
  sample (field0 y) (field2 y*field1 y+field3 y*i) (field4 y*field1 y)
def nodeBody : PTm 2 := node (var 0) (var 1)
def widthSum (p N a C E : PTm n) : PTm n := GaussianRationalFiniteSum.sum (forward nodeBody) N (chartData p N a C E)

ipra_subst node

private theorem sample_congr (p p' a a' b b' : PTm n) (hp : Γ ⊢[PRAAx] p ≐ p') (ha : Γ ⊢[PRAAx] a ≐ a')
    (hb : Γ ⊢[PRAAx] b ≐ b') : Γ ⊢[PRAAx] sample p a b ≐ sample p' a' b' := by
  let f : PTm 3 := sample (var 0) (var 1) (var 2)
  have read (s x y : PTm n) : Syn.subst (![s,x,y] : Fin 3 → PTm n) f = sample s x y := by
    simp only [f,GaussianPositiveRationalLogarithm.subst_sample,Syn.subst_var]
    rfl
  simpa only [read] using Prf.eqCongr f
      (σ := ![p,a,b]) (σ' := ![p',a',b']) (fun i => by fin_cases i; exact hp; exact ha; exact hb)

theorem node_at (i p N a C E : PTm n) : Γ ⊢[PRAAx]
    inst2 nodeBody i (chartData p N a C E) ≐ sample p (a*N+C*i) (E*N) := by
  have atNode : inst2 nodeBody i (chartData p N a C E) = node i (chartData p N a C E) := by
    simp only [nodeBody,inst2,subst_node,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [atNode]
  exact sample_congr _ _ _ _ _ _ (GaussianCompactRiemannName.field0_at _ _ _ _ _ _)
    (congrAdd (congrMul (GaussianCompactRiemannName.field2_at _ _ _ _ _ _) (GaussianCompactRiemannName.field1_at _ _ _ _ _ _))
      (congrMul (GaussianCompactRiemannName.field3_at _ _ _ _ _ _) (.eqRefl _)))
    (congrMul (GaussianCompactRiemannName.field4_at _ _ _ _ _ _) (GaussianCompactRiemannName.field1_at _ _ _ _ _ _))

theorem width_at (i p N a C E : PTm n) : Γ ⊢[PRAAx]
    inst2 (forward nodeBody) i (chartData p N a C E) ≐ increment p p (a*N+C*i) (E*N) C := by
  rw [forward_at]
  exact qsub_congr ((node_at (succ i) p N a C E).eqTrans
    (sample_congr _ _ _ _ _ _ (.eqRefl _) (by ipra_ring) (.eqRefl _))) (node_at i p N a C E)

theorem original_total_width (p N a C E : PTm n) : Γ ⊢[PRAAx]
    widthSum p N a C E ≐ qsub (sample p ((a+C)*N) (E*N)) (sample p (a*N) (E*N)) :=
  (forward_sum nodeBody N (chartData p N a C E)).eqTrans
    (qsub_congr ((node_at N p N a C E).eqTrans (sample_congr _ _ _ _ _ _ (.eqRefl _) (by ipra_ring) (.eqRefl _)))
      ((node_at zero p N a C E).eqTrans (sample_congr _ _ _ _ _ _ (.eqRefl _) (by ipra_ring) (.eqRefl _))))

theorem original_grid_width_bound (i p N a C E : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    bounded (increment p p (a*N+C*i) (E*N) C) C N := by
  have hn : Γ ⊢[PRAAx] le N (a*N+C*i) := le_trans
    (le_congr (one_mul N) (.eqRefl _) (mul_le_mul_right N ha)) (le_add_right _ _)
  exact original_width_bound p (a*N+C*i) (E*N) C N (le_trans hN hn) hN hn

theorem actual_log_grid_width_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((le one (var 3) ⋏ le one (var 2)) ⟶
      bounded (increment (var 1) (var 1) (var 3*var 2+var 4*var 0) (var 5*var 2) (var 4)) (var 4) (var 2)) :=
  closeUniv 6 (.impI (original_grid_width_bound _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_log_grid_width_telescope_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (widthSum (var 0) (var 1) (var 2) (var 3) (var 4) ≐
      qsub (sample (var 0) ((var 2+var 3)*var 1) (var 4*var 1)) (sample (var 0) (var 2*var 1) (var 4*var 1))) :=
  closeUniv 5 (original_total_width _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianEulerExponentialLogPartition
