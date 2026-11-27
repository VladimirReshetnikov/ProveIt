import IPRADerivations.Analysis.Trigonometry.Hyperbolic.ProductEstimates.GaussianSineProductImaginaryLogDerivative
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.GaussianRationalSumAlgebra

/-!
# Exact first-order increment of an imaginary-axis sine product

For x=A/B and h=C/B the original finite Euler product at i(x+h)
equals the product at ix, plus h times its derivative recurrence, plus
h² times a primitive-recursive remainder. The remainder keeps the
inverse-square coefficients visible for subsequent uniform bounds.
-/

set_option autoImplicit false
set_option maxHeartbeats 550000

namespace LeanProofs.IPRA.Analysis.GaussianSineProductImaginaryFirstOrder

open_ipra
open ComplexLogarithmRemainder (eval_im_code eval_re_code)
open GaussianGammaEulerReflectionHead (body)
open GaussianRationalCoefficientScaling (qmul_add)
open GaussianRationalFiniteProduct (product_zero)
open GaussianRationalHorner
  (canonical_unique ofGaussian_canonical ofGaussian_represents positive_product
    qadd qadd_canonical qadd_represents qmul qmul_canonical qmul_represents qzero represents_congr)
open GaussianRationalPowerAlgebra (qmul_commutative qmul_shuffle)
open GaussianRationalSumAlgebra (qadd_associative)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qmul_zero_right qone qone_canonical rescale_to)
open GaussianReciprocalHorner (qadd_zero_right qmul_associative)
open GaussianRootAlgebra (equal_of_values im_add im_mul im_scale re_add re_mul re_scale)
open GaussianSineProductImaginaryLogDerivative
  (axisNumerator derivative derivative_succ derivative_zero factor factorDerivative factor_value product
    rationalReal realNumerator squareDenominator)
open GaussianSineProductName (sine_product_succ)
open GaussianRationalPolynomialBuffers renaming distribute_right → mul_add_right
open GaussianRationalPowerAlgebra renaming commute_nested → mul_swap_middle

variable {n : ℕ} {Γ : List (Fm PTm n)}

def step (B C : PTm n) : PTm n := rationalReal C B

def quadraticRow (i B : PTm n) : PTm n := rationalReal (B*B) (squareDenominator i B)

def linearRow (i A B C : PTm n) : PTm n :=
  qadd (factorDerivative i A B) (qmul (step B C) (quadraticRow i B))

def remainderStep (i V A B C : PTm n) : PTm n :=
  qadd (qadd (qmul (product A B i) (quadraticRow i B)) (qmul (derivative A B i) (linearRow i A B C)))
    (qmul V (factor i (A+C) B))

private def remainderBody : PTm 3 :=
  remainderStep (var 0) (var 1) (fstT (var 2)) (fstT (sndT (var 2))) (sndT (sndT (var 2)))

def remainderF : PR 2 := rec2 (qzero : PTm 1) remainderBody
def remainder (A B C N : PTm n) : PTm n := ap2 remainderF N (pairT A (pairT B C))

ipra_subst step

ipra_subst quadraticRow

ipra_subst linearRow

ipra_subst remainderStep

ipra_subst remainder

private theorem real_congr {a a' d : PTm n} (e : Γ ⊢[PRAAx] a ≐ a') :
    Γ ⊢[PRAAx] rationalReal a d ≐ rationalReal a' d := by
  simpa only [GaussianSineProductImaginaryLogDerivative.subst_rationalReal, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one] using
      Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (rationalReal (var 0) (var 1) : PTm 2)
        (σ := ![a,d]) (σ' := ![a',d]) (fun i => by fin_cases i; exact e; exact .eqRefl d)

private theorem real_add_same (a b d : PTm n) (hd : Γ ⊢[PRAAx] le one d) :
    Γ ⊢[PRAAx] qadd (rationalReal a d) (rationalReal b d) ≐ rationalReal (a+b) d := by
  have aRep := ofGaussian_represents (Γ := Γ) (realNumerator a) d hd
  have bRep := ofGaussian_represents (Γ := Γ) (realNumerator b) d hd
  have left := qadd_represents _ _ _ _ _ hd aRep bRep
  have right := ofGaussian_represents (Γ := Γ) (realNumerator (a+b)) d hd
  apply canonical_unique _ _ _ d (qadd_canonical _ _) (ofGaussian_canonical _ _ hd) hd (hrv := right)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := left)
  apply equal_of_values
  · simp only [re_add, realNumerator, eval_re_code, ZT.toZ_ofNat]
    ipra_simps
  · simp [im_add, realNumerator, eval_im_code, ZT.toZ_ofNat]

private theorem real_mul_scaled (a b d e : PTm n) (hd : Γ ⊢[PRAAx] le one d) (he : Γ ⊢[PRAAx] le one e) :
    Γ ⊢[PRAAx] qmul (rationalReal a d) (rationalReal (d*b) e) ≐ rationalReal (a*b) e := by
  have ra := ofGaussian_represents (Γ := Γ) (realNumerator a) d hd
  have rb := ofGaussian_represents (Γ := Γ) (realNumerator (d*b)) e he
  have left := qmul_represents _ _ _ _ _ _ hd he ra rb
  have right := rescale_to (rationalReal (a*b) e) (realNumerator (a*b)) e d (d*e)
    (ofGaussian_represents _ _ he) (mul_comm e d)
  apply canonical_unique _ _ _ (d*e) (qmul_canonical _ _) (ofGaussian_canonical _ _ he)
    (positive_product _ _ hd he) (hrv := right)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := left)
  apply equal_of_values <;>
    simp only [re_mul, im_mul, re_scale, im_scale, realNumerator, eval_re_code, eval_im_code, ZT.toZ_ofNat] <;>
    ipra_simps <;> ring

theorem factor_increment (i A B C : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] factor i (A+C) B ≐ qadd (factor i A B) (qmul (step B C) (linearRow i A B C)) := by
  let E := squareDenominator i B
  have hJ : Γ ⊢[PRAAx] le one (B*succ i) := positive_product _ _ hB (zero_lt_succ _)
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _ hJ hJ
  have curvature : Γ ⊢[PRAAx] qmul (step B C) (quadraticRow i B) ≐ rationalReal (C*B) E :=
    real_mul_scaled C B B E hB hE
  have slope : Γ ⊢[PRAAx] linearRow i A B C ≐ rationalReal (B*(two*A+C)) E :=
    (qadd_congr (.eqRefl (factorDerivative i A B)) curvature).eqTrans
      ((real_add_same (two*A*B) (C*B) E hE).eqTrans (real_congr (by ipra_ring)))
  have delta := (qmul_congr (.eqRefl (step B C)) slope).eqTrans (real_mul_scaled C (two*A+C) B E hB hE)
  have rhs : Γ ⊢[PRAAx] qadd (factor i A B) (qmul (step B C) (linearRow i A B C)) ≐
      rationalReal (E+(A+C)*(A+C)) E :=
    (qadd_congr (factor_value i A B hB) delta).eqTrans
    ((real_add_same (E+A*A) (C*(two*A+C)) E hE).eqTrans (real_congr (by ipra_ring)))
  exact (factor_value i (A+C) B hB).eqTrans rhs.eqSymm

private theorem advance (P D V F G d e h : PTm n)
    (hG : Γ ⊢[PRAAx] G ≐ qadd F (qmul h (qadd d (qmul h e)))) : Γ ⊢[PRAAx]
    qmul (qadd (qadd P (qmul h D)) (qmul (qmul h h) V)) G ≐
      qadd (qadd (qmul P F) (qmul h (qadd (qmul D F) (qmul P d))))
        (qmul (qmul h h) (qadd (qadd (qmul P e) (qmul D (qadd d (qmul h e)))) (qmul V G))) := by
  let H := qmul h h
  let A := qadd P (qmul h D)
  let T := qadd d (qmul h e)
  let L₁ := qmul h (qmul D F)
  let L₂ := qmul h (qmul P d)
  let R₁ := qmul H (qmul P e)
  let R₂ := qmul H (qmul D T)
  let R₃ := qmul H (qmul V G)
  let F₀ := qmul P F
  have initial : Γ ⊢[PRAAx] qmul (qadd A (qmul H V)) G ≐
      qadd (qadd (qmul A F) (qmul A (qmul h T))) R₃ :=
    (mul_add_right A (qmul H V) G).eqTrans
      (qadd_congr ((qmul_congr (.eqRefl A) hG).eqTrans (qmul_add A F (qmul h T))) (qmul_associative H V G))
  have left : Γ ⊢[PRAAx] qmul A F ≐ qadd F₀ L₁ :=
    (mul_add_right P (qmul h D) F).eqTrans (qadd_congr (.eqRefl F₀) (qmul_associative h D F))
  have E : Γ ⊢[PRAAx] qmul P T ≐ qadd (qmul P d) (qmul h (qmul P e)) :=
    (qmul_add P d (qmul h e)).eqTrans (qadd_congr (.eqRefl _) (mul_swap_middle P h e))
  have M : Γ ⊢[PRAAx] qmul P (qmul h T) ≐ qadd L₂ R₁ :=
    (mul_swap_middle P h T).eqTrans ((qmul_congr (.eqRefl h) E).eqTrans
      ((qmul_add h (qmul P d) (qmul h (qmul P e))).eqTrans
        (qadd_congr (.eqRefl L₂) (qmul_associative h h (qmul P e)).eqSymm)))
  have right : Γ ⊢[PRAAx] qmul A (qmul h T) ≐ qadd (qadd L₂ R₁) R₂ :=
    (mul_add_right P (qmul h D) (qmul h T)).eqTrans (qadd_congr M (qmul_shuffle h D h T))
  have grouped : Γ ⊢[PRAAx] qadd (qadd (qadd F₀ L₁) (qadd (qadd L₂ R₁) R₂)) R₃ ≐
      qadd (qadd F₀ (qadd L₁ L₂)) (qadd (qadd R₁ R₂) R₃) := by
    have regroup := (qadd_congr (.eqRefl (qadd F₀ L₁)) (qadd_associative (Γ := Γ) L₂ R₁ R₂)).eqTrans
      ((qadd_associative (qadd F₀ L₁) L₂ (qadd R₁ R₂)).eqSymm.eqTrans
        (qadd_congr (qadd_associative F₀ L₁ L₂) (.eqRefl (qadd R₁ R₂))))
    exact (qadd_congr regroup (.eqRefl R₃)).eqTrans
      (qadd_associative (qadd F₀ (qadd L₁ L₂)) (qadd R₁ R₂) R₃)
  have a := initial.eqTrans ((qadd_congr (qadd_congr left right) (.eqRefl R₃)).eqTrans grouped)
  exact a.eqTrans
    (qadd_congr (qadd_congr (.eqRefl F₀) (qmul_add h (qmul D F) (qmul P d)).eqSymm)
      ((qadd_congr (qmul_add H (qmul P e) (qmul D T)).eqSymm (.eqRefl R₃)).eqTrans
        (qmul_add H (qadd (qmul P e) (qmul D T)) (qmul V G)).eqSymm))

theorem remainder_zero (A B C : PTm n) : Γ ⊢[PRAAx] remainder A B C zero ≐ qzero := by
  simpa [remainder, remainderF] using rec2_zero (Γ := Γ) (qzero : PTm 1) remainderBody (pairT A (pairT B C))

theorem remainder_succ (A B C N : PTm n) : Γ ⊢[PRAAx] remainder A B C (succ N) ≐
    remainderStep N (remainder A B C N) A B C := by
  let x := pairT A (pairT B C)
  let v := remainder A B C N
  have raw := rec2_succ (Γ := Γ) (qzero : PTm 1) remainderBody N x
  have atBody : Γ ⊢[PRAAx] remainder A B C (succ N) ≐
      remainderStep N v (fstT x) (fstT (sndT x)) (sndT (sndT x)) := by
    simpa only [remainder, remainderF, remainderBody, x, v, inst3, subst_remainderStep, subst_fstT, subst_sndT,
      Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      using raw
  refine atBody.eqTrans ?_
  simpa only [subst_remainderStep, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons] using
      Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (remainderStep (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
        (σ := ![N,v,fstT x,fstT (sndT x),sndT (sndT x)]) (σ' := ![N,v,A,B,C])
        (fun j => by
          fin_cases j
          · exact .eqRefl _
          · exact .eqRefl _
          · exact fst_pair _ _
          · exact (congrFst (snd_pair A (pairT B C))).eqTrans (fst_pair _ _)
          · exact (congrSnd (snd_pair A (pairT B C))).eqTrans (snd_pair _ _))

private def expansion (A B C N : PTm n) : Fm PTm n :=
  product (A+C) B N ≐ qadd (qadd (product A B N) (qmul (step B C) (derivative A B N)))
    (qmul (qmul (step B C) (step B C)) (remainder A B C N))

@[simp] private theorem subst_expansion {m : ℕ} (σ : Fin n → PTm m) (A B C N : PTm n) :
    (expansion A B C N).subst σ = expansion (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ C) (Syn.subst σ N) := by
  simp [expansion]

private theorem expansion_zero (A B C : PTm n) : Γ ⊢[PRAAx] expansion A B C zero := by
  have p : Γ ⊢[PRAAx] product A B zero ≐ qone := product_zero body (pairT (axisNumerator A) B)
  have q : Γ ⊢[PRAAx] product (A+C) B zero ≐ qone := product_zero body (pairT (axisNumerator (A+C)) B)
  have hD := (qmul_congr (.eqRefl (step B C)) (derivative_zero (Γ := Γ) A B)).eqTrans (qmul_zero_right _)
  have hV := (qmul_congr (.eqRefl (qmul (step B C) (step B C))) (remainder_zero (Γ := Γ) A B C)).eqTrans
    (qmul_zero_right _)
  exact q.eqTrans ((qadd_congr ((qadd_congr p hD).eqTrans (qadd_zero_right _ qone_canonical)) hV).eqTrans
    (qadd_zero_right _ qone_canonical)).eqSymm

private theorem expansion_succ (A B C N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (ih : Γ ⊢[PRAAx] expansion A B C N) : Γ ⊢[PRAAx] expansion A B C (succ N) := by
  have p := sine_product_succ (Γ := Γ) (axisNumerator (A+C)) B N
  have left := p.eqTrans (qmul_congr ih (.eqRefl (factor N (A+C) B)))
  have expand := advance (product A B N) (derivative A B N) (remainder A B C N)
    (factor N A B) (factor N (A+C) B) (factorDerivative N A B) (quadraticRow N B) (step B C)
    (factor_increment N A B C hB)
  exact left.eqTrans (expand.eqTrans
    (qadd_congr (qadd_congr (sine_product_succ (axisNumerator A) B N).eqSymm
      (qmul_congr (.eqRefl _) (derivative_succ A B N).eqSymm))
      (qmul_congr (.eqRefl _) (remainder_succ A B C N).eqSymm)))

theorem first_order (A B C N : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    product (A+C) B N ≐ qadd (qadd (product A B N) (qmul (step B C) (derivative A B N)))
      (qmul (qmul (step B C) (step B C)) (remainder A B C N)) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift, Syn.shift, one] using hB.shift
  have full : Γ ⊢[PRAAx] .all (expansion (Syn.shift A) (Syn.shift B) (Syn.shift C) (var 0)) := by
    refine PRA.qfInd _ (by trivial) ?_ ?_
    · simpa only [subst_expansion, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using expansion_zero A B C
    · simpa only [subst_expansion, Syn.subst_var, Syn.repl_zero, subst_repl_shift] using
        expansion_succ (Syn.shift A) (Syn.shift B) (Syn.shift C) (var 0) hs.wk Prf.hyp0
  have final : Γ ⊢[PRAAx] expansion A B C N := by
    simpa only [subst_expansion, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using full.allE N
  exact final

theorem actual_finite_imaginary_sine_product_first_order_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (let A := var 0
       let B := var 1
       let C := var 2
       let N := var 3
       le one B ⟶
       product (A+C) B N ≐ qadd (qadd (product A B N) (qmul (step B C) (derivative A B N)))
         (qmul (qmul (step B C) (step B C)) (remainder A B C N))) :=
  closeUniv 4 (.impI (first_order _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianSineProductImaginaryFirstOrder
