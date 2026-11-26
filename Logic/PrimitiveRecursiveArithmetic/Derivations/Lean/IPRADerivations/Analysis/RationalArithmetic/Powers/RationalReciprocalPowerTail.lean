import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Analysis.RationalArithmetic.PowerSums
import IPRADerivations.Analysis.Inequalities.RationalNonnegativePowers
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalSyntheticBounds

/-!
# Sharp finite reciprocal-power tails

For internal m>=2 and N>=1 the actual rational finite sum over
N+1,...,N+r satisfies the sharp integral-test bound. The stronger finite
conservation inequality retains the endpoint 1/((m-1)(N+r)^(m-1)).
The native PowerSums.lower inequality supplies the discrete antiderivative;
no infinite sum or convergence law is an input.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.RationalReciprocalPowerTail

open_ipra
open GaussianEuclideanDistanceName (fraction fraction_represents fraction_order subst_fraction)
open RationalArithmetic (add represents)
open RationalArgmin (rationalLE)
open RationalNonnegativePowers (fraction_congr)
open RationalSupMetric (numeratorOf denominatorOf)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def reciprocalPower (m k : PTm n) : PTm n := fraction one (pw k m)
def potential (m N : PTm n) : PTm n := fraction one (pred m*pw N (pred m))
def data (m N : PTm n) : PTm n := pairT m N
def body : PTm 2 := reciprocalPower (fstT (var 1)) (succ (sndT (var 1)+var 0))
def tail (m N r : PTm n) : PTm n := RationalFiniteSum.sum body r (data m N)

ipra_subst reciprocalPower
ipra_subst potential
ipra_subst data
ipra_subst tail

theorem reciprocal_congr {m k a b : PTm n} (hm : Γ ⊢[PRAAx] m ≐ a) (hk : Γ ⊢[PRAAx] k ≐ b) :
    Γ ⊢[PRAAx] reciprocalPower m k ≐ reciprocalPower a b :=
  fraction_congr (.eqRefl _) (congrAp2 powF hm hk)
theorem potential_congr {m N a b : PTm n} (hm : Γ ⊢[PRAAx] m ≐ a) (hN : Γ ⊢[PRAAx] N ≐ b) :
    Γ ⊢[PRAAx] potential m N ≐ potential a b :=
  fraction_congr (.eqRefl _) (congrMul (congrPred hm) (congrAp2 powF (congrPred hm) hN))

theorem exponent_form (m : PTm n) (hm : Γ ⊢[PRAAx] le two m) :
    Γ ⊢[PRAAx] m ≐ succ (succ (monus m two)) :=
  (eq_add_of_le hm).eqTrans (by ipra_ring)
theorem predecessor_form (m : PTm n) (hm : Γ ⊢[PRAAx] le two m) :
    Γ ⊢[PRAAx] pred m ≐ succ (monus m two) :=
  (congrPred (exponent_form m hm)).eqTrans (pred_succ _)
theorem predecessor_positive (m : PTm n) (hm : Γ ⊢[PRAAx] le two m) :
    Γ ⊢[PRAAx] le one (pred m) :=
  le_congr (.eqRefl _) (predecessor_form m hm).eqSymm (zero_lt_succ _)
theorem potential_denominator_positive (m N : PTm n) (hm : Γ ⊢[PRAAx] le two m)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] le one (pred m*pw N (pred m)) :=
  RationalAlgebra.positive_product (predecessor_positive m hm) (GaussianFactorBudget.power_positive _ _ hN)

/-- The actual native power inequality gives the exact discrete
antiderivative inequality, with no division and no positive k premise. -/
theorem native_antiderivative (k q : PTm n) : Γ ⊢[PRAAx]
    le ((succ q+succ k)*pw k (succ q)) (succ k*pw (succ k) (succ q)) := by
  have h := PowerSums.lower (Γ := Γ) k q
  have e := natEq (pw_succ (Γ := Γ) k q)
  ipra_le 𝔞(succ k)*sl h+𝔞(succ q)*𝔞(pw k q) using
    rw [e]
    ring

theorem one_step_successors (q k : PTm n) (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx]
    rationalLE (add (reciprocalPower (succ (succ q)) (succ k))
      (potential (succ (succ q)) (succ k))) (potential (succ (succ q)) k) := by
  let p := succ q
  let W := succ k
  have hp : Γ ⊢[PRAAx] le one p := zero_lt_succ q
  have hW : Γ ⊢[PRAAx] le one W := zero_lt_succ k
  have hP := GaussianFactorBudget.power_positive (Γ := Γ) W p hW
  have hQ := GaussianFactorBudget.power_positive (Γ := Γ) W (succ p) hW
  have hD := RationalAlgebra.positive_product hp hP
  have hE := RationalAlgebra.positive_product hp (GaussianFactorBudget.power_positive k p hk)
  have sumrep := RationalRepresentations.represents_add (Γ := Γ)
    (fraction one (pw W (succ p))) (fraction one (p*pw W p)) _ _ _ _
    (fraction_represents _ _ hQ) (fraction_represents _ _ hD)
  have rep : Γ ⊢[PRAAx] represents
      (add (fraction one (pw W (succ p))) (fraction one (p*pw W p)))
      (ZT.ofNat (p*pw W p+pw W (succ p))) (pw W (succ p)*(p*pw W p)) := by
    apply GaussianRationalHorner.scalar_congr (.eqRefl _) (hAB := .eqRefl _) (h := sumrep)
    ipra_lc
  have native := native_antiderivative (Γ := Γ) k q
  have step := natEq (pw_succ (Γ := Γ) W p)
  have cmp : Γ ⊢[PRAAx]
      le ((p*pw k p)*(p*pw W p+pw W (succ p))) (one*(pw W (succ p)*(p*pw W p))) := by
    ipra_le 𝔞(p)*𝔞(pw W p)*sl native using
      dsimp [p,W] at *
      ipra_simps
      rw [step]
      ring
  have result := GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _
    (RationalAlgebra.positive_product hQ hD) hE rep (fraction_represents _ _ hE) cmp
  have ep := pred_succ (Γ := Γ) (succ q)
  exact RationalArgmin.rationalLE_congr
    (RationalAlgebra.add_congr (.eqRefl _) (fraction_congr (.eqRefl _)
      (congrMul ep.eqSymm (congrAp2 powF ep.eqSymm (.eqRefl _)))))
    (fraction_congr (.eqRefl _) (congrMul ep.eqSymm (congrAp2 powF ep.eqSymm (.eqRefl _)))) result

theorem one_step (m k : PTm n) (hm : Γ ⊢[PRAAx] le two m) (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx]
    rationalLE (add (reciprocalPower m (succ k)) (potential m (succ k))) (potential m k) := by
  have em := exponent_form m hm
  exact RationalArgmin.rationalLE_congr
    (RationalAlgebra.add_congr (reciprocal_congr em.eqSymm (.eqRefl _)) (potential_congr em.eqSymm (.eqRefl _)))
    (potential_congr em.eqSymm (.eqRefl _)) (one_step_successors (monus m two) k hk)

theorem term_at (m N i : PTm n) : Γ ⊢[PRAAx]
    RationalFiniteSum.term body i (data m N) ≐ reciprocalPower m (succ (N+i)) := by
  simp only [RationalFiniteSum.term,body,inst2,subst_reciprocalPower,subst_fstT,subst_sndT,
    PTm.subst_add,ConciseIPRA.PTm.subst_succ,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact reciprocal_congr (fst_pair _ _) (congrSucc (congrAdd (snd_pair _ _) (.eqRefl _)))

theorem zero_fraction : Γ ⊢[PRAAx]
    fraction zero one ≐ RationalIntegerNormalization.integerCode (ZT.natLit 0 : ZT n) := by
  apply RationalIntegerNormalization.normalize_integer _ _ _ (le_refl one)
  ipra_ring

theorem add_zero_right (c : PTm n) (hc : Γ ⊢[PRAAx] RationalNormalForm.wellFormed c) : Γ ⊢[PRAAx]
    add c (fraction zero one) ≐ c := by
  have hD := RationalArgmin.denominator_positive (Γ := Γ) c
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.add_guard _ _) hc
    (RationalRepresentations.represents_add _ _ _ _ _ _ (RationalRepresentations.represents_self c)
      (fraction_represents zero one (le_refl one)))
    (RationalRepresentations.represents_self c) (RationalAlgebra.positive_product hD (le_refl one)) hD
  ipra_lc

theorem tail_zero (m N : PTm n) : Γ ⊢[PRAAx] tail m N zero ≐ fraction zero one :=
  (RationalFiniteSum.sum_zero body (data m N)).eqTrans zero_fraction.eqSymm

theorem tail_succ (m N r : PTm n) : Γ ⊢[PRAAx]
    tail m N (succ r) ≐ add (tail m N r) (reciprocalPower m (succ (N+r))) :=
  (RationalFiniteSum.sum_succ body r (data m N)).eqTrans (RationalAlgebra.add_congr (.eqRefl _) (term_at m N r))

theorem tail_canonical (m N r : PTm n) : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (tail m N r) :=
  RationalFiniteSum.sum_well_formed body r (data m N)

theorem reciprocal_nonnegative (m k : PTm n) (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx]
    rationalLE (fraction zero one) (reciprocalPower m k) :=
  fraction_order _ _ _ _ (le_refl one) (GaussianFactorBudget.power_positive _ _ hk)
    (le_congr (mul_zero _).eqSymm (one_mul _).eqSymm (zero_le one))

theorem potential_nonnegative (m N : PTm n) (hm : Γ ⊢[PRAAx] le two m) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    rationalLE (fraction zero one) (potential m N) :=
  fraction_order _ _ _ _ (le_refl one) (potential_denominator_positive m N hm hN)
    (le_congr (mul_zero _).eqSymm (one_mul _).eqSymm (zero_le one))

def finiteBound (m N r : PTm n) : Fm PTm n :=
  rationalLE (fraction zero one) (tail m N r) ⋏
    rationalLE (add (tail m N r) (potential m (N+r))) (potential m N)
ipra_subst finiteBound

theorem finite_bound_zero (m N : PTm n) (hm : Γ ⊢[PRAAx] le two m) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] finiteBound m N zero := by
  have cp : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (potential m N) :=
    RationalNormalForm.normalize_well_formed _ _ (potential_denominator_positive m N hm hN)
  have init := (RationalAlgebra.add_congr (tail_zero m N)
    (potential_congr (.eqRefl m) (add_zero N))).eqTrans
    ((RationalAlgebra.add_commutative _ _).eqTrans (add_zero_right _ cp))
  exact .andI (RationalArgmin.rationalLE_congr (.eqRefl _) (tail_zero m N).eqSymm (RationalArgmin.reflexive _))
    (RationalArgmin.rationalLE_congr init.eqSymm (.eqRefl _) (RationalArgmin.reflexive _))

theorem finite_bound_succ (m N r : PTm n) (hm : Γ ⊢[PRAAx] le two m) (hN : Γ ⊢[PRAAx] le one N)
    (ih : Γ ⊢[PRAAx] finiteBound m N r) : Γ ⊢[PRAAx] finiteBound m N (succ r) := by
  have hk : Γ ⊢[PRAAx] le one (N+r) := le_trans hN (le_add_right N r)
  have step := one_step m (N+r) hm hk
  have addstep := GaussianRationalSyntheticBounds.add_monotone
    (tail m N r) (tail m N r) _ _ (RationalArgmin.reflexive _) step
  have left : Γ ⊢[PRAAx] add (tail m N (succ r)) (potential m (N+succ r)) ≐
      add (tail m N r) (add (reciprocalPower m (succ (N+r))) (potential m (succ (N+r)))) :=
    (RationalAlgebra.add_congr (tail_succ m N r) (potential_congr (.eqRefl m) (by ipra_ring))).eqTrans
      (RationalAlgebra.add_associative _ _ _)
  have conserved := RationalArgmin.transitive
    (RationalArgmin.rationalLE_congr left.eqSymm (.eqRefl _) addstep) ih.andE₂
  have zc : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (fraction zero one) :=
    RationalNormalForm.normalize_well_formed _ _ (le_refl one)
  have pos := GaussianRationalSyntheticBounds.add_monotone _ _ _ _ ih.andE₁
    (reciprocal_nonnegative m (succ (N+r)) (zero_lt_succ _))
  have positive := RationalArgmin.rationalLE_congr (add_zero_right _ zc) (tail_succ m N r).eqSymm pos
  exact .andI positive conserved

/-- A genuine quantifier-free induction on the actual rational finite-sum
program preserves positivity and the endpoint potential simultaneously. -/
theorem finite_bound (m N r : PTm n) (hm : Γ ⊢[PRAAx] le two m) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] finiteBound m N r := by
  have hall : Γ ⊢[PRAAx] .all (finiteBound (Syn.shift m) (Syn.shift N) (var 0)) := by
    refine PRA.qfInd _ ⟨trivial,trivial⟩ ?_ ?_
    · simpa only [subst_finiteBound,Syn.subst_var,Syn.subst_inst_shift,Syn.inst_zero,ConciseIPRA.PTm.subst_zero] using
        finite_bound_zero m N hm hN
    · simp only [subst_finiteBound,subst_repl_shift,Syn.repl_zero]
      have hms : Γ.map Fm.shift ⊢[PRAAx] le two (Syn.shift m) := by simpa [Fm.shift,Syn.shift] using hm.shift
      have hNs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hN.shift
      exact finite_bound_succ (Syn.shift m) (Syn.shift N) (var 0) hms.wk hNs.wk Prf.hyp0
  simpa only [subst_finiteBound,Syn.subst_var,Syn.subst_inst_shift,Syn.inst_zero] using hall.allE r

theorem tail_nonnegative (m N r : PTm n) (hm : Γ ⊢[PRAAx] le two m) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] rationalLE (fraction zero one) (tail m N r) := (finite_bound m N r hm hN).andE₁

theorem finite_conservation (m N r : PTm n) (hm : Γ ⊢[PRAAx] le two m) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] rationalLE (add (tail m N r) (potential m (N+r))) (potential m N) :=
  (finite_bound m N r hm hN).andE₂

/-- The source C17 constant is exactly 1/((m-1)N^(m-1)), for every
internal exponent and every finite runtime tail length. -/
theorem sharp_tail (m N r : PTm n) (hm : Γ ⊢[PRAAx] le two m) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] rationalLE (tail m N r) (potential m N) := by
  have hNr := le_trans hN (le_add_right N r)
  have added := GaussianRationalSyntheticBounds.add_monotone _ _ _ _ (RationalArgmin.reflexive (tail m N r))
    (potential_nonnegative m (N+r) hm hNr)
  exact RationalArgmin.transitive
    (RationalArgmin.rationalLE_congr (add_zero_right _ (tail_canonical m N r)) (.eqRefl _) added)
    (finite_conservation m N r hm hN)

/-- Fixed arity, actual scalar output: exponent, start and length are all
runtime numerical inputs. -/
def tailF : PR 3 := PTm.toPR (tail (var 0) (var 1) (var 2))
def run (m N r : PTm n) : PTm n := ap3 tailF m N r
ipra_subst run
theorem program_at (m N r : PTm n) : Γ ⊢[PRAAx] run m N r ≐ tail m N r := by
  simpa only [run,tailF,ap3,subst_tail,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    toPR_eq (Γ := Γ) (tail (var 0) (var 1) (var 2) : PTm 3) ![m,N,r]
theorem returned_nonnegative (m N r : PTm n) (hm : Γ ⊢[PRAAx] le two m) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] rationalLE (fraction zero one) (run m N r) :=
  RationalArgmin.rationalLE_congr (.eqRefl _) (program_at m N r).eqSymm (tail_nonnegative m N r hm hN)
theorem returned_bound (m N r : PTm n) (hm : Γ ⊢[PRAAx] le two m) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] rationalLE (run m N r) (potential m N) :=
  RationalArgmin.rationalLE_congr (program_at m N r).eqSymm (.eqRefl _) (sharp_tail m N r hm hN)

theorem native_antiderivative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le ((succ (var 1)+succ (var 0))*pw (var 0) (succ (var 1)))
      (succ (var 0)*pw (succ (var 0)) (succ (var 1)))) :=
  closeUniv 2 (native_antiderivative _ _)

theorem reciprocal_power_one_step_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le two (var 0) ⟶ le one (var 1) ⟶
      rationalLE (add (reciprocalPower (var 0) (succ (var 1))) (potential (var 0) (succ (var 1))))
        (potential (var 0) (var 1))) :=
  closeUniv 2 (.impI (.impI (one_step _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_finite_tail_recurrence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (tail (var 0) (var 1) zero ≐ fraction zero one ⋏
      tail (var 0) (var 1) (succ (var 2)) ≐
        add (tail (var 0) (var 1) (var 2)) (reciprocalPower (var 0) (succ (var 1+var 2)))) :=
  closeUniv 3 (.andI (tail_zero _ _) (tail_succ _ _ _))

theorem finite_tail_conservation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le two (var 0) ⟶ le one (var 1) ⟶
      rationalLE (add (tail (var 0) (var 1) (var 2)) (potential (var 0) (var 1+var 2)))
        (potential (var 0) (var 1))) :=
  closeUniv 3 (.impI (.impI (finite_conservation _ _ _ Prf.hyp1 Prf.hyp0)))

theorem source_C17_sharp_finite_tail_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le two (var 0) ⟶ le one (var 1) ⟶
      (rationalLE (fraction zero one) (tail (var 0) (var 1) (var 2)) ⋏
        rationalLE (tail (var 0) (var 1) (var 2)) (potential (var 0) (var 1)))) :=
  closeUniv 3 (.impI (.impI (.andI (tail_nonnegative _ _ _ Prf.hyp1 Prf.hyp0)
    (sharp_tail _ _ _ Prf.hyp1 Prf.hyp0))))

theorem actual_tail_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ tail (var 0) (var 1) (var 2) ⋏
      RationalNormalForm.wellFormed (tail (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.andI (program_at _ _ _) (tail_canonical _ _ _))

theorem actual_returned_C17_finite_bounds_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le two (var 0) ⟶ le one (var 1) ⟶
      (rationalLE (fraction zero one) (run (var 0) (var 1) (var 2)) ⋏
        rationalLE (run (var 0) (var 1) (var 2)) (potential (var 0) (var 1)))) :=
  closeUniv 3 (.impI (.impI (.andI (returned_nonnegative _ _ _ Prf.hyp1 Prf.hyp0)
    (returned_bound _ _ _ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.RationalReciprocalPowerTail
