import IPRADerivations.Analysis.GaussianStirlingAllOrderKernel
import IPRADerivations.Analysis.RationalSumLinearity

/-!
# Mesh-uniform tails of the original periodic Bernoulli panel sums

An entire panel averages M original kernel samples. Its upper bound is
the actual midpoint cap divided by the integer panel index to power
q + 1. Summing a suffix uses the sharp reciprocal-power tail, with
the resulting bound independent of the mesh within each panel.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPanelTail

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (fraction fraction_represents subst_fraction)
open GaussianStirlingAllOrderKernel (row row_envelope multiply_zero_right subst_row)
open GaussianStirlingAllOrderBernoulliEnvelope (cap)
open GaussianRationalHorner (positive_product)
open GaussianRationalL1 (nonnegative_of_representation nonnegative_of_lower)
open RationalAlgebra (multiply_commutative multiply_associative multiply_congr add_congr)
open RationalArithmetic (add multiply)
open RationalArgmin (rationalLE rationalLE_congr transitive)
open RationalFiniteSum (sum term termwiseLE sum_monotone)
open RationalNonnegativePowers (fraction_multiply fraction_congr)
open RationalReciprocalPowerTail (reciprocalPower potential)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private def oneBody : PTm 2 := fraction one one
private def constantBody : PTm 2 := var 1

private theorem term_constant (i c : PTm n) : term constantBody i c = c := by
  simp [term,constantBody,inst2]

private theorem multiply_one_right (c : PTm n) (hc : Γ ⊢[PRAAx] RationalNormalForm.wellFormed c) :
    Γ ⊢[PRAAx] multiply c (fraction one one) ≐ c := by
  have hD := RationalArgmin.denominator_positive (Γ := Γ) c
  have e := RationalRepresentations.represents_multiply _ _ _ _ _ _
    (RationalRepresentations.represents_self (Γ := Γ) c) (fraction_represents one one (le_refl one))
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.multiply_guard _ _) hc e
    (RationalRepresentations.represents_self c) (positive_product _ _ hD (le_refl _)) hD
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat,IPRA.Q.mk_one,map_one,IPRA.Q.mk_mul,_root_.mul_one]

private theorem fraction_add_one (j : PTm n) : Γ ⊢[PRAAx] add (fraction j one) (fraction one one) ≐ fraction (succ j) one := by
  have D : Γ ⊢[PRAAx] le one (one*one : PTm n) := by ipra_le 0
  have e := RationalRepresentations.represents_add _ _ _ _ _ _
    (fraction_represents j one (le_refl one : Γ ⊢[PRAAx] _)) (fraction_represents one one (le_refl one))
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.add_guard _ _)
    (RationalNormalForm.normalize_well_formed _ _ (le_refl one)) e (fraction_represents _ _ (le_refl one)) D (le_refl one)
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat,ZT.toZ_add]
  ipra_simps
  ring

private theorem sum_ones (j : PTm n) : Γ ⊢[PRAAx] sum oneBody j zero ≐ fraction j one := by
  have all : Γ ⊢[PRAAx] .all (sum oneBody (var 0) zero ≐ fraction (var 0) one) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp [Syn.inst_zero]
      exact (RationalFiniteSum.sum_zero oneBody zero).eqTrans RationalReciprocalPowerTail.zero_fraction.eqSymm
    · simp [Syn.repl_zero]
      have ei : term oneBody (var 0 : PTm (n+1)) zero = fraction one one := by
        simp [term,oneBody,inst2]
      have hterm : (sum oneBody (var 0) zero ≐ fraction (var 0) one) :: Γ.map Fm.shift ⊢[PRAAx]
          term oneBody (var 0) zero ≐ fraction one one := by
        rw [ei]
        exact .eqRefl _
      exact (RationalFiniteSum.sum_succ oneBody (var 0) zero).eqTrans
        ((add_congr Prf.hyp0 hterm).eqTrans (fraction_add_one _))
  simpa [Syn.inst_zero] using all.allE j

private theorem sum_constant (K c : PTm n) (hc : Γ ⊢[PRAAx] RationalNormalForm.wellFormed c) :
    Γ ⊢[PRAAx] sum constantBody K c ≐ multiply c (fraction K one) := by
  have h : Γ ⊢[PRAAx] RationalFiniteSum.termwiseEq constantBody (RationalSumLinearity.scaledBody oneBody) K
      c (pairT c zero) := by
    refine .allI (.impI ?_)
    have h₁ := RationalSumLinearity.scaled_term (Γ := lt (var 0) (Syn.shift K) :: Γ.map Fm.shift)
      oneBody (var 0) (Syn.shift c) zero
    simp only [term_constant,Syn.shift,subst_pairT,ConciseIPRA.PTm.subst_zero]
    apply RationalArgmin.rationalEq_congr (.eqRefl _) h₁.eqSymm
    have e : term oneBody (var 0 : PTm (n+1)) zero = fraction one one := by simp [term,oneBody,inst2]
    rw [e]
    have hc' : Γ.map Fm.shift ⊢[PRAAx] RationalNormalForm.wellFormed (Syn.shift c) :=
      by simpa [Fm.shift,Syn.shift] using hc.shift
    exact RationalArgmin.rationalEq_congr (.eqRefl _) (multiply_one_right _ hc'.wk).eqSymm (.eqRefl _)
  exact (RationalFiniteSum.sum_ext _ _ _ _ _ h).eqTrans ((RationalSumLinearity.sum_homogeneous oneBody K c zero).eqTrans
    (multiply_congr (.eqRefl _) (sum_ones K)))

def panelData (q A B M k : PTm n) : PTm n := pairT q (pairT A (pairT B (pairT M k)))
def panelBody (m : ℕ) : PTm 2 :=
  let v := var 1
  row m (fstT v) (fstT (sndT v)) (fstT (sndT (sndT v))) (fstT (sndT (sndT (sndT v)))) (sndT (sndT (sndT (sndT v)))) (var 0)
def panel (m : ℕ) (q A B M k : PTm n) : PTm n :=
  multiply (fraction one M) (sum (panelBody m) M (panelData q A B M k))

@[simp] theorem subst_panelData {l : ℕ} (σ : Fin n → PTm l) (q A B M k : PTm n) :
    Syn.subst σ (panelData q A B M k) =
      panelData (Syn.subst σ q) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ M) (Syn.subst σ k) := by
  simp [panelData]
@[simp] theorem subst_panel {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) (q A B M k : PTm n) :
    Syn.subst σ (panel m q A B M k) =
      panel m (Syn.subst σ q) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ M) (Syn.subst σ k) := by
  simp [panel]

private theorem row_congr (m : ℕ) {q A B M k r q' A' B' M' k' r' : PTm n}
    (h : Γ ⊢[PRAAx] q ≐ q') (hA : Γ ⊢[PRAAx] A ≐ A') (hB : Γ ⊢[PRAAx] B ≐ B') (hM : Γ ⊢[PRAAx] M ≐ M')
    (hk : Γ ⊢[PRAAx] k ≐ k') (hr : Γ ⊢[PRAAx] r ≐ r') :
    Γ ⊢[PRAAx] row m q A B M k r ≐ row m q' A' B' M' k' r' := by
  have val_five (a b c d e f : PTm n) : (![a,b,c,d,e,f] : Fin 6 → PTm n) 5 = f := rfl
  simpa only [subst_row,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_four,val_five,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (row m (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6)
      (σ := ![q,A,B,M,k,r]) (σ' := ![q',A',B',M',k',r']) (fun i => by
        fin_cases i
        exact h
        exact hA
        exact hB
        exact hM
        exact hk
        exact hr)

theorem panel_row_at (m : ℕ) (q A B M k r : PTm n) :
    Γ ⊢[PRAAx] term (panelBody m) r (panelData q A B M k) ≐ row m q A B M k r := by
  unfold term panelBody inst2
  simp only [subst_row,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact row_congr m (fst_pair _ _) ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
    ((congrFst ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _))
    ((congrFst ((congrSnd ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _))
    ((congrSnd ((congrSnd ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)) (.eqRefl _)

private theorem cancel_panel_average (M c : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hc : Γ ⊢[PRAAx] RationalNormalForm.wellFormed c) :
    Γ ⊢[PRAAx] multiply (fraction one M) (sum constantBody M c) ≐ c := by
  have same : Γ ⊢[PRAAx] fraction (M*one) (one*M) ≐ fraction one one := by
    have hp := positive_product _ _ (le_refl one) hM
    apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
      (RationalNormalForm.normalize_well_formed _ _ hp) (RationalNormalForm.normalize_well_formed _ _ (le_refl one))
      (fraction_represents _ _ hp) (fraction_represents _ _ (le_refl one)) hp (le_refl one)
    apply ZT.derive
    simp only [ZT.toZ_mul,ZT.toZ_ofNat]
    ipra_simps
    ring
  have e := (fraction_multiply M one one M (le_refl one) hM).eqTrans same
  exact (multiply_congr (.eqRefl _) (sum_constant M c hc)).eqTrans
    ((multiply_commutative _ _).eqTrans ((multiply_associative _ _ _).eqTrans
      ((multiply_congr (.eqRefl _) e).eqTrans (multiply_one_right c hc))))

theorem panel_envelope (m : ℕ) (q A B M k : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hM : Γ ⊢[PRAAx] le one M) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] rationalLE (fraction zero one) (panel m q A B M k) ⋏
      rationalLE (panel m q A B M k) (multiply (cap m) (reciprocalPower (succ q) k)) := by
  let z : PTm n := fraction zero one
  let c := multiply (cap m) (reciprocalPower (succ q) k)
  let d := panelData q A B M k
  let w := fraction one M
  let Δ := lt (var 0) (Syn.shift M) :: Γ.map Fm.shift
  have hrow : Δ ⊢[PRAAx] rationalLE (term constantBody (var 0) (Syn.shift z)) (term (panelBody m) (var 0) (Syn.shift d)) ⋏
      rationalLE (term (panelBody m) (var 0) (Syn.shift d)) (term constantBody (var 0) (Syn.shift c)) := by
    have ha' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift A) := by simpa [Fm.shift,Syn.shift] using hA.shift
    have hm' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift M) := by simpa [Fm.shift,Syn.shift] using hM.shift
    have hk' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift k) := by simpa [Fm.shift,Syn.shift] using hk.shift
    have h := row_envelope m (Syn.shift q) (Syn.shift A) (Syn.shift B) (Syn.shift M) (Syn.shift k) (var 0)
      ha'.wk hm'.wk hk'.wk (le_of_lt (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (Syn.shift M)))
    have er : Δ ⊢[PRAAx] term (panelBody m) (var 0) (Syn.shift d) ≐
        row m (Syn.shift q) (Syn.shift A) (Syn.shift B) (Syn.shift M) (Syn.shift k) (var 0) := by
      simpa [d,Syn.shift] using panel_row_at m (Syn.shift q) (Syn.shift A) (Syn.shift B) (Syn.shift M) (Syn.shift k) (var 0)
    rw [term_constant,term_constant]
    exact .andI (rationalLE_congr (by simp [z,Syn.shift]; exact .eqRefl _) er.eqSymm h.andE₁)
      (rationalLE_congr er.eqSymm (by simp [c,Syn.shift]; exact .eqRefl _) h.andE₂)
  have lo := sum_monotone constantBody (panelBody m) M z d (.allI (.impI hrow.andE₁))
  have hi := sum_monotone (panelBody m) constantBody M d c (.allI (.impI hrow.andE₂))
  have hw := nonnegative_of_representation w _ _ hM (fraction_represents one M hM)
  exact .andI
    (rationalLE_congr (cancel_panel_average M z hM (RationalNormalForm.normalize_well_formed _ _ (le_refl one)))
      (.eqRefl _) (RationalArithmetic.multiply_monotone w _ _ hw lo))
    (rationalLE_congr (.eqRefl _) (cancel_panel_average M c hM (RationalArithmetic.multiply_guard _ _))
      (RationalArithmetic.multiply_monotone w _ _ hw hi))

/-- The literal suffix starts with panel `N + 1`, with its original mesh. -/
def tailBody (m : ℕ) : PTm 2 :=
  let v := var 1
  let a := sndT v
  let b := sndT a
  let meshAndStart := sndT b
  panel m (fstT v) (fstT a) (fstT b) (fstT meshAndStart) (succ (sndT meshAndStart+var 0))

def tail (m : ℕ) (q A B M N L : PTm n) : PTm n := sum (tailBody m) L (panelData q A B M N)

@[simp] theorem subst_tail {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) (q A B M N L : PTm n) :
    Syn.subst σ (tail m q A B M N L) =
      tail m (Syn.subst σ q) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ M) (Syn.subst σ N) (Syn.subst σ L) := by
  simp [tail]

private theorem panel_congr (m : ℕ) {q A B M k q' A' B' M' k' : PTm n}
    (h : Γ ⊢[PRAAx] q ≐ q') (hA : Γ ⊢[PRAAx] A ≐ A') (hB : Γ ⊢[PRAAx] B ≐ B') (hM : Γ ⊢[PRAAx] M ≐ M')
    (hk : Γ ⊢[PRAAx] k ≐ k') : Γ ⊢[PRAAx] panel m q A B M k ≐ panel m q' A' B' M' k' := by
  simpa only [subst_panel,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (panel m (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
      (σ := ![q,A,B,M,k]) (σ' := ![q',A',B',M',k']) (fun i => by
        fin_cases i
        exact h
        exact hA
        exact hB
        exact hM
        exact hk)

theorem tail_term_at (m : ℕ) (q A B M N j : PTm n) :
    Γ ⊢[PRAAx] term (tailBody m) j (panelData q A B M N) ≐ panel m q A B M (succ (N+j)) := by
  let d := panelData q A B M N
  have e₁ : Γ ⊢[PRAAx] sndT d ≐ pairT A (pairT B (pairT M N)) := snd_pair _ _
  have e₂ := (congrSnd e₁).eqTrans (snd_pair A _)
  have e₃ := (congrSnd e₂).eqTrans (snd_pair B _)
  unfold term tailBody inst2
  simp only [subst_panel,subst_fstT,subst_sndT,ConciseIPRA.PTm.subst_succ,PTm.subst_add,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact panel_congr m (fst_pair _ _) ((congrFst e₁).eqTrans (fst_pair _ _))
    ((congrFst e₂).eqTrans (fst_pair _ _)) ((congrFst e₃).eqTrans (fst_pair _ _))
    (congrSucc (congrAdd ((congrSnd e₃).eqTrans (snd_pair _ _)) (.eqRefl j)))

theorem tail_bound (m : ℕ) (q A B M N L : PTm n) (hq : Γ ⊢[PRAAx] le one q)
    (hA : Γ ⊢[PRAAx] le one A) (hM : Γ ⊢[PRAAx] le one M) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] rationalLE (fraction zero one) (tail m q A B M N L) ⋏
      rationalLE (tail m q A B M N L) (multiply (cap m) (potential (succ q) N)) := by
  let z : PTm n := fraction zero one
  let c : PTm n := cap m
  let d := panelData q A B M N
  let v := RationalReciprocalPowerTail.data (succ q) N
  let w := pairT c v
  let reference := RationalSumLinearity.scaledBody RationalReciprocalPowerTail.body
  let Δ := lt (var 0) (Syn.shift L) :: Γ.map Fm.shift
  have hrow : Δ ⊢[PRAAx] rationalLE (term constantBody (var 0) (Syn.shift z)) (term (tailBody m) (var 0) (Syn.shift d)) ⋏
      rationalLE (term (tailBody m) (var 0) (Syn.shift d)) (term reference (var 0) (Syn.shift w)) := by
    let k := succ (Syn.shift N+var 0)
    have hk : Δ ⊢[PRAAx] le one k := zero_lt_succ _
    have ha' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift A) := by simpa [Fm.shift,Syn.shift] using hA.shift
    have hm' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift M) := by simpa [Fm.shift,Syn.shift] using hM.shift
    have h := panel_envelope m (Syn.shift q) (Syn.shift A) (Syn.shift B) (Syn.shift M) k ha'.wk hm'.wk hk
    have e : Δ ⊢[PRAAx] term (tailBody m) (var 0) (Syn.shift d) ≐
        panel m (Syn.shift q) (Syn.shift A) (Syn.shift B) (Syn.shift M) k := by
      simpa [d,k,Syn.shift] using tail_term_at m (Syn.shift q) (Syn.shift A) (Syn.shift B) (Syn.shift M) (Syn.shift N) (var 0)
    have ew : Δ ⊢[PRAAx] term reference (var 0) (Syn.shift w) ≐ multiply (cap m) (reciprocalPower (succ (Syn.shift q)) k) := by
      let v' := RationalReciprocalPowerTail.data (succ (Syn.shift q)) (Syn.shift N)
      have h₁ := RationalSumLinearity.scaled_term (Γ := Δ) RationalReciprocalPowerTail.body (var 0) (cap m) v'
      have h₂ := RationalReciprocalPowerTail.term_at (Γ := Δ) (succ (Syn.shift q)) (Syn.shift N) (var 0)
      simpa [reference,w,v,c,v',k,Syn.shift] using h₁.eqTrans (multiply_congr (.eqRefl _) h₂)
    rw [term_constant]
    exact .andI (rationalLE_congr (by simp [z,Syn.shift]; exact .eqRefl _) e.eqSymm h.andE₁)
      (rationalLE_congr e.eqSymm ew.eqSymm h.andE₂)
  have lo := sum_monotone constantBody (tailBody m) L z d (.allI (.impI hrow.andE₁))
  have hi := sum_monotone (tailBody m) reference L d w (.allI (.impI hrow.andE₂))
  have e₀ : Γ ⊢[PRAAx] sum constantBody L z ≐ fraction zero one :=
    (sum_constant L z (RationalNormalForm.normalize_well_formed _ _ (le_refl one))).eqTrans
      ((multiply_commutative z (fraction L one)).eqTrans (multiply_zero_right _))
  have eh := RationalSumLinearity.sum_homogeneous (Γ := Γ) RationalReciprocalPowerTail.body L c v
  have hq' : Γ ⊢[PRAAx] le two (succ q) := by
    have e := natEq (eq_add_of_le hq)
    ipra_le Groth.ι (IPRA.Q.mk Γ (LeanProofs.IPRA.PTm.monus q one)) using linear_combination e
  have hc := nonnegative_of_lower (Γ := Γ) z c
    (nonnegative_of_representation _ _ _ (le_refl one) (fraction_represents zero one (le_refl one)))
    (GaussianStirlingAllOrderBernoulliEnvelope.cap_nonnegative m)
  exact .andI (rationalLE_congr e₀ (.eqRefl _) lo)
    (transitive (rationalLE_congr (.eqRefl _) eh hi)
      (RationalArithmetic.multiply_monotone c _ _ hc (RationalReciprocalPowerTail.sharp_tail _ N L hq' hN)))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPanelTail
