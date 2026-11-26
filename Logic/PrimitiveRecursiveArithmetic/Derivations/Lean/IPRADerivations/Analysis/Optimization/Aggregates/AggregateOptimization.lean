import IPRADerivations.Analysis.RationalArithmetic.RationalValueBounds
import IPRADerivations.Analysis.Optimization.RationalArgmin
import IPRADerivations.Analysis.RationalArithmetic.Distances.RationalPointDistance
import IPRADerivations.Analysis.RationalArithmetic.RationalClosure
import IPRADerivations.Foundations.BoundedSyntax

/-!
# Actual finite minima and approximate support witnesses

Finite-demand Section 3, `thm:aggregate-optimization`. Values are independently
denominated signed rational codes. A fixed evaluator has three inputs: the
rational point code, its precision, and persistent runtime data. The numerical
Lipschitz constant is `A/B`, with positivity of `B` explicit.

All uses of the represented map are through its finite approximation contract;
neither coherence of finite minimizers nor validity of an output name is an
input. Raw invalid aggregate inputs have the totalization of `AggregateChain`.
Geometric interpretation uses the first `d` coordinates, with the optional
`AggregateChain.shaped` contract recovering literal stored vector length.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.AggregateOptimization

open_ipra
open LeanProofs.IPRA.Analysis.RationalSupMetric
open LeanProofs.IPRA.Analysis.RationalHausdorff
open LeanProofs.IPRA.Analysis.AggregateEquality
open LeanProofs.IPRA.Analysis.RationalValueBounds
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open LeanProofs.IPRA.Foundations.GapDecision (zabs)
open LeanProofs.IPRA.Foundations
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def evaluate (f : PR 3) (q p x : PTm n) : PTm n := ap3 f q p x

ipra_subst evaluate

def errorNumerator (A B C D p t : PTm n) : PTm n :=
  A*C*unit p*unit t+B*D*(unit p+unit t)
def errorDenominator (B D p t : PTm n) : PTm n := B*D*unit p*unit t

ipra_subst errorNumerator

ipra_subst errorDenominator

/-- The actual approximation law at six finite numerical inputs. -/
def mapInstance (f : PR 3) (d A B x q r p t C D : PTm n) : Fm PTm n :=
  pointRadius q r d C D ⟶ radius (evaluate f q p x) (evaluate f r t x)
    (errorNumerator A B C D p t) (errorDenominator B D p t)

ipra_subst mapInstance

def argument (i : Fin 6) (z : PTm n) : PTm n :=
  BoundedFormulas.at1 (BoundedSyntax.projections 6 i) z

@[simp] theorem subst_argument {m : ℕ} (σ : Fin n → PTm m) (i : Fin 6) (z : PTm n) :
    Syn.subst σ (argument i z) = argument i (Syn.subst σ z) := by
  simp [argument, BoundedFormulas.at1, Syn.subst_subst]
  apply congrArg (fun τ => Syn.subst τ (BoundedSyntax.projections 6 i))
  funext j
  fin_cases j
  rfl

/-- One universal packed tuple quantifies all point/precision/radius inputs;
the decoder is justified by the checked tuple projection equations. -/
def mapContract (f : PR 3) (d A B x : PTm n) : Fm PTm n :=
  .all (mapInstance f (Syn.shift d) (Syn.shift A) (Syn.shift B) (Syn.shift x)
    (argument 0 (var 0)) (argument 1 (var 0)) (argument 2 (var 0))
    (argument 3 (var 0)) (argument 4 (var 0)) (argument 5 (var 0)))

ipra_subst mapContract [Fm.subst_all, subst_mapInstance, Syn.subst_shift, Syn.shift_subst, subst_argument,
    Syn.subst_var, Syn.up_zero, Syn.up_succ, BoundedFormulas.subst_up_shift']

theorem mapContract_at (f : PR 3) (d A B x q r p t C D : PTm n)
    (h : Γ ⊢[PRAAx] mapContract f d A B x)
    (hqr : Γ ⊢[PRAAx] pointRadius q r d C D) :
    Γ ⊢[PRAAx] radius (evaluate f q p x) (evaluate f r t x)
      (errorNumerator A B C D p t) (errorDenominator B D p t) := by
  let z := BoundedSyntax.pack ![q,r,p,t,C,D]
  have raw : Γ ⊢[PRAAx] mapInstance f d A B x (argument 0 z) (argument 1 z)
      (argument 2 z) (argument 3 z) (argument 4 z) (argument 5 z) := by
    simpa only [mapContract, subst_mapInstance, Syn.subst_inst_shift,
      subst_argument, Syn.subst_var, Syn.inst_zero] using Prf.allE z h
  have eqs (i : Fin 6) : Γ ⊢[PRAAx] argument i z ≐ (![q,r,p,t,C,D] : Fin 6 → PTm n) i :=
    BoundedSyntax.projections_pack _ i
  have current := Prf.eqSubst (mapInstance f (var 6) (var 7) (var 8) (var 9)
      (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : Fm PTm 10)
    (σ := ![argument 0 z,argument 1 z,argument 2 z,argument 3 z,argument 4 z,argument 5 z,d,A,B,x])
    (σ' := ![q,r,p,t,C,D,d,A,B,x]) (fun i => by
      fin_cases i
      · exact eqs 0
      · exact eqs 1
      · exact eqs 2
      · exact eqs 3
      · exact eqs 4
      · exact eqs 5
      all_goals exact .eqRefl _)
    (by simpa [subst_mapInstance] using raw)
  have contract : Γ ⊢[PRAAx] mapInstance f d A B x q r p t C D := by
    simpa [subst_mapInstance] using current
  exact .impE contract hqr

/-- The stage/data specialization is an actual fixed PR evaluator. -/
def stageValues (S : PR 2) (f : PR 3) : PR 2 := PTm.toPR
  (evaluate f (entry (sample S (fstT (var 1)) (sndT (var 1))) (var 0))
    (fstT (var 1)) (sndT (var 1)) : PTm 2)

def minimumIndex (S : PR 2) (f : PR 3) (s x : PTm n) : PTm n :=
  RationalArgmin.selected (stageValues S f) (pred (length (sample S s x))) (pairT s x)
def minimumPoint (S : PR 2) (f : PR 3) (s x : PTm n) : PTm n :=
  entry (sample S s x) (minimumIndex S f s x)
def minimumValue (S : PR 2) (f : PR 3) (s x : PTm n) : PTm n :=
  evaluate f (minimumPoint S f s x) s x

ipra_subst minimumIndex
ipra_subst minimumPoint
ipra_subst minimumValue

theorem stageValues_at (S : PR 2) (f : PR 3) (s i x : PTm n) :
    Γ ⊢[PRAAx] RationalArgmin.value (stageValues S f) i (pairT s x) ≐
      evaluate f (entry (sample S s x) i) s x := by
  have base := toPR_eq (Γ := Γ)
    (evaluate f (entry (sample S (fstT (var 1)) (sndT (var 1))) (var 0))
      (fstT (var 1)) (sndT (var 1)) : PTm 2) ![i,pairT s x]
  have args := Prf.eqCongr (Γ := Γ)
    (evaluate f (entry (sample S (var 0) (var 2)) (var 1)) (var 0) (var 2) : PTm 3)
    (σ := ![fstT (pairT s x),i,sndT (pairT s x)]) (σ' := ![s,i,x]) (fun j => by
      fin_cases j
      · exact fst_pair _ _
      · exact .eqRefl _
      · exact snd_pair _ _)
  have first : Γ ⊢[PRAAx] RationalArgmin.value (stageValues S f) i (pairT s x) ≐
      evaluate f (entry (sample S (fstT (pairT s x)) (sndT (pairT s x))) i)
        (fstT (pairT s x)) (sndT (pairT s x)) := by
    simpa [stageValues, RationalArgmin.value, ap2, subst_evaluate, subst_sample, subst_entry] using base
  exact first.eqTrans (by simpa [subst_evaluate] using args)

theorem minimum_index_range (S : PR 2) (f : PR 3) (s x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) :
    Γ ⊢[PRAAx] lt (minimumIndex S f s x) (length (sample S s x)) := by
  have positive := nonempty_at S s x hS
  have len : Γ ⊢[PRAAx] length (sample S s x) ≐ succ (pred (length (sample S s x))) :=
    AnalyticNumberTheory.Primes.eq_succ_pred ((eq_add_of_le positive).eqTrans (by ipra_ring))
  have bound := RationalArgmin.selected_spec (Γ := Γ) (stageValues S f)
    (pred (length (sample S s x))) (pairT s x)
  exact le_congr (.eqRefl _) len.eqSymm
    ((succ_monus_succ _ _).eqTrans bound)

theorem minimum_value_le (S : PR 2) (f : PR 3) (s i x : PTm n)
    (hi : Γ ⊢[PRAAx] lt i (length (sample S s x))) :
    Γ ⊢[PRAAx] RationalArgmin.rationalLE (minimumValue S f s x)
      (evaluate f (entry (sample S s x) i) s x) := by
  have bound : Γ ⊢[PRAAx] le i (pred (length (sample S s x))) := by
    have e : Γ ⊢[PRAAx] length (sample S s x) ≐
        succ (i+monus (length (sample S s x)) (succ i)) :=
      (eq_add_of_le hi).eqTrans (succ_add _ _)
    have ep : Γ ⊢[PRAAx] pred (length (sample S s x)) ≐
        i+monus (length (sample S s x)) (succ i) :=
      (congrPred e).eqTrans (pred_succ _)
    exact le_congr (.eqRefl _) ep.eqSymm (le_add_right _ _)
  exact RationalArgmin.rationalLE_congr (stageValues_at S f s (minimumIndex S f s x) x)
    (stageValues_at S f s i x)
    (RationalArgmin.selected_minimal (stageValues S f) (pred (length (sample S s x))) i (pairT s x) bound)

theorem minimum_upper (S : PR 2) (f : PR 3) (s t d A B C D x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x)
    (hmap : Γ ⊢[PRAAx] mapContract f d A B x)
    (hcover : Γ ⊢[PRAAx] originalClose (sample S t x) (sample S s x) d C D) :
    Γ ⊢[PRAAx] upper (minimumValue S f s x) (minimumValue S f t x)
      (errorNumerator A B C D s t) (errorDenominator B D s t) := by
  let i := minimumIndex S f t x
  let j := RationalNearest.selected (sample S t x) (sample S s x) d i
  have hj : Γ ⊢[PRAAx] lt j (length (sample S s x)) :=
    RationalNearest.selected_spec _ _ _ _ (nonempty_at S s x hS)
  have near := RationalNearest.cover_selected_radius (sample S t x) (sample S s x) d i C D
    (minimum_index_range S f t x hS) (nonempty_at S s x hS) hcover
  have reverse := AggregateChain.point_symmetric _ _ d C D near
  have value := mapContract_at f d A B x (entry (sample S s x) j) (minimumPoint S f t x)
    s t C D hmap reverse
  exact upper_order_left (minimumValue S f s x) (evaluate f (entry (sample S s x) j) s x)
    (minimumValue S f t x) _ _ (minimum_value_le S f s j x hj)
    (upper_of_radius _ _ _ _ value)

/-- Actual finite minima have the sharp source `(L+1)(e_s+e_t)` bound. -/
theorem minima_cauchy (S : PR 2) (f : PR 3) (s t d A B x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hmap : Γ ⊢[PRAAx] mapContract f d A B x) :
    Γ ⊢[PRAAx] radius (minimumValue S f s x) (minimumValue S f t x)
      ((A+B)*(unit s+unit t)) (B*unit s*unit t) := by
  have hab := minimum_upper S f s t d A B (unit t+unit s) (unit t*unit s) x
    hS hmap (regular_at S t s d x hR)
  have hba := minimum_upper S f t s d A B (unit s+unit t) (unit s*unit t) x
    hS hmap (regular_at S s t d x hR)
  have positive : Γ ⊢[PRAAx] le one (unit s*unit t) :=
    le_congr (one_mul one) (.eqRefl _) (le_mul_mono (unit_positive s) (unit_positive t))
  apply radius_of_upper
  · exact upper_cancel _ _ _ _ (unit s*unit t) positive
      (upper_congr (.eqRefl _) (.eqRefl _) (by unfold errorNumerator; ipra_ring)
        (by unfold errorDenominator; ipra_ring) hab)
  · exact upper_cancel _ _ _ _ (unit s*unit t) positive
      (upper_congr (.eqRefl _) (.eqRefl _) (by unfold errorNumerator; ipra_ring)
        (by unfold errorDenominator; ipra_ring) hba)

def valueName (S : PR 2) (f : PR 3) (k c x : PTm n) : PTm n := minimumValue S f (k+c) x

ipra_subst valueName

/-- Precision shifting regularizes the actual minimum-value program. -/
theorem value_name_regular (S : PR 2) (f : PR 3) (k l c d A B x : PTm n)
    (hB : Γ ⊢[PRAAx] le one B)
    (hc : Γ ⊢[PRAAx] le (A+B) (B*unit c))
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hmap : Γ ⊢[PRAAx] mapContract f d A B x) :
    Γ ⊢[PRAAx] radius (valueName S f k c x) (valueName S f l c x)
      (unit k+unit l) (unit k*unit l) := by
  have h := minima_cauchy S f (k+c) (l+c) d A B x hS hR hmap
  have denominatorPos : Γ ⊢[PRAAx] le one (B*unit (k+c)*unit (l+c)) :=
    le_congr (by ipra_ring) (.eqRefl _)
      (le_mul_mono (le_mul_mono hB (unit_positive (k+c))) (unit_positive (l+c)))
  apply radius_mono _ _ _ _ _ _ denominatorPos h
  have bound := le_mul_mono hc (le_refl (unit c*(unit k+unit l)*unit k*unit l))
  have ek := natEq (AggregateChain.unit_add (Γ := Γ) k c)
  have el := natEq (AggregateChain.unit_add (Γ := Γ) l c)
  apply le_congr ?_ ?_ bound
  · apply deriveNat
    ipra_simps
    rw [ek,el]
    ring
  · apply deriveNat
    ipra_simps
    rw [ek,el]
    ring

/-- The exact finite budget before the final runtime precision shifts. -/
def witnessNumerator (A B s p r : PTm n) : PTm n :=
  (num 4*A+two*B)*unit p*unit r+B*unit s*unit r+(A+B)*unit p*unit s
def witnessDenominator (B s p r : PTm n) : PTm n := B*unit s*unit p*unit r

ipra_subst witnessNumerator
ipra_subst witnessDenominator

theorem combine_witness_budget (a b c A B s p r : PTm n)
    (hB : Γ ⊢[PRAAx] le one B)
    (hab : Γ ⊢[PRAAx] upper a b
      (errorNumerator A B (num 3) (unit s) p s) (errorDenominator B (unit s) p s))
    (hbc : Γ ⊢[PRAAx] upper b c ((A+B)*(unit s+unit r)) (B*unit s*unit r)) :
    Γ ⊢[PRAAx] upper a c (witnessNumerator A B s p r) (witnessDenominator B s p r) := by
  have combined := upper_triangle a b c _ _ _ _ hab hbc
  have pos : Γ ⊢[PRAAx] le one (B*unit s*unit s) :=
    le_congr (by ipra_ring) (.eqRefl _)
      (le_mul_mono (le_mul_mono hB (unit_positive s)) (unit_positive s))
  exact upper_cancel a c _ _ (B*unit s*unit s) pos
    (upper_congr (.eqRefl _) (.eqRefl _)
      (by unfold errorNumerator errorDenominator witnessNumerator; ipra_ring)
      (by unfold errorDenominator witnessDenominator; ipra_ring) combined)

/-- An observation near the actual minimizing entry has this upper value bound. -/
theorem near_minimum_upper (S : PR 2) (f : PR 3) (q s p r d A B x : PTm n)
    (hB : Γ ⊢[PRAAx] le one B)
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hmap : Γ ⊢[PRAAx] mapContract f d A B x)
    (hnear : Γ ⊢[PRAAx] pointRadius q (minimumPoint S f s x) d (num 3) (unit s)) :
    Γ ⊢[PRAAx] upper (evaluate f q p x) (minimumValue S f r x)
      (witnessNumerator A B s p r) (witnessDenominator B s p r) := by
  exact combine_witness_budget _ _ _ A B s p r hB
    (upper_of_radius _ _ _ _ (mapContract_at f d A B x q (minimumPoint S f s x)
      p s (num 3) (unit s) hmap hnear))
    (upper_of_radius _ _ _ _ (minima_cauchy S f s r d A B x hS hR hmap))

/-- A finite nearby aggregate entry proves a lower bound, with no chosen
exact member or completed infimum premise. -/
theorem observation_lower (S : PR 2) (f : PR 3) (q j s p r d A B x : PTm n)
    (hB : Γ ⊢[PRAAx] le one B)
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hmap : Γ ⊢[PRAAx] mapContract f d A B x)
    (hj : Γ ⊢[PRAAx] lt j (length (sample S s x)))
    (hnear : Γ ⊢[PRAAx] pointRadius q (entry (sample S s x) j) d (num 3) (unit s)) :
    Γ ⊢[PRAAx] upper (minimumValue S f r x) (evaluate f q p x)
      (witnessNumerator A B s p r) (witnessDenominator B s p r) := by
  have map := mapContract_at f d A B x (entry (sample S s x) j) q s p
    (num 3) (unit s) hmap (AggregateChain.point_symmetric _ _ d _ _ hnear)
  have first : Γ ⊢[PRAAx] upper (minimumValue S f s x) (evaluate f q p x)
      (errorNumerator A B (num 3) (unit s) p s) (errorDenominator B (unit s) p s) :=
    upper_order_left _ _ _ _ _ (minimum_value_le S f s j x hj)
      (upper_congr (.eqRefl _) (.eqRefl _) (by unfold errorNumerator; ipra_ring)
        (by unfold errorDenominator; ipra_ring) (upper_of_radius _ _ _ _ map))
  have second := upper_of_radius _ _ _ _ (minima_cauchy S f r s d A B x hS hR hmap)
  have combined := upper_triangle _ _ _ _ _ _ _ second first
  have pos : Γ ⊢[PRAAx] le one (B*unit s*unit s) :=
    le_congr (by ipra_ring) (.eqRefl _)
      (le_mul_mono (le_mul_mono hB (unit_positive s)) (unit_positive s))
  exact upper_cancel _ _ _ _ (B*unit s*unit s) pos
    (upper_congr (.eqRefl _) (.eqRefl _)
      (by unfold errorNumerator errorDenominator witnessNumerator; ipra_ring)
      (by unfold errorDenominator witnessDenominator; ipra_ring) combined)

/-- `4L+2` is retained exactly, including `L=0`, in the runtime budget. -/
theorem shift_witness_budget (a b A B k t l bshift c : PTm n)
    (hB : Γ ⊢[PRAAx] le one B)
    (hb : Γ ⊢[PRAAx] le (num 4*A+two*B) (B*unit bshift))
    (hc : Γ ⊢[PRAAx] le (A+B) (B*unit c))
    (h : Γ ⊢[PRAAx] upper a b (witnessNumerator A B (k+bshift) (t+c) (l+c))
      (witnessDenominator B (k+bshift) (t+c) (l+c))) :
    Γ ⊢[PRAAx] upper a b
      (unit t*unit l+unit k*unit l+unit k*unit t) (unit k*unit t*unit l) := by
  have pos : Γ ⊢[PRAAx] le one (witnessDenominator B (k+bshift) (t+c) (l+c)) :=
    le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono
      (le_mul_mono (le_mul_mono hB (unit_positive _)) (unit_positive _)) (unit_positive _))
  apply upper_mono _ _ _ _ _ _ pos h
  have mid : Γ ⊢[PRAAx] le B (B*unit c) :=
    le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl B) (unit_positive c))
  have h1 := le_mul_mono hb (le_refl (unit (t+c)*unit (l+c)*unit k*unit t*unit l))
  have h2 := le_mul_mono mid (le_refl (unit (k+bshift)*unit (l+c)*unit k*unit t*unit l))
  have h3 := le_mul_mono hc (le_refl (unit (t+c)*unit (k+bshift)*unit k*unit t*unit l))
  have total := add_le_add₂ (add_le_add₂ h1 h2) h3
  have es := natEq (AggregateChain.unit_add (Γ := Γ) k bshift)
  have ep := natEq (AggregateChain.unit_add (Γ := Γ) t c)
  have er := natEq (AggregateChain.unit_add (Γ := Γ) l c)
  apply le_congr ?_ ?_ total
  · unfold witnessNumerator
    ipra_ring
  · unfold witnessDenominator
    apply deriveNat
    ipra_simps
    rw [es,ep,er]
    ring

def witnessName (S : PR 2) (f : PR 3) (k t b d x : PTm n) : PTm n :=
  AggregateChain.name S t (k+b) (minimumIndex S f (k+b) x) d x

def witnessValue (S : PR 2) (f : PR 3) (k t b c d x : PTm n) : PTm n :=
  evaluate f (witnessName S f k (t+c) b d x) (t+c) x

ipra_subst witnessName
ipra_subst witnessValue

theorem witness_name_regular (S : PR 2) (f : PR 3) (k t u b d x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x) :
    Γ ⊢[PRAAx] pointRadius (witnessName S f k t b d x) (witnessName S f k u b d x)
      d (unit t+unit u) (unit t*unit u) :=
  AggregateChain.name_regular S t u (k+b) (minimumIndex S f (k+b) x) d x hS hR
    (minimum_index_range S f (k+b) x hS)

theorem witness_support (S : PR 2) (f : PR 3) (k b d x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x) :
    Γ ⊢[PRAAx] AggregateChain.supportAll S (k+b) (minimumIndex S f (k+b) x) d x :=
  .andE₂ (.andE₂ (AggregateChain.aggregate_chain S (k+b) (minimumIndex S f (k+b) x)
    d x hS hR (minimum_index_range S f (k+b) x hS)))

/-- Arbitrarily fine finite observations establish the desired approximate
value inequality. The two residual terms are the observation errors. -/
theorem witness_value_approximate (S : PR 2) (f : PR 3) (k t l b c d A B x : PTm n)
    (hB : Γ ⊢[PRAAx] le one B)
    (hb : Γ ⊢[PRAAx] le (num 4*A+two*B) (B*unit b))
    (hc : Γ ⊢[PRAAx] le (A+B) (B*unit c))
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hmap : Γ ⊢[PRAAx] mapContract f d A B x) :
    Γ ⊢[PRAAx] upper (witnessValue S f k t b c d x) (valueName S f l c x)
      (unit t*unit l+unit k*unit l+unit k*unit t) (unit k*unit t*unit l) := by
  apply shift_witness_budget _ _ A B k t l b c hB hb hc
  apply near_minimum_upper S f _ (k+b) (t+c) (l+c) d A B x hB hS hR hmap
  exact AggregateChain.name_near_initial S (t+c) (k+b) (minimumIndex S f (k+b) x) d x
    hS hR (minimum_index_range S f (k+b) x hS)

theorem map_regular_pair (f : PR 3) (q r p t d A B x : PTm n)
    (hmap : Γ ⊢[PRAAx] mapContract f d A B x)
    (hqr : Γ ⊢[PRAAx] pointRadius q r d (unit p+unit t) (unit p*unit t)) :
    Γ ⊢[PRAAx] radius (evaluate f q p x) (evaluate f r t x)
      ((A+B)*(unit p+unit t)) (B*unit p*unit t) := by
  have raw := mapContract_at f d A B x q r p t (unit p+unit t) (unit p*unit t) hmap hqr
  have pos : Γ ⊢[PRAAx] le one (unit p*unit t) :=
    le_congr (one_mul one) (.eqRefl _) (le_mul_mono (unit_positive p) (unit_positive t))
  exact radius_cancel _ _ _ _ (unit p*unit t) pos
    (radius_congr (.eqRefl _) (.eqRefl _) (by unfold errorNumerator; ipra_ring)
      (by unfold errorDenominator; ipra_ring) raw)

theorem shifted_regular_budget (a b k l c A B : PTm n)
    (hB : Γ ⊢[PRAAx] le one B)
    (hc : Γ ⊢[PRAAx] le (A+B) (B*unit c))
    (h : Γ ⊢[PRAAx] radius a b ((A+B)*(unit (k+c)+unit (l+c)))
      (B*unit (k+c)*unit (l+c))) :
    Γ ⊢[PRAAx] radius a b (unit k+unit l) (unit k*unit l) := by
  have pos : Γ ⊢[PRAAx] le one (B*unit (k+c)*unit (l+c)) :=
    le_congr (by ipra_ring) (.eqRefl _)
      (le_mul_mono (le_mul_mono hB (unit_positive _)) (unit_positive _))
  apply radius_mono _ _ _ _ _ _ pos h
  have bound := le_mul_mono hc (le_refl (unit c*(unit k+unit l)*unit k*unit l))
  have ek := natEq (AggregateChain.unit_add (Γ := Γ) k c)
  have el := natEq (AggregateChain.unit_add (Γ := Γ) l c)
  apply le_congr ?_ ?_ bound
  · apply deriveNat
    ipra_simps
    rw [ek,el]
    ring
  · apply deriveNat
    ipra_simps
    rw [ek,el]
    ring

/-- The prescribed represented-map extension is itself a regular name. -/
theorem witness_value_regular (S : PR 2) (f : PR 3) (k t u b c d A B x : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hc : Γ ⊢[PRAAx] le (A+B) (B*unit c))
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hmap : Γ ⊢[PRAAx] mapContract f d A B x) :
    Γ ⊢[PRAAx] radius (witnessValue S f k t b c d x) (witnessValue S f k u b c d x)
      (unit t+unit u) (unit t*unit u) :=
  shifted_regular_budget _ _ t u c A B hB hc
    (map_regular_pair f _ _ (t+c) (u+c) d A B x hmap
      (witness_name_regular S f k (t+c) (u+c) b d x hS hR))

/-- Actual primitive-recursive programs for the scalar name and the
two-parameter family of support-point names. -/
def minimumF (S : PR 2) (f : PR 3) : PR 2 :=
  PTm.toPR (minimumValue S f (var 0) (var 1))
def valueNameF (S : PR 2) (f : PR 3) : PR 3 :=
  PTm.toPR (valueName S f (var 0) (var 1) (var 2))
def witnessNameF (S : PR 2) (f : PR 3) : PR 5 :=
  PTm.toPR (witnessName S f (var 0) (var 1) (var 2) (var 3) (var 4))
def witnessValueF (S : PR 2) (f : PR 3) : PR 6 :=
  PTm.toPR (witnessValue S f (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))

def apply6 (v : PR 6) (a b c d e f : PTm n) : PTm n := .app v ![a,b,c,d,e,f]

theorem minimum_program_at (S : PR 2) (f : PR 3) (s x : PTm n) :
    Γ ⊢[PRAAx] ap2 (minimumF S f) s x ≐ minimumValue S f s x := by
  have h := toPR_eq (Γ := Γ) (minimumValue S f (var 0) (var 1) : PTm 2) ![s,x]
  simpa [minimumF, ap2] using h

theorem value_program_at (S : PR 2) (f : PR 3) (k c x : PTm n) :
    Γ ⊢[PRAAx] ap3 (valueNameF S f) k c x ≐ valueName S f k c x := by
  have h := toPR_eq (Γ := Γ) (valueName S f (var 0) (var 1) (var 2) : PTm 3) ![k,c,x]
  simpa [valueNameF, ap3] using h

theorem witness_program_at (S : PR 2) (f : PR 3) (k t b d x : PTm n) :
    Γ ⊢[PRAAx] RationalHausdorff.apply5 (witnessNameF S f) k t b d x ≐ witnessName S f k t b d x := by
  have h := toPR_eq (Γ := Γ) (witnessName S f (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![k,t,b,d,x]
  simpa [witnessNameF, RationalHausdorff.apply5] using h

theorem witness_value_program_at (S : PR 2) (f : PR 3) (k t b c d x : PTm n) :
    Γ ⊢[PRAAx] apply6 (witnessValueF S f) k t b c d x ≐ witnessValue S f k t b c d x := by
  have h := toPR_eq (Γ := Γ)
    (witnessValue S f (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![k,t,b,c,d,x]
  simpa [witnessValueF, apply6] using h

def valueRegular (S : PR 2) (f : PR 3) (c x : PTm n) : Fm PTm n :=
  .all (.all (radius (valueName S f (var 1) (Syn.shift (Syn.shift c)) (Syn.shift (Syn.shift x)))
    (valueName S f (var 0) (Syn.shift (Syn.shift c)) (Syn.shift (Syn.shift x)))
    (unit (var 1)+unit (var 0)) (unit (var 1)*unit (var 0))))

def witnessValueRegular (S : PR 2) (f : PR 3) (k b c d x : PTm n) : Fm PTm n :=
  .all (.all (radius
    (witnessValue S f (Syn.shift (Syn.shift k)) (var 1) (Syn.shift (Syn.shift b))
      (Syn.shift (Syn.shift c)) (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x)))
    (witnessValue S f (Syn.shift (Syn.shift k)) (var 0) (Syn.shift (Syn.shift b))
      (Syn.shift (Syn.shift c)) (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x)))
    (unit (var 1)+unit (var 0)) (unit (var 1)*unit (var 0))))

def approximationAll (S : PR 2) (f : PR 3) (k b c d x : PTm n) : Fm PTm n :=
  .all (.all (upper
    (witnessValue S f (Syn.shift (Syn.shift k)) (var 1) (Syn.shift (Syn.shift b))
      (Syn.shift (Syn.shift c)) (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x)))
    (valueName S f (var 0) (Syn.shift (Syn.shift c)) (Syn.shift (Syn.shift x)))
    (unit (var 1)*unit (var 0)+unit (Syn.shift (Syn.shift k))*unit (var 0)+
      unit (Syn.shift (Syn.shift k))*unit (var 1))
    (unit (Syn.shift (Syn.shift k))*unit (var 1)*unit (var 0))))

def witnessResult (S : PR 2) (f : PR 3) (k b c d x : PTm n) : Fm PTm n :=
  AggregateChain.nameRegular S (k+b) (minimumIndex S f (k+b) x) d x ⋏
    (AggregateChain.supportAll S (k+b) (minimumIndex S f (k+b) x) d x ⋏
      (witnessValueRegular S f k b c d x ⋏ approximationAll S f k b c d x))

def optimizationResult (S : PR 2) (f : PR 3) (b c d x : PTm n) : Fm PTm n :=
  valueRegular S f c x ⋏ .all (witnessResult S f (var 0) (Syn.shift b) (Syn.shift c)
    (Syn.shift d) (Syn.shift x))

theorem value_regular_all (S : PR 2) (f : PR 3) (c d A B x : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hc : Γ ⊢[PRAAx] le (A+B) (B*unit c))
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hmap : Γ ⊢[PRAAx] mapContract f d A B x) : Γ ⊢[PRAAx] valueRegular S f c x := by
  refine .allI (.allI ?_)
  exact value_name_regular S f (var 1) (var 0) _ _ (Syn.shift (Syn.shift A)) _ _
    (by simpa [Fm.shift, Syn.shift, two, one] using hB.shift.shift) (by simpa [Fm.shift, Syn.shift, two, one] using hc.shift.shift)
    (by simpa [Fm.shift, Syn.shift, two, one] using hS.shift.shift) (by simpa [Fm.shift, Syn.shift, two, one] using hR.shift.shift)
    (by simpa [Fm.shift, Syn.shift, two, one] using hmap.shift.shift)

theorem witness_value_regular_all (S : PR 2) (f : PR 3) (k b c d A B x : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hc : Γ ⊢[PRAAx] le (A+B) (B*unit c))
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hmap : Γ ⊢[PRAAx] mapContract f d A B x) : Γ ⊢[PRAAx] witnessValueRegular S f k b c d x := by
  refine .allI (.allI ?_)
  exact witness_value_regular S f _ (var 1) (var 0) _ _ _ (Syn.shift (Syn.shift A)) _ _
    (by simpa [Fm.shift, Syn.shift, two, one] using hB.shift.shift) (by simpa [Fm.shift, Syn.shift, two, one] using hc.shift.shift)
    (by simpa [Fm.shift, Syn.shift, two, one] using hS.shift.shift) (by simpa [Fm.shift, Syn.shift, two, one] using hR.shift.shift)
    (by simpa [Fm.shift, Syn.shift, two, one] using hmap.shift.shift)

theorem approximation_all (S : PR 2) (f : PR 3) (k b c d A B x : PTm n)
    (hB : Γ ⊢[PRAAx] le one B)
    (hb : Γ ⊢[PRAAx] le (num 4*A+two*B) (B*unit b))
    (hc : Γ ⊢[PRAAx] le (A+B) (B*unit c))
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hmap : Γ ⊢[PRAAx] mapContract f d A B x) : Γ ⊢[PRAAx] approximationAll S f k b c d x := by
  refine .allI (.allI ?_)
  exact witness_value_approximate S f _ (var 1) (var 0) _ _ _ (Syn.shift (Syn.shift A)) _ _
    (by simpa [Fm.shift, Syn.shift, two, one] using hB.shift.shift) (by simpa [Fm.shift, Syn.shift, two, one] using hb.shift.shift)
    (by simpa [Fm.shift, Syn.shift, two, one] using hc.shift.shift) (by simpa [Fm.shift, Syn.shift, two, one] using hS.shift.shift)
    (by simpa [Fm.shift, Syn.shift, two, one] using hR.shift.shift) (by simpa [Fm.shift, Syn.shift, two, one] using hmap.shift.shift)

theorem witness_result (S : PR 2) (f : PR 3) (k b c d A B x : PTm n)
    (hB : Γ ⊢[PRAAx] le one B)
    (hb : Γ ⊢[PRAAx] le (num 4*A+two*B) (B*unit b))
    (hc : Γ ⊢[PRAAx] le (A+B) (B*unit c))
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hmap : Γ ⊢[PRAAx] mapContract f d A B x) : Γ ⊢[PRAAx] witnessResult S f k b c d x :=
  .andI (AggregateChain.name_regular_all S (k+b) (minimumIndex S f (k+b) x) d x hS hR
    (minimum_index_range S f (k+b) x hS))
    (.andI (witness_support S f k b d x hS hR)
      (.andI (witness_value_regular_all S f k b c d A B x hB hc hS hR hmap)
        (approximation_all S f k b c d A B x hB hb hc hS hR hmap)))

theorem aggregate_optimization (S : PR 2) (f : PR 3) (b c d A B x : PTm n)
    (hB : Γ ⊢[PRAAx] le one B)
    (hb : Γ ⊢[PRAAx] le (num 4*A+two*B) (B*unit b))
    (hc : Γ ⊢[PRAAx] le (A+B) (B*unit c))
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hmap : Γ ⊢[PRAAx] mapContract f d A B x) : Γ ⊢[PRAAx] optimizationResult S f b c d x := by
  refine .andI (value_regular_all S f c d A B x hB hc hS hR hmap) (.allI ?_)
  exact witness_result S f (var 0) _ _ _ (Syn.shift A) _ _
    (by simpa [Fm.shift, Syn.shift, two, one] using hB.shift) (by simpa [Fm.shift, Syn.shift, two, one] using hb.shift)
    (by simpa [Fm.shift, Syn.shift, two, one] using hc.shift) (by simpa [Fm.shift, Syn.shift, two, one] using hS.shift)
    (by simpa [Fm.shift, Syn.shift, two, one] using hR.shift) (by simpa [Fm.shift, Syn.shift, two, one] using hmap.shift)

theorem aggregate_optimization_closed (S : PR 2) (f : PR 3) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (le one (var 4) ⟶ le (num 4*var 3+two*var 4) (var 4*unit (var 0)) ⟶
        le (var 3+var 4) (var 4*unit (var 1)) ⟶ nonempty S (var 5) ⟶
        regular S (var 2) (var 5) ⟶ mapContract f (var 2) (var 3) (var 4) (var 5) ⟶
        optimizationResult S f (var 0) (var 1) (var 2) (var 5)) := by
  apply closeUniv 6
  refine .impI (.impI (.impI (.impI (.impI (.impI ?_)))))
  exact aggregate_optimization S f (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp))
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp))

def pointRegular (U : PR 2) (d x : PTm n) : Fm PTm n :=
  .all (.all (pointRadius (sample U (var 1) (Syn.shift (Syn.shift x)))
    (sample U (var 0) (Syn.shift (Syn.shift x))) (Syn.shift (Syn.shift d))
    (unit (var 1)+unit (var 0)) (unit (var 1)*unit (var 0))))

/-- The nonnegative actual distance-name samples name zero. This is a
finite numerical support condition, not an assumed optimization conclusion. -/
def supportZero (U S : PR 2) (d x : PTm n) : Fm PTm n :=
  .all (le (unit (var 0)*RationalPointDistance.numerator
    (sample U (succ (var 0)) (Syn.shift x)) (sample S (succ (var 0)) (Syn.shift x)) (Syn.shift d))
    (RationalPointDistance.denominator (sample U (succ (var 0)) (Syn.shift x))
      (sample S (succ (var 0)) (Syn.shift x)) (Syn.shift d)))

ipra_subst pointRegular [Fm.subst_all, subst_pointRadius, subst_sample, subst_unit, PTm.subst_add, PTm.subst_mul,
    Syn.subst_var, Syn.up_zero, Syn.up_one, Syn.up_succ, Syn.subst_shift, Syn.shift_subst, Syn.shift_var,
    Fin.succ_zero_eq_one]
ipra_subst supportZero [Fm.subst_all, subst_le, PTm.subst_mul, subst_unit, RationalPointDistance.subst_numerator,
    RationalPointDistance.subst_denominator, subst_sample, Syn.subst_var, Syn.up_zero, Syn.up_succ, Syn.subst_shift,
    Syn.shift_subst, ConciseIPRA.PTm.subst_succ]

theorem pointRegular_at (U : PR 2) (p q d x : PTm n) (h : Γ ⊢[PRAAx] pointRegular U d x) :
    Γ ⊢[PRAAx] pointRadius (sample U p x) (sample U q x) d (unit p+unit q) (unit p*unit q) := by
  have first : Γ ⊢[PRAAx] .all (pointRadius (sample U (Syn.shift p) (Syn.shift x))
      (sample U (var 0) (Syn.shift x)) (Syn.shift d)
      (unit (Syn.shift p)+unit (var 0)) (unit (Syn.shift p)*unit (var 0))) := by
    simpa only [pointRegular, Fm.subst_all, subst_pointRadius, subst_sample, subst_unit,
      PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.up_zero, Syn.up_one, Syn.up_succ,
      Syn.inst_zero, Syn.inst_succ, Syn.subst_inst_shift, Syn.shift_var,
      BoundedFormulas.subst_up_shift'] using Prf.allE p h
  simpa only [subst_pointRadius, subst_sample, subst_unit, PTm.subst_add, PTm.subst_mul,
    Syn.subst_var, Syn.inst_zero, Syn.inst_succ, Syn.subst_inst_shift] using Prf.allE q first

theorem supportZero_at (U S : PR 2) (v d x : PTm n) (h : Γ ⊢[PRAAx] supportZero U S d x) :
    Γ ⊢[PRAAx] le (unit v*RationalPointDistance.numerator
      (sample U (succ v) x) (sample S (succ v) x) d)
      (RationalPointDistance.denominator (sample U (succ v) x) (sample S (succ v) x) d) := by
  simpa only [supportZero, subst_le, PTm.subst_mul, subst_unit,
    RationalPointDistance.subst_numerator, RationalPointDistance.subst_denominator,
    subst_sample, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_succ] using Prf.allE v h

/-- Three genuine finite comparisons give a removable `2e_v` tail. -/
theorem support_distance_tail (U S : PR 2) (p s v d x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hU : Γ ⊢[PRAAx] pointRegular U d x) (hzero : Γ ⊢[PRAAx] supportZero U S d x) :
    Γ ⊢[PRAAx] le ((unit p*unit s*unit v)*
        RationalPointDistance.numerator (sample U p x) (sample S s x) d)
      ((unit v*unit s+unit v*unit p+two*unit p*unit s)*
        RationalPointDistance.denominator (sample U p x) (sample S s x) d) := by
  let j := RationalPointDistance.selected (sample U (succ v) x) (sample S (succ v) x) d
  let j' := RationalNearest.selected (sample S (succ v) x) (sample S s x) d j
  have hj : Γ ⊢[PRAAx] lt j (length (sample S (succ v) x)) :=
    RationalPointDistance.selected_spec _ _ _ (nonempty_at S _ x hS)
  have hj' : Γ ⊢[PRAAx] lt j' (length (sample S s x)) :=
    RationalNearest.selected_spec _ _ _ _ (nonempty_at S s x hS)
  have near := RationalPointDistance.selected_radius (sample U (succ v) x)
    (sample S (succ v) x) d one (unit v) (nonempty_at S _ x hS)
    (le_congr (.eqRefl _) (one_mul _).eqSymm (supportZero_at U S v d x hzero))
  have covered := RationalNearest.cover_selected_radius (sample S (succ v) x) (sample S s x)
    d j (unit (succ v)+unit s) (unit (succ v)*unit s) hj (nonempty_at S s x hS)
    (regular_at S (succ v) s d x hR)
  have first := RationalHausdorffTriangle.pointRadius_triangle _ _ _ d _ _ _ _
    (pointRegular_at U p (succ v) d x hU) near
  have total := RationalHausdorffTriangle.pointRadius_triangle _ _ _ d _ _ _ _ first covered
  have scalePos : Γ ⊢[PRAAx] le one (unit (succ v)*unit (succ v)) :=
    le_congr (one_mul one) (.eqRefl _) (le_mul_mono (unit_positive _) (unit_positive _))
  have nearby : Γ ⊢[PRAAx] pointRadius (sample U p x) (entry (sample S s x) j') d
      (unit v*unit s+unit v*unit p+two*unit p*unit s) (unit p*unit s*unit v) := by
    apply AggregateChain.point_cancel _ _ d _ _ (unit (succ v)*unit (succ v)) scalePos
    apply AggregateChain.point_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) ?_ ?_ total
    · have ev := natEq (AggregateChain.unit_succ (Γ := Γ) v)
      apply deriveNat
      ipra_simps
      rw [ev]
      ring
    · ipra_ring
  exact RationalPointDistance.bound_of_point_hit _ _ _ _ _
    (RationalPointDistance.pointHit_intro _ _ _ _ _ j' hj' nearby)

/-- Integer discreteness removes the auxiliary tail at an explicit index,
proving the exact source support-distance law for any finite observation. -/
theorem support_distance_bound (U S : PR 2) (p s d x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hU : Γ ⊢[PRAAx] pointRegular U d x) (hzero : Γ ⊢[PRAAx] supportZero U S d x) :
    Γ ⊢[PRAAx] le ((unit p*unit s)*
      RationalPointDistance.numerator (sample U p x) (sample S s x) d)
      ((unit p+unit s)*RationalPointDistance.denominator (sample U p x) (sample S s x) d) := by
  let V := two*unit p*unit s*RationalPointDistance.denominator (sample U p x) (sample S s x) d
  have finite := support_distance_tail U S p s V d x hS hR hU hzero
  apply GapRemoval.gap (C := V)
  exact le_congr (by unfold unit; ipra_ring) (by dsimp [V]; unfold unit; ipra_ring) finite

theorem support_nearby (U S : PR 2) (p s d x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hU : Γ ⊢[PRAAx] pointRegular U d x) (hzero : Γ ⊢[PRAAx] supportZero U S d x) :
    Γ ⊢[PRAAx] pointRadius (sample U p x)
      (entry (sample S s x) (RationalPointDistance.selected (sample U p x) (sample S s x) d))
      d (unit p+unit s) (unit p*unit s) :=
  RationalPointDistance.selected_radius _ _ _ _ _ (nonempty_at S s x hS)
    (support_distance_bound U S p s d x hS hR hU hzero)

def lowerNumerator (A B s p r : PTm n) : PTm n :=
  (A+B)*(two*unit p*unit r+unit s*unit r+unit p*unit s)

/-- Arbitrary supported point observations bound the actual finite minimum
name from below. Both the nearest index and its geometric bound are derived. -/
theorem support_value_lower (U S : PR 2) (f : PR 3) (s p r d A B x : PTm n)
    (hB : Γ ⊢[PRAAx] le one B)
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hmap : Γ ⊢[PRAAx] mapContract f d A B x)
    (hU : Γ ⊢[PRAAx] pointRegular U d x) (hzero : Γ ⊢[PRAAx] supportZero U S d x) :
    Γ ⊢[PRAAx] upper (minimumValue S f r x) (evaluate f (sample U p x) p x)
      (lowerNumerator A B s p r) (witnessDenominator B s p r) := by
  let j := RationalPointDistance.selected (sample U p x) (sample S s x) d
  have hj : Γ ⊢[PRAAx] lt j (length (sample S s x)) :=
    RationalPointDistance.selected_spec _ _ _ (nonempty_at S s x hS)
  have near := support_nearby U S p s d x hS hR hU hzero
  have reversed : Γ ⊢[PRAAx] pointRadius (entry (sample S s x) j) (sample U p x) d
      (unit s+unit p) (unit s*unit p) :=
    AggregateChain.point_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (add_comm _ _) (mul_comm _ _)
      (AggregateChain.point_symmetric _ _ d _ _ near)
  have mapping := map_regular_pair f (entry (sample S s x) j) (sample U p x) s p d A B x hmap reversed
  have first := upper_order_left (minimumValue S f s x) _ _ _ _
    (minimum_value_le S f s j x hj) (upper_of_radius _ _ _ _ mapping)
  have second := upper_of_radius _ _ _ _ (minima_cauchy S f r s d A B x hS hR hmap)
  have total := upper_triangle _ _ _ _ _ _ _ second first
  have pos : Γ ⊢[PRAAx] le one (B*unit s) :=
    le_congr (one_mul one) (.eqRefl _) (le_mul_mono hB (unit_positive s))
  exact upper_cancel _ _ _ _ (B*unit s) pos
    (upper_congr (.eqRefl _) (.eqRefl _) (by unfold lowerNumerator; ipra_ring)
      (by unfold witnessDenominator; ipra_ring) total)

theorem shift_lower_budget (a b A B k t l bshift c : PTm n)
    (hB : Γ ⊢[PRAAx] le one B)
    (hb : Γ ⊢[PRAAx] le (num 4*A+two*B) (B*unit bshift))
    (hc : Γ ⊢[PRAAx] le (A+B) (B*unit c))
    (h : Γ ⊢[PRAAx] upper a b (lowerNumerator A B (k+bshift) (t+c) (l+c))
      (witnessDenominator B (k+bshift) (t+c) (l+c))) :
    Γ ⊢[PRAAx] upper a b
      (unit t*unit l+unit k*unit l+unit k*unit t) (unit k*unit t*unit l) := by
  have pos : Γ ⊢[PRAAx] le one (witnessDenominator B (k+bshift) (t+c) (l+c)) :=
    le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono
      (le_mul_mono (le_mul_mono hB (unit_positive _)) (unit_positive _)) (unit_positive _))
  apply upper_mono _ _ _ _ _ _ pos h
  have hsmall : Γ ⊢[PRAAx] le (two*(A+B)) (B*unit bshift) :=
    le_trans (le_of_eq_add (d := two*A) (by ipra_ring)) hb
  have h1 := le_mul_mono hsmall (le_refl (unit (t+c)*unit (l+c)*unit k*unit t*unit l))
  have h2 := le_mul_mono hc (le_refl (unit (k+bshift)*unit (l+c)*unit k*unit t*unit l))
  have h3 := le_mul_mono hc (le_refl (unit (t+c)*unit (k+bshift)*unit k*unit t*unit l))
  have total := add_le_add₂ (add_le_add₂ h1 h2) h3
  have es := natEq (AggregateChain.unit_add (Γ := Γ) k bshift)
  have ep := natEq (AggregateChain.unit_add (Γ := Γ) t c)
  have er := natEq (AggregateChain.unit_add (Γ := Γ) l c)
  apply le_congr ?_ ?_ total
  · unfold lowerNumerator
    ipra_ring
  · unfold witnessDenominator
    apply deriveNat
    ipra_simps
    rw [es,ep,er]
    ring

def pointValue (U : PR 2) (f : PR 3) (t c x : PTm n) : PTm n :=
  evaluate f (sample U (t+c) x) (t+c) x

ipra_subst pointValue

theorem point_value_regular (U : PR 2) (f : PR 3) (t l c d A B x : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hc : Γ ⊢[PRAAx] le (A+B) (B*unit c))
    (hmap : Γ ⊢[PRAAx] mapContract f d A B x) (hU : Γ ⊢[PRAAx] pointRegular U d x) :
    Γ ⊢[PRAAx] radius (pointValue U f t c x) (pointValue U f l c x)
      (unit t+unit l) (unit t*unit l) :=
  shifted_regular_budget _ _ t l c A B hB hc
    (map_regular_pair f _ _ (t+c) (l+c) d A B x hmap
      (pointRegular_at U (t+c) (l+c) d x hU))

/-- The infimum lower-bound law, expressed entirely by arbitrarily accurate
finite observations of a supported point and the actual minimum-value name. -/
theorem support_lower_approximate (U S : PR 2) (f : PR 3) (k t l b c d A B x : PTm n)
    (hB : Γ ⊢[PRAAx] le one B)
    (hb : Γ ⊢[PRAAx] le (num 4*A+two*B) (B*unit b))
    (hc : Γ ⊢[PRAAx] le (A+B) (B*unit c))
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hmap : Γ ⊢[PRAAx] mapContract f d A B x)
    (hU : Γ ⊢[PRAAx] pointRegular U d x) (hzero : Γ ⊢[PRAAx] supportZero U S d x) :
    Γ ⊢[PRAAx] upper (valueName S f l c x) (pointValue U f t c x)
      (unit t*unit l+unit k*unit l+unit k*unit t) (unit k*unit t*unit l) :=
  shift_lower_budget _ _ A B k t l b c hB hb hc
    (support_value_lower U S f (k+b) (t+c) (l+c) d A B x hB hS hR hmap hU hzero)

theorem support_distance_closed (U S : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (nonempty S (var 3) ⟶ regular S (var 2) (var 3) ⟶
        pointRegular U (var 2) (var 3) ⟶ supportZero U S (var 2) (var 3) ⟶
        le ((unit (var 0)*unit (var 1))*RationalPointDistance.numerator
          (sample U (var 0) (var 3)) (sample S (var 1) (var 3)) (var 2))
          ((unit (var 0)+unit (var 1))*RationalPointDistance.denominator
            (sample U (var 0) (var 3)) (sample S (var 1) (var 3)) (var 2))) := by
  apply closeUniv 4
  refine .impI (.impI (.impI (.impI ?_)))
  exact support_distance_bound U S _ _ _ _ (.hyp (by simp)) (.hyp (by simp))
    (.hyp (by simp)) (.hyp (by simp))

theorem support_lower_closed (U S : PR 2) (f : PR 3) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
      (le one (var 7) ⟶ le (num 4*var 6+two*var 7) (var 7*unit (var 3)) ⟶
        le (var 6+var 7) (var 7*unit (var 4)) ⟶ nonempty S (var 8) ⟶
        regular S (var 5) (var 8) ⟶ mapContract f (var 5) (var 6) (var 7) (var 8) ⟶
        pointRegular U (var 5) (var 8) ⟶ supportZero U S (var 5) (var 8) ⟶
        upper (valueName S f (var 2) (var 4) (var 8))
          (pointValue U f (var 1) (var 4) (var 8))
          (unit (var 1)*unit (var 2)+unit (var 0)*unit (var 2)+unit (var 0)*unit (var 1))
          (unit (var 0)*unit (var 1)*unit (var 2))) := by
  apply closeUniv 9
  refine .impI (.impI (.impI (.impI (.impI (.impI (.impI (.impI ?_)))))))
  exact support_lower_approximate U S f (var 0) (var 1) (var 2) (var 3) (var 4)
    (var 5) (var 6) (var 7) (var 8)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp))
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp))

/-- A conservative actual arithmetic choice suffices; no unbounded search
or existence of a precision shift is a premise of the constructor. -/
def coarseValueShift (A B : PTm n) : PTm n := A+B
def coarseWitnessShift (A B : PTm n) : PTm n := num 4*A+two*B

theorem coarse_shift_bound (W B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] le W (B*unit W) :=
  le_trans (le_trans (le_succ_self W) (RationalClosure.succ_le_two_pow W))
    (le_congr (one_mul _) (.eqRefl _) (le_mul_mono hB (le_refl (unit W))))

theorem aggregate_optimization_coarse (S : PR 2) (f : PR 3) (d A B x : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hS : Γ ⊢[PRAAx] nonempty S x)
    (hR : Γ ⊢[PRAAx] regular S d x) (hmap : Γ ⊢[PRAAx] mapContract f d A B x) :
    Γ ⊢[PRAAx] optimizationResult S f (coarseWitnessShift A B) (coarseValueShift A B) d x :=
  aggregate_optimization S f _ _ d A B x hB (coarse_shift_bound _ B hB)
    (coarse_shift_bound _ B hB) hS hR hmap

theorem aggregate_optimization_coarse_closed (S : PR 2) (f : PR 3) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (le one (var 2) ⟶ nonempty S (var 3) ⟶ regular S (var 0) (var 3) ⟶
        mapContract f (var 0) (var 1) (var 2) (var 3) ⟶ optimizationResult S f
          (coarseWitnessShift (var 1) (var 2)) (coarseValueShift (var 1) (var 2)) (var 0) (var 3)) := by
  apply closeUniv 4
  refine .impI (.impI (.impI (.impI ?_)))
  exact aggregate_optimization_coarse S f (var 0) (var 1) (var 2) (var 3)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp))

theorem support_lower_coarse_closed (U S : PR 2) (f : PR 3) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (le one (var 5) ⟶ nonempty S (var 6) ⟶ regular S (var 3) (var 6) ⟶
        mapContract f (var 3) (var 4) (var 5) (var 6) ⟶ pointRegular U (var 3) (var 6) ⟶
        supportZero U S (var 3) (var 6) ⟶
        upper (valueName S f (var 2) (coarseValueShift (var 4) (var 5)) (var 6))
          (pointValue U f (var 1) (coarseValueShift (var 4) (var 5)) (var 6))
          (unit (var 1)*unit (var 2)+unit (var 0)*unit (var 2)+unit (var 0)*unit (var 1))
          (unit (var 0)*unit (var 1)*unit (var 2))) := by
  apply closeUniv 7
  refine .impI (.impI (.impI (.impI (.impI (.impI ?_)))))
  let Δ : List (Fm PTm 7) := [supportZero U S (var 3) (var 6), pointRegular U (var 3) (var 6),
    mapContract f (var 3) (var 4) (var 5) (var 6), regular S (var 3) (var 6),
    nonempty S (var 6), le one (var 5)]
  have hB : Δ ⊢[PRAAx] le one (var 5) := .hyp (by simp [Δ])
  exact support_lower_approximate U S f (var 0) (var 1) (var 2)
    (coarseWitnessShift (var 4) (var 5)) (coarseValueShift (var 4) (var 5))
    (var 3) (var 4) (var 5) (var 6) hB (coarse_shift_bound _ _ hB)
    (coarse_shift_bound _ _ hB) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp))
    (.hyp (by simp)) (.hyp (by simp))

theorem witness_name_length (S : PR 2) (f : PR 3) (k t b d x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) (hshape : Γ ⊢[PRAAx] AggregateChain.shaped S d x) :
    Γ ⊢[PRAAx] length (witnessName S f k t b d x) ≐ d :=
  AggregateChain.name_length S t (k+b) (minimumIndex S f (k+b) x) d x hS hshape
    (minimum_index_range S f (k+b) x hS)

theorem programs_closed (S : PR 2) (f : PR 3) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      ((ap2 (minimumF S f) (var 0) (var 5) ≐ minimumValue S f (var 0) (var 5)) ⋏
        ((ap3 (valueNameF S f) (var 0) (var 3) (var 5) ≐ valueName S f (var 0) (var 3) (var 5)) ⋏
          ((RationalHausdorff.apply5 (witnessNameF S f) (var 0) (var 1) (var 2) (var 4) (var 5) ≐
            witnessName S f (var 0) (var 1) (var 2) (var 4) (var 5)) ⋏
            (apply6 (witnessValueF S f) (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐
              witnessValue S f (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))))) :=
  closeUniv 6 (.andI (minimum_program_at S f _ _)
    (.andI (value_program_at S f _ _ _)
      (.andI (witness_program_at S f _ _ _ _ _) (witness_value_program_at S f _ _ _ _ _ _))))

/-- The source's supremum reduction is an actual evaluator, not an assumed
closure property of represented functions. -/
def negateEvaluator (f : PR 3) : PR 3 :=
  PTm.toPR (negate (evaluate f (var 0) (var 1) (var 2)))

theorem negate_evaluator_at (f : PR 3) (q p x : PTm n) :
    Γ ⊢[PRAAx] evaluate (negateEvaluator f) q p x ≐ negate (evaluate f q p x) := by
  have h := toPR_eq (Γ := Γ) (negate (evaluate f (var 0) (var 1) (var 2)) : PTm 3) ![q,p,x]
  change Γ ⊢[PRAAx] PTm.app (PTm.toPR (negate (evaluate f (var 0) (var 1) (var 2))))
    ![q,p,x] ≐ negate (evaluate f q p x)
  simpa [subst_negate, subst_evaluate] using h

theorem negate_map_contract (f : PR 3) (d A B x : PTm n)
    (hmap : Γ ⊢[PRAAx] mapContract f d A B x) :
    Γ ⊢[PRAAx] mapContract (negateEvaluator f) d A B x := by
  refine .allI (.impI ?_)
  let Δ := pointRadius (argument 0 (var 0)) (argument 1 (var 0)) (Syn.shift d)
    (argument 4 (var 0)) (argument 5 (var 0)) :: Γ.map Fm.shift
  have mapping : Δ ⊢[PRAAx] mapContract f (Syn.shift d) (Syn.shift A) (Syn.shift B) (Syn.shift x) := by
    simpa [Δ, Fm.shift, Syn.shift] using hmap.shift.wk
  have original := mapContract_at f (Syn.shift d) (Syn.shift A) (Syn.shift B) (Syn.shift x)
    (argument 0 (var 0)) (argument 1 (var 0)) (argument 2 (var 0)) (argument 3 (var 0))
    (argument 4 (var 0)) (argument 5 (var 0)) mapping Prf.hyp0
  exact radius_congr (negate_evaluator_at f _ _ _).eqSymm (negate_evaluator_at f _ _ _).eqSymm
    (.eqRefl _) (.eqRefl _) (radius_negate _ _ _ _ original)

def supremumName (S : PR 2) (f : PR 3) (k c x : PTm n) : PTm n :=
  negate (valueName S (negateEvaluator f) k c x)
def supremumWitnessValue (S : PR 2) (f : PR 3) (k t b c d x : PTm n) : PTm n :=
  evaluate f (witnessName S (negateEvaluator f) k (t+c) b d x) (t+c) x

ipra_subst supremumName
ipra_subst supremumWitnessValue

theorem supremum_name_regular (S : PR 2) (f : PR 3) (t l c d A B x : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hc : Γ ⊢[PRAAx] le (A+B) (B*unit c))
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hmap : Γ ⊢[PRAAx] mapContract f d A B x) :
    Γ ⊢[PRAAx] radius (supremumName S f t c x) (supremumName S f l c x)
      (unit t+unit l) (unit t*unit l) :=
  radius_negate _ _ _ _ (value_name_regular S (negateEvaluator f) t l c d A B x hB hc hS hR
    (negate_map_contract f d A B x hmap))

theorem supremum_witness_regular (S : PR 2) (f : PR 3) (k t u b c d A B x : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hc : Γ ⊢[PRAAx] le (A+B) (B*unit c))
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hmap : Γ ⊢[PRAAx] mapContract f d A B x) :
    Γ ⊢[PRAAx] radius (supremumWitnessValue S f k t b c d x)
      (supremumWitnessValue S f k u b c d x) (unit t+unit u) (unit t*unit u) :=
  shifted_regular_budget _ _ t u c A B hB hc
    (map_regular_pair f _ _ (t+c) (u+c) d A B x hmap
      (witness_name_regular S (negateEvaluator f) k (t+c) (u+c) b d x hS hR))

theorem supremum_witness_approximate (S : PR 2) (f : PR 3) (k t l b c d A B x : PTm n)
    (hB : Γ ⊢[PRAAx] le one B)
    (hb : Γ ⊢[PRAAx] le (num 4*A+two*B) (B*unit b))
    (hc : Γ ⊢[PRAAx] le (A+B) (B*unit c))
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hmap : Γ ⊢[PRAAx] mapContract f d A B x) :
    Γ ⊢[PRAAx] upper (supremumName S f l c x) (supremumWitnessValue S f k t b c d x)
      (unit t*unit l+unit k*unit l+unit k*unit t) (unit k*unit t*unit l) := by
  have original := witness_value_approximate S (negateEvaluator f) k t l b c d A B x
    hB hb hc hS hR (negate_map_contract f d A B x hmap)
  have swapped : Γ ⊢[PRAAx] upper (negate (supremumWitnessValue S f k t b c d x))
      (valueName S (negateEvaluator f) l c x)
      (unit t*unit l+unit k*unit l+unit k*unit t) (unit k*unit t*unit l) :=
    upper_congr (negate_evaluator_at f _ _ _) (.eqRefl _) (.eqRefl _) (.eqRefl _) original
  exact upper_negate_elim _ _ _ _ swapped

/-- Every represented supported value is below the supremum name, again
with all finite residual precision indices universally available. -/
theorem support_supremum_approximate (U S : PR 2) (f : PR 3) (k t l b c d A B x : PTm n)
    (hB : Γ ⊢[PRAAx] le one B)
    (hb : Γ ⊢[PRAAx] le (num 4*A+two*B) (B*unit b))
    (hc : Γ ⊢[PRAAx] le (A+B) (B*unit c))
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hmap : Γ ⊢[PRAAx] mapContract f d A B x)
    (hU : Γ ⊢[PRAAx] pointRegular U d x) (hzero : Γ ⊢[PRAAx] supportZero U S d x) :
    Γ ⊢[PRAAx] upper (pointValue U f t c x) (supremumName S f l c x)
      (unit t*unit l+unit k*unit l+unit k*unit t) (unit k*unit t*unit l) := by
  have original := support_lower_approximate U S (negateEvaluator f) k t l b c d A B x
    hB hb hc hS hR (negate_map_contract f d A B x hmap) hU hzero
  have swapped : Γ ⊢[PRAAx] upper (valueName S (negateEvaluator f) l c x)
      (negate (pointValue U f t c x))
      (unit t*unit l+unit k*unit l+unit k*unit t) (unit k*unit t*unit l) :=
    upper_congr (.eqRefl _) (negate_evaluator_at f _ _ _) (.eqRefl _) (.eqRefl _) original
  exact upper_unnegate_left _ _ _ _ (upper_negate _ _ _ _ swapped)

theorem supremum_optimization_closed (S : PR 2) (f : PR 3) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
      (le one (var 7) ⟶ le (num 4*var 6+two*var 7) (var 7*unit (var 3)) ⟶
        le (var 6+var 7) (var 7*unit (var 4)) ⟶ nonempty S (var 8) ⟶
        regular S (var 5) (var 8) ⟶ mapContract f (var 5) (var 6) (var 7) (var 8) ⟶
        (optimizationResult S (negateEvaluator f) (var 3) (var 4) (var 5) (var 8) ⋏
          (radius (supremumName S f (var 1) (var 4) (var 8))
            (supremumName S f (var 2) (var 4) (var 8))
            (unit (var 1)+unit (var 2)) (unit (var 1)*unit (var 2)) ⋏
            upper (supremumName S f (var 2) (var 4) (var 8))
              (supremumWitnessValue S f (var 0) (var 1) (var 3) (var 4) (var 5) (var 8))
              (unit (var 1)*unit (var 2)+unit (var 0)*unit (var 2)+unit (var 0)*unit (var 1))
              (unit (var 0)*unit (var 1)*unit (var 2))))) := by
  apply closeUniv 9
  refine .impI (.impI (.impI (.impI (.impI (.impI ?_)))))
  refine .andI (aggregate_optimization S (negateEvaluator f) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp))
    (negate_map_contract f _ _ _ _ Prf.hyp0)) ?_
  exact .andI (supremum_name_regular S f (var 1) (var 2) (var 4) (var 5) (var 6) (var 7) (var 8)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)))
    (supremum_witness_approximate S f (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)
      (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)))

theorem support_supremum_closed (U S : PR 2) (f : PR 3) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
      (le one (var 7) ⟶ le (num 4*var 6+two*var 7) (var 7*unit (var 3)) ⟶
        le (var 6+var 7) (var 7*unit (var 4)) ⟶ nonempty S (var 8) ⟶
        regular S (var 5) (var 8) ⟶ mapContract f (var 5) (var 6) (var 7) (var 8) ⟶
        pointRegular U (var 5) (var 8) ⟶ supportZero U S (var 5) (var 8) ⟶
        upper (pointValue U f (var 1) (var 4) (var 8))
          (supremumName S f (var 2) (var 4) (var 8))
          (unit (var 1)*unit (var 2)+unit (var 0)*unit (var 2)+unit (var 0)*unit (var 1))
          (unit (var 0)*unit (var 1)*unit (var 2))) := by
  apply closeUniv 9
  refine .impI (.impI (.impI (.impI (.impI (.impI (.impI (.impI ?_)))))))
  exact support_supremum_approximate U S f (var 0) (var 1) (var 2) (var 3) (var 4)
    (var 5) (var 6) (var 7) (var 8)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp))
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp))

theorem supremum_optimization_coarse_closed (S : PR 2) (f : PR 3) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (le one (var 5) ⟶ nonempty S (var 6) ⟶ regular S (var 3) (var 6) ⟶
        mapContract f (var 3) (var 4) (var 5) (var 6) ⟶
        (optimizationResult S (negateEvaluator f) (coarseWitnessShift (var 4) (var 5))
          (coarseValueShift (var 4) (var 5)) (var 3) (var 6) ⋏
          (radius (supremumName S f (var 1) (coarseValueShift (var 4) (var 5)) (var 6))
            (supremumName S f (var 2) (coarseValueShift (var 4) (var 5)) (var 6))
            (unit (var 1)+unit (var 2)) (unit (var 1)*unit (var 2)) ⋏
            upper (supremumName S f (var 2) (coarseValueShift (var 4) (var 5)) (var 6))
              (supremumWitnessValue S f (var 0) (var 1) (coarseWitnessShift (var 4) (var 5))
                (coarseValueShift (var 4) (var 5)) (var 3) (var 6))
              (unit (var 1)*unit (var 2)+unit (var 0)*unit (var 2)+unit (var 0)*unit (var 1))
              (unit (var 0)*unit (var 1)*unit (var 2))))) := by
  apply closeUniv 7
  refine .impI (.impI (.impI (.impI ?_)))
  let Δ : List (Fm PTm 7) := [mapContract f (var 3) (var 4) (var 5) (var 6),
    regular S (var 3) (var 6), nonempty S (var 6), le one (var 5)]
  have hB : Δ ⊢[PRAAx] le one (var 5) := .hyp (by simp [Δ])
  have hc := coarse_shift_bound (var 4+var 5) (var 5) hB
  have hb := coarse_shift_bound (num 4*var 4+two*var 5) (var 5) hB
  refine .andI (aggregate_optimization_coarse S (negateEvaluator f) (var 3) (var 4) (var 5) (var 6)
    hB (.hyp (by simp [Δ])) (.hyp (by simp [Δ])) (negate_map_contract f _ _ _ _ Prf.hyp0)) ?_
  exact .andI (supremum_name_regular S f (var 1) (var 2) _ (var 3) (var 4) (var 5) (var 6)
    hB hc (.hyp (by simp [Δ])) (.hyp (by simp [Δ])) Prf.hyp0)
    (supremum_witness_approximate S f (var 0) (var 1) (var 2) _ _ (var 3) (var 4) (var 5) (var 6)
      hB hb hc (.hyp (by simp [Δ])) (.hyp (by simp [Δ])) Prf.hyp0)

theorem support_supremum_coarse_closed (U S : PR 2) (f : PR 3) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (le one (var 5) ⟶ nonempty S (var 6) ⟶ regular S (var 3) (var 6) ⟶
        mapContract f (var 3) (var 4) (var 5) (var 6) ⟶ pointRegular U (var 3) (var 6) ⟶
        supportZero U S (var 3) (var 6) ⟶
        upper (pointValue U f (var 1) (coarseValueShift (var 4) (var 5)) (var 6))
          (supremumName S f (var 2) (coarseValueShift (var 4) (var 5)) (var 6))
          (unit (var 1)*unit (var 2)+unit (var 0)*unit (var 2)+unit (var 0)*unit (var 1))
          (unit (var 0)*unit (var 1)*unit (var 2))) := by
  apply closeUniv 7
  refine .impI (.impI (.impI (.impI (.impI (.impI ?_)))))
  let Δ : List (Fm PTm 7) := [supportZero U S (var 3) (var 6), pointRegular U (var 3) (var 6),
    mapContract f (var 3) (var 4) (var 5) (var 6), regular S (var 3) (var 6),
    nonempty S (var 6), le one (var 5)]
  have hB : Δ ⊢[PRAAx] le one (var 5) := .hyp (by simp [Δ])
  exact support_supremum_approximate U S f (var 0) (var 1) (var 2)
    (coarseWitnessShift (var 4) (var 5)) (coarseValueShift (var 4) (var 5))
    (var 3) (var 4) (var 5) (var 6) hB (coarse_shift_bound _ _ hB)
    (coarse_shift_bound _ _ hB) (.hyp (by simp [Δ])) (.hyp (by simp [Δ])) (.hyp (by simp [Δ]))
    (.hyp (by simp [Δ])) (.hyp (by simp [Δ]))

def supremumNameF (S : PR 2) (f : PR 3) : PR 3 :=
  PTm.toPR (supremumName S f (var 0) (var 1) (var 2))

theorem supremum_program_at (S : PR 2) (f : PR 3) (k c x : PTm n) :
    Γ ⊢[PRAAx] ap3 (supremumNameF S f) k c x ≐ supremumName S f k c x := by
  have h := toPR_eq (Γ := Γ) (supremumName S f (var 0) (var 1) (var 2) : PTm 3) ![k,c,x]
  simpa [supremumNameF, ap3] using h

theorem supremum_program_closed (S : PR 2) (f : PR 3) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (ap3 (supremumNameF S f) (var 0) (var 1) (var 2) ≐ supremumName S f (var 0) (var 1) (var 2)) :=
  closeUniv 3 (supremum_program_at S f _ _ _)

/-- Remove the freely available auxiliary optimization slack as well. This
is the literal represented lower-order law, not only its semantic limit. -/
theorem support_lower_exact (U S : PR 2) (f : PR 3) (t l c d A B x : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hc : Γ ⊢[PRAAx] le (A+B) (B*unit c))
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hmap : Γ ⊢[PRAAx] mapContract f d A B x)
    (hU : Γ ⊢[PRAAx] pointRegular U d x) (hzero : Γ ⊢[PRAAx] supportZero U S d x) :
    Γ ⊢[PRAAx] upper (valueName S f l c x) (pointValue U f t c x)
      (unit t+unit l) (unit t*unit l) := by
  let C := unit t*unit l*denominatorOf (valueName S f l c x)*denominatorOf (pointValue U f t c x)
  have finite := support_lower_approximate U S f C t l (coarseWitnessShift A B) c d A B x
    hB (coarse_shift_bound _ _ hB) hc hS hR hmap hU hzero
  unfold upper at finite ⊢
  apply GapRemoval.gap (C := C)
  exact le_congr (by unfold unit; ipra_ring) (by dsimp [C]; unfold unit; ipra_ring) finite

theorem support_supremum_exact (U S : PR 2) (f : PR 3) (t l c d A B x : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hc : Γ ⊢[PRAAx] le (A+B) (B*unit c))
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hmap : Γ ⊢[PRAAx] mapContract f d A B x)
    (hU : Γ ⊢[PRAAx] pointRegular U d x) (hzero : Γ ⊢[PRAAx] supportZero U S d x) :
    Γ ⊢[PRAAx] upper (pointValue U f t c x) (supremumName S f l c x)
      (unit t+unit l) (unit t*unit l) := by
  have original := support_lower_exact U S (negateEvaluator f) t l c d A B x
    hB hc hS hR (negate_map_contract f d A B x hmap) hU hzero
  have swapped : Γ ⊢[PRAAx] upper (valueName S (negateEvaluator f) l c x)
      (negate (pointValue U f t c x)) (unit t+unit l) (unit t*unit l) :=
    upper_congr (.eqRefl _) (negate_evaluator_at f _ _ _) (.eqRefl _) (.eqRefl _) original
  exact upper_unnegate_left _ _ _ _ (upper_negate _ _ _ _ swapped)

/-- Source `LeNamed` at zero slack: at every common observation
precision, `a_j ≤ b_j + 2e_j`. -/
def namedLower (U S : PR 2) (f : PR 3) (c x : PTm n) : Fm PTm n :=
  .all (upper (valueName S f (var 0) (Syn.shift c) (Syn.shift x))
    (pointValue U f (var 0) (Syn.shift c) (Syn.shift x)) two (unit (var 0)))
def namedUpper (U S : PR 2) (f : PR 3) (c x : PTm n) : Fm PTm n :=
  .all (upper (pointValue U f (var 0) (Syn.shift c) (Syn.shift x))
    (supremumName S f (var 0) (Syn.shift c) (Syn.shift x)) two (unit (var 0)))

theorem named_lower (U S : PR 2) (f : PR 3) (c d A B x : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hc : Γ ⊢[PRAAx] le (A+B) (B*unit c))
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hmap : Γ ⊢[PRAAx] mapContract f d A B x)
    (hU : Γ ⊢[PRAAx] pointRegular U d x) (hzero : Γ ⊢[PRAAx] supportZero U S d x) :
    Γ ⊢[PRAAx] namedLower U S f c x := by
  refine .allI ?_
  have bound := support_lower_exact U S f (var 0) (var 0) (Syn.shift c) (Syn.shift d)
    (Syn.shift A) (Syn.shift B) (Syn.shift x)
    (by simpa [Fm.shift, Syn.shift] using hB.shift)
    (by simpa [Fm.shift, Syn.shift] using hc.shift)
    (by simpa [Fm.shift, Syn.shift] using hS.shift)
    (by simpa [Fm.shift, Syn.shift] using hR.shift)
    (by simpa [Fm.shift, Syn.shift] using hmap.shift)
    (by simpa [Fm.shift, Syn.shift] using hU.shift)
    (by simpa [Fm.shift, Syn.shift] using hzero.shift)
  exact upper_cancel _ _ two _ (unit (var 0)) (unit_positive _)
    (upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) bound)

theorem named_upper (U S : PR 2) (f : PR 3) (c d A B x : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hc : Γ ⊢[PRAAx] le (A+B) (B*unit c))
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hmap : Γ ⊢[PRAAx] mapContract f d A B x)
    (hU : Γ ⊢[PRAAx] pointRegular U d x) (hzero : Γ ⊢[PRAAx] supportZero U S d x) :
    Γ ⊢[PRAAx] namedUpper U S f c x := by
  refine .allI ?_
  have bound := support_supremum_exact U S f (var 0) (var 0) (Syn.shift c) (Syn.shift d)
    (Syn.shift A) (Syn.shift B) (Syn.shift x)
    (by simpa [Fm.shift, Syn.shift] using hB.shift)
    (by simpa [Fm.shift, Syn.shift] using hc.shift)
    (by simpa [Fm.shift, Syn.shift] using hS.shift)
    (by simpa [Fm.shift, Syn.shift] using hR.shift)
    (by simpa [Fm.shift, Syn.shift] using hmap.shift)
    (by simpa [Fm.shift, Syn.shift] using hU.shift)
    (by simpa [Fm.shift, Syn.shift] using hzero.shift)
  exact upper_cancel _ _ two _ (unit (var 0)) (unit_positive _)
    (upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) bound)

theorem named_bounds_closed (U S : PR 2) (f : PR 3) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (le one (var 3) ⟶ le (var 2+var 3) (var 3*unit (var 0)) ⟶
        nonempty S (var 4) ⟶ regular S (var 1) (var 4) ⟶
        mapContract f (var 1) (var 2) (var 3) (var 4) ⟶
        pointRegular U (var 1) (var 4) ⟶ supportZero U S (var 1) (var 4) ⟶
        (namedLower U S f (var 0) (var 4) ⋏ namedUpper U S f (var 0) (var 4))) := by
  apply closeUniv 5
  refine .impI (.impI (.impI (.impI (.impI (.impI (.impI ?_))))))
  exact .andI (named_lower U S f (var 0) (var 1) (var 2) (var 3) (var 4)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp))
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)))
    (named_upper U S f (var 0) (var 1) (var 2) (var 3) (var 4)
      (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp))
      (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)))

end LeanProofs.IPRA.Analysis.AggregateOptimization
