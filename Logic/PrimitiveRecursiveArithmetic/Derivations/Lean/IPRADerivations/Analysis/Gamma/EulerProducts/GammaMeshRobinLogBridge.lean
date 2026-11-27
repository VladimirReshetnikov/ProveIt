import IPRADerivations.Analysis.Gamma.EulerProducts.GammaEulerConstantName
import IPRADerivations.Analysis.RationalArithmetic.Grids.RationalCubeMidpoint
import IPRADerivations.Analysis.RationalArithmetic.OrderBounds.GapRemoval
import IPRADerivations.Analysis.RationalArithmetic.Representations.RationalRepresentations
import IPRADerivations.AnalyticNumberTheory.RobinLipSum
import IPRADerivations.AnalyticNumberTheory.LogElementary

/-!
# The actual harmonic mesh and Robin logarithm at the same rational argument

The grid is (Q+j)/Q. The original Robin lower numerators and denominators
are used at every grid point. Their checked local inequalities telescope
against the actual factorial-cleared left and right rectangle sums.

For N,Q≥1 and every original truncation k, the resulting exact comparisons
are RobinLower(N,k)−(H_(QN)−H_Q)≤1/Q and
(H_(QN)−H_Q)−RobinLower(N,k)≤(N−1)/9^k. The actual PR2 programs
use Q=4·2^p and the explicit Robin truncation k=p+N+4. Their independently
queried samples are within 2^(−p)+2^(−q), and both programs satisfy the
ordinary scalar regular-name formula. The auxiliary precision used to
remove a vanishing error is computed only from the two endpoint codes.

The exact finite identity with the pre-existing fixed-N gamma program
is also proved: gammaMesh(p,N)+meshLog(p,N)=H_N. This identifies its
logarithm with the binary-range-reduced Robin interval construction;
identification with an unreduced artanh logarithm is a separate issue.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GammaMeshRobinLogBridge

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB quo_anti)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogInterval (loN loD loD_pos c3)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLipName (Rv)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le cancel_pos)
open Products (fact)
open GammaEulerMesh (factorial_quotient factorial_positive)
open GammaEulerConstantName (unit mesh unit_positive mesh_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def gridNumerator (Q k i : PTm n) : PTm n := loN (Q+i) Q k
def gridDenominator (Q k i : PTm n) : PTm n := loD (Q+i) Q k
def gain (k : PTm n) : PTm n := Rv k c3
def leftSum (Q i F : PTm n) : PTm n := ap2 (sumF (offB hB)) i (pairT (pred Q) F)
def rightSum (Q i F : PTm n) : PTm n := ap2 (sumF (offB hB)) i (pairT Q F)

ipra_subst gridNumerator [loN]
ipra_subst gridDenominator [loD]
ipra_subst gain [Rv, c3]
ipra_subst leftSum
ipra_subst rightSum

theorem grid_denominator_positive (Q k i : PTm n) (hQ : Γ ⊢[PRAAx] le one Q) :
    Γ ⊢[PRAAx] le one (gridDenominator Q k i) :=
  le_congr (.eqRefl _) (loD_pos hQ (le_add_right Q i) k).eqSymm (zero_lt_succ _)

theorem left_zero (Q F : PTm n) : Γ ⊢[PRAAx] leftSum Q zero F ≐ zero := sum_zero _ _
theorem right_zero (Q F : PTm n) : Γ ⊢[PRAAx] rightSum Q zero F ≐ zero := sum_zero _ _

theorem left_succ (Q i F : PTm n) (hQ : Γ ⊢[PRAAx] le one Q) :
    Γ ⊢[PRAAx] leftSum Q (succ i) F ≐ leftSum Q i F+quo F (Q+i) := by
  have e := (sum_succ' (Γ := Γ) (offB hB) i (pairT (pred Q) F)).eqTrans
    (congrAdd (.eqRefl _) (LeanProofs.IPRA.AnalyticNumberTheory.LogElementary.off_at i (pred Q) F))
  exact e.eqTrans (congrAdd (.eqRefl _) (congrAp2 quoF (.eqRefl _) (by
    ipra_lc -natEq (pos_of_one_le hQ))))

theorem right_succ (Q i F : PTm n) :
    Γ ⊢[PRAAx] rightSum Q (succ i) F ≐ rightSum Q i F+quo F (Q+succ i) :=
  (sum_succ' (offB hB) i (pairT Q F)).eqTrans
    (congrAdd (.eqRefl _) ((LeanProofs.IPRA.AnalyticNumberTheory.LogElementary.off_at i Q F).eqTrans
      (congrAp2 quoF (.eqRefl _) (add_succ Q i).eqSymm)))

/-- The actual neighboring Robin codes, on an exact factorial scale. -/
theorem grid_step (Q k i L : PTm n) (hQ : Γ ⊢[PRAAx] le one Q)
    (hi : Γ ⊢[PRAAx] le (Q+succ i) L) : Γ ⊢[PRAAx]
    le (fact L*gridNumerator Q k (succ i)*gridDenominator Q k i)
      (fact L*gridNumerator Q k i*gridDenominator Q k (succ i)+
        quo (fact L) (Q+i)*gridDenominator Q k i*gridDenominator Q k (succ i)) ⋏
    le (fact L*gain k*gridNumerator Q k i*gridDenominator Q k (succ i)+
        gain k*quo (fact L) (Q+succ i)*gridDenominator Q k i*gridDenominator Q k (succ i))
      (fact L*gain k*gridNumerator Q k (succ i)*gridDenominator Q k i+
        quo (fact L) (Q+i)*gridDenominator Q k i*gridDenominator Q k (succ i)) := by
  let a := Q+i
  let b := Q+succ i
  let n := gridNumerator Q k i
  let d := gridDenominator Q k i
  let n' := gridNumerator Q k (succ i)
  let d' := gridDenominator Q k (succ i)
  have ha : Γ ⊢[PRAAx] le one a := le_trans hQ (le_add_right _ _)
  have hb : Γ ⊢[PRAAx] le one b := le_trans hQ (le_add_right _ _)
  have eD : Γ ⊢[PRAAx] b*Q ≐ a*Q+Q := by dsimp only [a,b]; ipra_ring
  have h2 : Γ ⊢[PRAAx] le (b*Q) (two*(a*Q)) := by
    dsimp only [a,b]
    ipra_le 𝔞 Q*sl hQ+𝔞 Q*𝔞 i
  have up := LeanProofs.IPRA.AnalyticNumberTheory.RobinLipLog.lo_lip_up hQ (le_add_right Q i) hQ
    (le_add_right Q (succ i)) eD h2 k
  have low := LeanProofs.IPRA.AnalyticNumberTheory.RobinLipLog.lo_lip_low hQ (le_add_right Q i) hQ
    (le_add_right Q (succ i)) eD h2 k
  have u : Γ ⊢[PRAAx] le (a*n'*d) (a*n*d'+d*d') := by
    apply cancel_pos hQ
    exact le_congr (by dsimp only [a,n',d,gridNumerator,gridDenominator]; ipra_ring)
      (by dsimp only [a,n,d,d',gridNumerator,gridDenominator]; ipra_ring) up
  have v : Γ ⊢[PRAAx] le (a*b*gain k*n*d'+a*gain k*d*d') (a*b*gain k*n'*d+b*d*d') := by
    apply cancel_pos (RationalAlgebra.positive_product hQ hQ)
    exact le_congr (by dsimp only [a,b,n,d,d',gridNumerator,gridDenominator,gain]; ipra_ring)
      (by dsimp only [a,b,n',d,d',gridNumerator,gridDenominator,gain]; ipra_ring) low
  have ea := natEq (factorial_quotient a L ha (le_trans (add_le_add₂ (le_refl Q) (le_succ_self i)) hi))
  have eb := natEq (factorial_quotient b L hb hi)
  refine .andI ?_ ?_
  · ipra_le 𝔞 (quo (fact L) a)*sl u using linear_combination (𝔞 n'*𝔞 d-𝔞 n*𝔞 d')*ea
  · apply cancel_pos (RationalAlgebra.positive_product ha hb)
    ipra_le 𝔞 (fact L)*sl v using linear_combination 𝔞 b*𝔞 d*𝔞 d'*ea-𝔞 a*𝔞 (gain k)*𝔞 d*𝔞 d'*eb

def prefixBounds (Q k L i : PTm n) : Fm PTm n :=
  le (fact L*gridNumerator Q k i) (leftSum Q i (fact L)*gridDenominator Q k i) ⋏
    le (gain k*rightSum Q i (fact L)*gridDenominator Q k i)
      (fact L*gain k*gridNumerator Q k i+leftSum Q i (fact L)*gridDenominator Q k i)

ipra_subst prefixBounds

theorem prefix_zero (Q k L : PTm n) (hQ : Γ ⊢[PRAAx] le one Q) : Γ ⊢[PRAAx] prefixBounds Q k L zero := by
  have z : Γ ⊢[PRAAx] gridNumerator Q k zero ≐ zero :=
    LeanProofs.IPRA.AnalyticNumberTheory.RobinLipSum.lo_zero_at hQ (add_zero Q) k
  have a := natEq z
  have b := natEq (left_zero (Γ := Γ) Q (fact L))
  have c := natEq (right_zero (Γ := Γ) Q (fact L))
  refine .andI ?_ ?_
  · ipra_le 0 using linear_combination 𝔞 (gridDenominator Q k zero)*b-𝔞 (fact L)*a
  · ipra_le 0 using linear_combination 𝔞 (fact L)*𝔞 (gain k)*a+𝔞 (gridDenominator Q k zero)*b-𝔞 (gain k)*𝔞 (gridDenominator Q k zero)*c

theorem prefix_step (Q k L T i : PTm n) (hQ : Γ ⊢[PRAAx] le one Q)
    (hT : Γ ⊢[PRAAx] le (Q+T) L) (hi : Γ ⊢[PRAAx] le (succ i) T)
    (ih : Γ ⊢[PRAAx] prefixBounds Q k L i) : Γ ⊢[PRAAx] prefixBounds Q k L (succ i) := by
  have step := grid_step Q k i L hQ (le_trans (add_le_add₂ (le_refl Q) hi) hT)
  have a := natEq (left_succ Q i (fact L) hQ)
  have b := natEq (right_succ (Γ := Γ) Q i (fact L))
  refine .andI ?_ ?_
  · apply cancel_pos (grid_denominator_positive Q k i hQ)
    ipra_le 𝔞 (gridDenominator Q k (succ i))*sl ih.andE₁+sl step.andE₁ using linear_combination 𝔞 (gridDenominator Q k i)*𝔞 (gridDenominator Q k (succ i))*a
  · apply cancel_pos (grid_denominator_positive Q k i hQ)
    ipra_le 𝔞 (gridDenominator Q k (succ i))*sl ih.andE₂+sl step.andE₂ using linear_combination 𝔞 (gridDenominator Q k i)*𝔞 (gridDenominator Q k (succ i))*a-𝔞 (gain k)*𝔞 (gridDenominator Q k i)*𝔞 (gridDenominator Q k (succ i))*b

/-- The genuine finite grid telescope, retaining both actual rectangle sums. -/
theorem grid_telescope (Q k L T : PTm n) (hQ : Γ ⊢[PRAAx] le one Q)
    (hT : Γ ⊢[PRAAx] le (Q+T) L) : Γ ⊢[PRAAx] prefixBounds Q k L T := by
  have q : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift Q) := by simpa [Fm.shift,Syn.shift] using hQ.shift
  have t : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift Q+Syn.shift T) (Syn.shift L) := by
    simpa [Fm.shift,Syn.shift] using hT.shift
  have all : Γ ⊢[PRAAx] .all (le (var 0) (Syn.shift T) ⟶
      prefixBounds (Syn.shift Q) (Syn.shift k) (Syn.shift L) (var 0)) := by
    ipra_qfind (by unfold prefixBounds; exact ⟨le_QF _ _,⟨le_QF _ _,le_QF _ _⟩⟩) [subst_le, subst_prefixBounds]
    · exact .impI (prefix_zero Q k L hQ.wk)
    · exact .impI (prefix_step _ _ _ _ _ q.wk.wk t.wk.wk Prf.hyp0
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)))
  have h : Γ ⊢[PRAAx] le T T ⟶ prefixBounds Q k L T := by
    simpa only [Fm.subst_imp,subst_le,subst_prefixBounds,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE T
  exact .impE h (le_refl _)

def rectangleBalance (Q i F : PTm n) : Fm PTm n :=
  rightSum Q i F+quo F Q ≐ leftSum Q i F+quo F (Q+i)

ipra_subst rectangleBalance

theorem rectangle_balance (Q i F : PTm n) (hQ : Γ ⊢[PRAAx] le one Q) :
    Γ ⊢[PRAAx] rectangleBalance Q i F := by
  have q : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift Q) := by simpa [Fm.shift,Syn.shift] using hQ.shift
  have all : Γ ⊢[PRAAx] .all (rectangleBalance (Syn.shift Q) (var 0) (Syn.shift F)) := by
    ipra_qfind [subst_rectangleBalance]
    · have c := natEq (congrAp2 quoF (.eqRefl F) (add_zero (Γ := Γ) Q))
      apply deriveNat; ipra_simps
      linear_combination natEq (right_zero (Γ := Γ) Q F)-natEq (left_zero (Γ := Γ) Q F)-c
    · have a := natEq (left_succ (Γ := rectangleBalance (Syn.shift Q) (var 0) (Syn.shift F) :: Γ.map Fm.shift)
        (Syn.shift Q) (var 0) (Syn.shift F) q.wk)
      have b := natEq (right_succ (Γ := rectangleBalance (Syn.shift Q) (var 0) (Syn.shift F) :: Γ.map Fm.shift)
        (Syn.shift Q) (var 0) (Syn.shift F))
      have c := natEq (Prf.hyp0 : (rectangleBalance (Syn.shift Q) (var 0) (Syn.shift F) :: Γ.map Fm.shift) ⊢[PRAAx] _)
      apply deriveNat; ipra_simps
      linear_combination c+b-a
  simpa only [subst_rectangleBalance,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE i

theorem left_sum_bound (Q T F : PTm n) (hQ : Γ ⊢[PRAAx] le one Q) :
    Γ ⊢[PRAAx] le (leftSum Q T F) (T*quo F Q) := by
  have q : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift Q) := by simpa [Fm.shift,Syn.shift] using hQ.shift
  apply LeanProofs.IPRA.Foundations.AuxiliaryEnvelope.sum_le_const
  refine .allI (.impI ?_)
  simp only [Syn.shift,subst_pairT,PTm.subst_pred,subst_ap2] at ⊢
  have h := LeanProofs.IPRA.AnalyticNumberTheory.LogElementary.off_at (Γ := lt (var 0) (Syn.shift T) :: Γ.map Fm.shift)
    (var 0) (pred (Syn.shift Q)) (Syn.shift F)
  apply le_congr h.eqSymm (.eqRefl _)
  apply quo_anti (pos_of_one_le q.wk)
  have p := natEq (pos_of_one_le (Γ := lt (var 0) (Syn.shift T) :: Γ.map Fm.shift) q.wk)
  ipra_le 𝔞 (var 0) using linear_combination -p

def count (N Q : PTm n) : PTm n := Q*pred N
theorem grid_endpoint (N Q : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] Q+count N Q ≐ Q*N := by
  have e := natEq (pos_of_one_le hN)
  apply deriveNat; unfold count; ipra_simps
  linear_combination -𝔞 Q*e

theorem terminal_left_bound (N Q : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hQ : Γ ⊢[PRAAx] le one Q) : Γ ⊢[PRAAx]
    le (leftSum Q (count N Q) (fact (Q*N))) (pred N*fact (Q*N)) := by
  have q := natEq (factorial_quotient Q (Q*N) hQ (by ipra_le 𝔞 Q*sl hN))
  exact le_congr (.eqRefl _) (by
    apply deriveNat; unfold count; ipra_simps
    linear_combination 𝔞 (pred N)*q) (left_sum_bound Q (count N Q) (fact (Q*N)) hQ)

def harmonicNumerator (N Q : PTm n) : ZT n := ⟨S (Q*N) (fact (Q*N)),S Q (fact (Q*N))⟩
def harmonicLog (N Q : PTm n) : PTm n := RationalIntegerNormalization.normalize (harmonicNumerator N Q) (fact (Q*N))
def gridValue (Q k i : PTm n) : PTm n := RationalCubeMidpoint.fraction (gridNumerator Q k i) (gridDenominator Q k i)
def robinValue (N k : PTm n) : PTm n := RationalCubeMidpoint.fraction (loN N one k) (loD N one k)

theorem robin_denominator_positive (N k : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] le one (loD N one k) :=
  le_congr (.eqRefl _) (loD_pos (le_refl one) hN k).eqSymm (zero_lt_succ _)

theorem terminal_grid_value (N Q k : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hQ : Γ ⊢[PRAAx] le one Q) : Γ ⊢[PRAAx] gridValue Q k (count N Q) ≐ robinValue N k := by
  have endp := grid_endpoint N Q hN
  have val : Γ ⊢[PRAAx] gridNumerator Q k (count N Q)*loD N one k ≐
      loN N one k*gridDenominator Q k (count N Q) :=
    LeanProofs.IPRA.AnalyticNumberTheory.RobinLipSum.lo_val hQ (le_add_right _ _) (le_refl one) hN
      ((congrMul endp (.eqRefl one)).eqTrans (by ipra_ring)) k
  have a := grid_denominator_positive Q k (count N Q) hQ
  have b := robin_denominator_positive N k hN
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalNormalForm.normalize_well_formed _ _ a)
    (RationalNormalForm.normalize_well_formed _ _ b) (RationalCubeMidpoint.fraction_represents _ _ a)
    (RationalCubeMidpoint.fraction_represents _ _ b) a b
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  simpa only [IPRA.Q.mk_mul,map_mul] using natEq val

theorem harmonic_value (N Q : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (harmonicLog N Q) (ZT.ofNat (rightSum Q (count N Q) (fact (Q*N)))) (fact (Q*N)) := by
  have e : Γ ⊢[PRAAx] S (Q*N) (fact (Q*N)) ≐ S Q (fact (Q*N))+rightSum Q (count N Q) (fact (Q*N)) :=
    (congrAp2 (sumF hB) (grid_endpoint N Q hN).eqSymm (.eqRefl _)).eqTrans (sum_split hB Q (count N Q) (fact (Q*N)))
  apply GaussianRationalHorner.scalar_congr (.eqRefl _) ?_ (.eqRefl _)
    (RationalIntegerNormalization.normalize_preserves_value (harmonicNumerator N Q) _ (factorial_positive _))
  apply ZT.derive
  have p := natEq e
  simp only [ZT.toZ_ofNat]
  simp only [harmonicNumerator,ZT.toZ]
  ipra_simps
  linear_combination p

/-- The exact original finite mesh and Robin codes have quantitatively shrinking discrepancy. -/
theorem finite_bridge (N Q k : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hQ : Γ ⊢[PRAAx] le one Q) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (robinValue N k) (harmonicLog N Q) one Q ⋏
      RationalValueBounds.upper (harmonicLog N Q) (robinValue N k) (pred N) (gain k) := by
  let L := Q*N
  let T := count N Q
  let F := fact L
  let r := rightSum Q T F
  let l := leftSum Q T F
  let a := gridNumerator Q k T
  let d := gridDenominator Q k T
  have hp : Γ ⊢[PRAAx] prefixBounds Q k L T := grid_telescope Q k L T hQ
    (le_congr (grid_endpoint N Q hN).eqSymm (.eqRefl _) (le_refl _))
  have balance : Γ ⊢[PRAAx] le l (r+quo F Q) := le_of_eq_add (rectangle_balance Q T F hQ)
  have q := natEq (factorial_quotient Q L hQ (by dsimp only [L]; ipra_le 𝔞 Q*sl hN))
  have first : Γ ⊢[PRAAx] le (Q*F*a) (Q*r*d+F*d) := by
    ipra_le 𝔞 Q*sl hp.andE₁+𝔞 Q*𝔞 d*sl balance using linear_combination -𝔞 d*q
  have second : Γ ⊢[PRAAx] le (gain k*r*d) (F*gain k*a+pred N*F*d) := by
    ipra_le sl hp.andE₂+𝔞 d*sl (terminal_left_bound N Q hN hQ)
  have pd := grid_denominator_positive Q k T hQ
  have pf := factorial_positive (Γ := Γ) L
  have gv := RationalCubeMidpoint.fraction_represents (gridNumerator Q k T) (gridDenominator Q k T) pd
  have hv := harmonic_value N Q hN
  have firstBound : Γ ⊢[PRAAx] RationalValueBounds.upper (gridValue Q k T) (harmonicLog N Q) one Q := by
    apply RationalCubeInfimumIntervals.upper_of_representations _ _ _ _ _ _ _ _ pd pf gv hv
    apply zle_of_toZ (monus (Q*r*d+F*d) (Q*F*a))
    have e := natEq (eq_add_of_le first)
    simp only [ZT.toZ_mul,ZT.toZ_sub,ZT.toZ_ofNat]
    ipra_simps
    linear_combination -e
  have secondBound : Γ ⊢[PRAAx] RationalValueBounds.upper (harmonicLog N Q) (gridValue Q k T) (pred N) (gain k) := by
    apply RationalCubeInfimumIntervals.upper_of_representations _ _ _ _ _ _ _ _ pf pd hv gv
    apply zle_of_toZ (monus (F*gain k*a+pred N*F*d) (gain k*r*d))
    have e := natEq (eq_add_of_le second)
    simp only [ZT.toZ_mul,ZT.toZ_sub,ZT.toZ_ofNat]
    ipra_simps
    linear_combination -e
  have e := terminal_grid_value N Q k hN hQ
  exact .andI (RationalValueBounds.upper_congr e (.eqRefl _) (.eqRefl _) (.eqRefl _) firstBound)
    (RationalValueBounds.upper_congr (.eqRefl _) e (.eqRefl _) (.eqRefl _) secondBound)

def robinClock (N p : PTm n) : PTm n := p+N+LeanProofs.IPRA.PTm.num 4

ipra_subst harmonicNumerator [ZT.subst, S]
ipra_subst harmonicLog
ipra_subst robinValue [loN, loD]
ipra_subst robinClock

theorem binary_gain (k : PTm n) : Γ ⊢[PRAAx] le (unit k) (gain k) := by
  have h := le_trans (Γ := Γ)
    (GaussianFactorBudget.power_monotone_length two k (two*k) (le_succ_self one)
      (le_of_eq_add (d := k) (by ipra_ring)))
    (pw_le_pw (two*k) (le_succ_self two))
  simpa only [unit,gain,Rv,c3] using h

theorem gain_positive (k : PTm n) : Γ ⊢[PRAAx] le one (gain k) := le_trans (unit_positive k) (binary_gain k)

theorem clock_error_budget (N p : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] le (pred N*unit p) (gain (robinClock N p)) := by
  have hp : Γ ⊢[PRAAx] le (pred N) (pw two N) := le_trans
    (le_congr (.eqRefl _) (pos_of_one_le hN).eqSymm (le_succ_self (pred N)))
    (le_of_lt (LeanProofs.IPRA.AnalyticNumberTheory.Valuation.lt_pw (le_refl two) N))
  have small : Γ ⊢[PRAAx] le (pred N*unit p) (unit (N+p)) :=
    le_congr (.eqRefl _) (pw_add two N p).eqSymm (le_mul_mono hp (le_refl (unit p)))
  have grow := GaussianFactorBudget.power_monotone_length (Γ := Γ) two (N+p) (robinClock N p) (le_succ_self one)
    (by unfold robinClock; ipra_le 4)
  exact le_trans small (le_trans grow (binary_gain _))

theorem clocked_values (N p q : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (harmonicLog N (mesh p)) (robinValue N (robinClock N q))
      (unit p+unit q) (unit p*unit q) := by
  have h := finite_bridge N (mesh p) (robinClock N q) hN (mesh_positive p)
  have lower := RationalValueBounds.upper_mono _ _ _ _ one (unit q) (gain_positive _) h.andE₂
    (le_congr (.eqRefl _) (by ipra_ring) (clock_error_budget N q hN))
  apply RationalValueBounds.radius_of_upper _ _ _ _
  · exact RationalValueBounds.upper_mono _ _ _ _ _ _ (unit_positive q) lower
      (le_of_eq_add (d := unit q*unit q) (by ipra_ring))
  · exact RationalValueBounds.upper_mono _ _ _ _ _ _ (mesh_positive p) h.andE₁
      (le_of_eq_add (d := LeanProofs.IPRA.PTm.num 4*unit p*unit p+LeanProofs.IPRA.PTm.num 3*unit p*unit q)
        (by unfold mesh; ipra_ring))

def meshLogF : PR 2 := PTm.toPR (harmonicLog (var 1) (mesh (var 0)) : PTm 2)
def robinLogF : PR 2 := PTm.toPR (robinValue (var 1) (robinClock (var 1) (var 0)) : PTm 2)
def meshLogSample (p N : PTm n) : PTm n := ap2 meshLogF p N
def robinLogSample (p N : PTm n) : PTm n := ap2 robinLogF p N

ipra_subst meshLogSample
ipra_subst robinLogSample

theorem mesh_log_at (p N : PTm n) : Γ ⊢[PRAAx] meshLogSample p N ≐ harmonicLog N (mesh p) := by
  simpa [meshLogSample,meshLogF,ap2] using toPR_eq (Γ := Γ) (harmonicLog (var 1) (mesh (var 0)) : PTm 2) ![p,N]
theorem robin_log_at (p N : PTm n) : Γ ⊢[PRAAx] robinLogSample p N ≐ robinValue N (robinClock N p) := by
  simpa [robinLogSample,robinLogF,ap2] using toPR_eq (Γ := Γ) (robinValue (var 1) (robinClock (var 1) (var 0)) : PTm 2) ![p,N]

theorem cross_compatibility (N p q : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (meshLogSample p N) (robinLogSample q N) (unit p+unit q) (unit p*unit q) :=
  RationalValueBounds.radius_congr (mesh_log_at p N).eqSymm (robin_log_at q N).eqSymm (.eqRefl _) (.eqRefl _) (clocked_values N p q hN)

/-- The auxiliary precision depends only on the two endpoints, not on its own sample. -/
def gapClock (a b s t : PTm n) : PTm n :=
  two*(unit s*unit t)*RationalSupMetric.denominatorOf a*RationalSupMetric.denominatorOf b

theorem remove_cross_error (a b s t : PTm n)
    (h : Γ ⊢[PRAAx] RationalValueBounds.radius a b
      ((unit s+unit t)*unit (gapClock a b s t)+two*unit s*unit t)
      ((unit s*unit t)*unit (gapClock a b s t))) :
    Γ ⊢[PRAAx] RationalValueBounds.radius a b (unit s+unit t) (unit s*unit t) := by
  unfold RationalValueBounds.radius
  apply GapRemoval.gap (C := gapClock a b s t)
  exact le_congr (by simp only [unit]; ipra_ring) (by simp only [unit,gapClock]; ipra_ring) h

theorem join_cross_errors (a b c s t k : PTm n)
    (h₁ : Γ ⊢[PRAAx] RationalValueBounds.radius a c (unit s+unit k) (unit s*unit k))
    (h₂ : Γ ⊢[PRAAx] RationalValueBounds.radius c b (unit t+unit k) (unit t*unit k)) :
    Γ ⊢[PRAAx] RationalValueBounds.radius a b
      ((unit s+unit t)*unit k+two*unit s*unit t) ((unit s*unit t)*unit k) := by
  apply RationalValueBounds.radius_cancel _ _ _ _ (unit k) (unit_positive k)
  exact RationalValueBounds.radius_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (RationalValueBounds.radius_triangle _ _ _ _ _ _ _ h₁ h₂)

theorem mesh_samples_regularity (s t N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (meshLogSample s N) (meshLogSample t N)
      (unit s+unit t) (unit s*unit t) := by
  let k := gapClock (meshLogSample s N) (meshLogSample t N) s t
  apply remove_cross_error
  exact join_cross_errors _ _ (robinLogSample k N) s t k
    (cross_compatibility N s k hN)
    (RationalValueBounds.radius_symmetric _ _ _ _ (cross_compatibility N t k hN))

theorem robin_samples_regularity (s t N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (robinLogSample s N) (robinLogSample t N)
      (unit s+unit t) (unit s*unit t) := by
  let k := gapClock (robinLogSample s N) (robinLogSample t N) s t
  apply remove_cross_error
  exact join_cross_errors _ _ (meshLogSample k N) s t k
    (RationalValueBounds.radius_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring)
      (RationalValueBounds.radius_symmetric _ _ _ _ (cross_compatibility N k s hN)))
    (RationalValueBounds.radius_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring)
      (cross_compatibility N k t hN))

theorem mesh_name_regular (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] RationalCubeInfimumName.regular meshLogF N := by
  refine .allI (.allI ?_)
  have h : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (Syn.shift (Syn.shift N)) := by
    simpa [Fm.shift,Syn.shift] using hN.shift.shift
  simpa only [RationalCubeInfimumName.regular,RationalCubeGrid.scale,unit,meshLogSample,Syn.shift] using
    mesh_samples_regularity (var 1) (var 0) (Syn.shift (Syn.shift N)) h

theorem robin_name_regular (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] RationalCubeInfimumName.regular robinLogF N := by
  refine .allI (.allI ?_)
  have h : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (Syn.shift (Syn.shift N)) := by
    simpa [Fm.shift,Syn.shift] using hN.shift.shift
  simpa only [RationalCubeInfimumName.regular,RationalCubeGrid.scale,unit,robinLogSample,Syn.shift] using
    robin_samples_regularity (var 1) (var 0) (Syn.shift (Syn.shift N)) h

theorem mesh_sample_canonical (p N : PTm n) :
    Γ ⊢[PRAAx] RationalNormalForm.wellFormed (meshLogSample p N) :=
  RationalCubeMinimum.well_formed_congr (mesh_log_at p N).eqSymm
    (RationalNormalForm.normalize_well_formed _ _ (factorial_positive _))

theorem robin_sample_canonical (p N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] RationalNormalForm.wellFormed (robinLogSample p N) :=
  RationalCubeMinimum.well_formed_congr (robin_log_at p N).eqSymm
    (RationalNormalForm.normalize_well_formed _ _ (robin_denominator_positive N _ hN))

def harmonicValue (N : PTm n) : PTm n := RationalCubeMidpoint.fraction (S N (fact N)) (fact N)
ipra_subst harmonicValue [S]

/-- Exact finite identity: the pre-existing gamma mesh and this logarithm sum to H_N. -/
theorem fixed_mesh_sum (N Q : PTm n) (_hN : Γ ⊢[PRAAx] le one N)
    (hQ : Γ ⊢[PRAAx] le one Q) : Γ ⊢[PRAAx]
    RationalArithmetic.add (GammaEulerMesh.sample N Q) (harmonicLog N Q) ≐ harmonicValue N := by
  have e := natEq (LeanProofs.IPRA.AnalyticNumberTheory.MeshChange.S_denom (le_refl N)
    (show Γ ⊢[PRAAx] le N (Q*N) by ipra_le 𝔞 N*sl hQ))
  have a := GammaEulerMesh.common_value (Γ := Γ) N Q (Q*N)
  have b := RationalIntegerNormalization.normalize_preserves_value (Γ := Γ) (harmonicNumerator N Q)
    (fact (Q*N)) (factorial_positive _)
  have sum := RationalRepresentations.represents_add _ _ _ _ _ _ a b
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.add_guard _ _)
    (RationalNormalForm.normalize_well_formed _ _ (factorial_positive N)) sum
    (RationalCubeMidpoint.fraction_represents _ _ (factorial_positive N))
    (RationalAlgebra.positive_product (factorial_positive _) (factorial_positive _)) (factorial_positive N)
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat]
  simp only [GammaEulerMesh.numerator,harmonicNumerator,ZT.toZ]
  ipra_simps
  linear_combination 𝔞 (fact (Q*N))*e

theorem fixed_log_samples_sum (p N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    RationalArithmetic.add (GammaEulerConstantName.fixedSample p N) (meshLogSample p N) ≐ harmonicValue N := by
  have e := Prf.eqCongr (Γ := Γ) (RationalArithmetic.add (var 0) (var 1) : PTm 2)
    (σ := ![GammaEulerConstantName.fixedSample p N,meshLogSample p N])
    (σ' := ![GammaEulerMesh.sample N (mesh p),harmonicLog N (mesh p)])
    (fun i => by fin_cases i; exact GammaEulerConstantName.fixed_at p N; exact mesh_log_at p N)
  have e' : Γ ⊢[PRAAx] RationalArithmetic.add (GammaEulerConstantName.fixedSample p N) (meshLogSample p N) ≐
      RationalArithmetic.add (GammaEulerMesh.sample N (mesh p)) (harmonicLog N (mesh p)) := by simpa using e
  exact e'.eqTrans (fixed_mesh_sum N (mesh p) hN (mesh_positive p))

theorem actual_original_robin_grid_telescope_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 0) ⟶ le (var 0+var 3) (var 2) ⟶ prefixBounds (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (grid_telescope _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem original_finite_mesh_robin_comparison_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ le one (var 1) ⟶
      RationalValueBounds.upper (robinValue (var 0) (var 2)) (harmonicLog (var 0) (var 1)) one (var 1) ⋏
      RationalValueBounds.upper (harmonicLog (var 0) (var 1)) (robinValue (var 0) (var 2)) (pred (var 0)) (gain (var 2))) :=
  closeUniv 3 (.impI (.impI (finite_bridge _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_mesh_log_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (meshLogSample (var 0) (var 1) ≐ harmonicLog (var 1) (mesh (var 0))) := closeUniv 2 (mesh_log_at _ _)
theorem actual_robin_log_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (robinLogSample (var 0) (var 1) ≐ robinValue (var 1) (robinClock (var 1) (var 0))) := closeUniv 2 (robin_log_at _ _)
theorem original_named_mesh_robin_compatibility_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ RationalValueBounds.radius (meshLogSample (var 1) (var 0)) (robinLogSample (var 2) (var 0))
      (unit (var 1)+unit (var 2)) (unit (var 1)*unit (var 2))) :=
  closeUniv 3 (.impI (cross_compatibility _ _ _ Prf.hyp0))
theorem original_mesh_log_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le one (var 0) ⟶ RationalCubeInfimumName.regular meshLogF (var 0)) :=
  closeUniv 1 (.impI (mesh_name_regular _ Prf.hyp0))
theorem original_robin_log_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le one (var 0) ⟶ RationalCubeInfimumName.regular robinLogF (var 0)) :=
  closeUniv 1 (.impI (robin_name_regular _ Prf.hyp0))
theorem original_fixed_mesh_log_harmonic_identity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 1) ⟶ RationalArithmetic.add
      (GammaEulerConstantName.fixedSample (var 0) (var 1)) (meshLogSample (var 0) (var 1)) ≐ harmonicValue (var 1)) :=
  closeUniv 2 (.impI (fixed_log_samples_sum _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GammaMeshRobinLogBridge
