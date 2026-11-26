import IPRADerivations.Analysis.Stirling.Binet.ExponentialIntegrals.GaussianBinetExponentialIntegralGrid
import IPRADerivations.Analysis.Series.GaussianRationalParameterTelescope
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.GaussianLogGammaEulerRepresentation

/-!
# Compact antiderivative of the actual complex Laplace exponential

The finite left quadrature obeys the cleared antiderivative identity
`q * ∫₀ᵀ exp(q*t) dt = exp(q*T) - 1` with explicit mesh and sampling
errors. The signed rational right-half-plane specialization uses the
same exponential observation as the Binet strip at every physical
time.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBinetExponentialIntegral

open_ipra
open GaussianBinetExponentialPanel (nonpositive sample)
open GaussianBinetExponentialIntegralGrid (exponent row evaluatorF value cell_at subst_exponent)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (sampleBody sampleData)
open GaussianGammaCanonicalExponent (constantF)
open GaussianLogGammaEulerHead (argument)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianNameEquivalence (point_at)
open GaussianRadiusExponentialName (input data)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalFiniteSum (sum)
open GaussianRationalHorner (positive_product qadd qmul qmul_canonical)
open GaussianRationalMetric (bounded distanceBounded qsub qnegative)
open GaussianRationalParameterTelescope (localRows forward_at)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (bounded_negative)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr qone)
open GaussianReciprocalHorner (qmul_associative)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def nonpositiveRows (q T N : PTm n) : Fm PTm n := .all
  (le (var 0) (Syn.shift N) ⟶ nonpositive (exponent (Syn.shift q) (Syn.shift T*var 0) (Syn.shift N)))

def numerator (p R T N : PTm n) : PTm n := num 10*(N*N)+two*((R*T)*(R*T))*unit p
def rowDen (p N : PTm n) : PTm n := unit p*(N*N)

ipra_subst numerator [two]
ipra_subst rowDen
ipra_subst nonpositive

ipra_subst nonpositiveRows [Syn.subst_shift, Syn.shift_subst]

private theorem row_negative (j q T N : PTm n) (hr : Γ ⊢[PRAAx] nonpositiveRows q T N)
    (hj : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx] nonpositive (exponent q (T*j) N) := by
  have h : Γ ⊢[PRAAx] le j N ⟶ nonpositive (exponent q (T*j) N) := by
    simpa only [nonpositiveRows,Fm.subst_imp,subst_nonpositive,subst_exponent,subst_le,PTm.subst_mul,
      Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using hr.allE j
  exact .impE h hj

private theorem sample_congr (p S x y : PTm n) (e : Γ ⊢[PRAAx] x ≐ y) :
    Γ ⊢[PRAAx] sample p x S ≐ sample p y S := by
  simpa only [GaussianBinetExponentialPanel.subst_sample,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (sample (var 0) (var 1) (var 2) : PTm 3)
      (σ := ![p,x,S]) (σ' := ![p,y,S])
      (fun i => by fin_cases i; exact .eqRefl _; exact e; exact .eqRefl _)

theorem local_step (p q R T j N : PTm n) (hb : Γ ⊢[PRAAx] bounded q R one)
    (hN : Γ ⊢[PRAAx] le one N) (hS : Γ ⊢[PRAAx] le (R*T) N)
    (hr : Γ ⊢[PRAAx] nonpositiveRows q T N)
    (hc : Γ ⊢[PRAAx] nonpositive (exponent q T N)) (hj : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] distanceBounded (qsub (row p q (R*T) (T*succ j) N) (row p q (R*T) (T*j) N))
      (qmul (exponent q T N) (row p q (R*T) (T*j) N)) (numerator p R T N) (rowDen p N) := by
  let x := exponent q (T*j) N
  let y := exponent q T N
  let z := exponent q (T*succ j) N
  let S := R*T
  have e : Γ ⊢[PRAAx] qadd x y ≐ z := GaussianBinetExponentialIntegralGrid.step_coefficient q T j N hN
  have ix := GaussianBinetExponentialIntegralGrid.exponent_input q R T j N hb hN (le_of_lt hj)
  have iz : Γ ⊢[PRAAx] input constantF S z := GaussianBinetExponentialIntegralGrid.exponent_input q R T (succ j) N hb hN hj
  have iz' : Γ ⊢[PRAAx] input constantF S (qadd x y) := by
    simpa only [GaussianRadiusExponentialName.subst_input,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      (Prf.eqSubst1 (input constantF (Syn.shift S) (var 0)) e.eqSymm
        (by simpa only [GaussianRadiusExponentialName.subst_input,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using iz))
  have hx := row_negative j q T N hr (le_of_lt hj)
  have est := GaussianBinetExponentialPanel.step_error p x y S S S N ix iz' hx hc hN hS
    (GaussianBinetExponentialIntegralGrid.step_bound q R T N hb hN) (qmul_canonical _ _)
  exact distance_congr (qsub_congr (sample_congr p S (qadd x y) z e) (.eqRefl _))
    (qmul_commutative _ _) (.eqRefl _) (.eqRefl _) est

theorem finite_error (p q R T N : PTm n) (hb : Γ ⊢[PRAAx] bounded q R one)
    (hN : Γ ⊢[PRAAx] le one N) (hS : Γ ⊢[PRAAx] le (R*T) N)
    (hr : Γ ⊢[PRAAx] nonpositiveRows q T N) (hc : Γ ⊢[PRAAx] nonpositive (exponent q T N)) :
    Γ ⊢[PRAAx] distanceBounded (qmul q (value p q (R*T) T N)) (qsub (row p q (R*T) T one) qone)
      (numerator p R T N) (unit p*N) := by
  let f := sampleBody evaluatorF
  let d := sampleData p N one T one (pairT q (R*T))
  let c := exponent q T N
  let E := numerator p R T N
  let W := rowDen p N
  have hW : Γ ⊢[PRAAx] le one W := positive_product _ _ (unit_positive p) (positive_product _ _ hN hN)
  have rows : Γ ⊢[PRAAx] localRows f f N d d c E W := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let Δ := lt (var 0) (s N) :: Γ.map Fm.shift
    have bs : Δ ⊢[PRAAx] bounded (s q) (s R) one := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hb.shift.wk
    have ns : Δ ⊢[PRAAx] le one (s N) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hN.shift.wk
    have ss : Δ ⊢[PRAAx] le (s R*s T) (s N) := by simpa [Δ,s,Fm.shift,Syn.shift] using hS.shift.wk
    have rs : Δ ⊢[PRAAx] nonpositiveRows (s q) (s T) (s N) := by simpa [Δ,s,Fm.shift,Syn.shift] using hr.shift.wk
    have cs : Δ ⊢[PRAAx] nonpositive (exponent (s q) (s T) (s N)) := by
      simpa [Δ,s,Fm.shift,Syn.shift] using hc.shift.wk
    have read (j : PTm (n+1)) := cell_at (Γ := Δ) j (s p) (s q) (s R*s T) (s T) (s N)
    have ll := qsub_congr (read (succ (var 0))) (read (var 0))
    have rr := (GaussianRationalFiniteSum.multiply_body_at (Γ := Δ) f (exponent (s q) (s T) (s N)) (var 0)
      (sampleData (s p) (s N) one (s T) one (pairT (s q) (s R*s T)))).eqTrans
      (qmul_congr (.eqRefl _) (read (var 0)))
    simpa only [localRows,GaussianRationalRiemannRefinement.termsDistance,Syn.shift,s,Δ,d,c,E,W,f,
      GaussianCompactRiemannName.subst_sampleData,subst_pairT,PTm.subst_mul,subst_exponent,
      subst_numerator,subst_rowDen,forward_at,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
      distance_congr ll.eqSymm rr.eqSymm (.eqRefl _) (.eqRefl _)
        (local_step (s p) (s q) (s R) (s T) (var 0) (s N) bs ns ss rs cs Prf.hyp0)
  have raw := GaussianRationalParameterTelescope.local_error f f N d d c E W hW rows
  have er := (cell_at (Γ := Γ) N p q (R*T) T N).eqTrans
    (GaussianBinetExponentialIntegralGrid.right_endpoint p q (R*T) T N hN)
  have el := (cell_at (Γ := Γ) zero p q (R*T) T N).eqTrans
    (GaussianBinetExponentialIntegralGrid.left_endpoint p q (R*T) T N hN)
  have ew : Γ ⊢[PRAAx] GaussianRationalRiemannRefinement.weight T one N ≐ fraction T N :=
    GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl _) (one_mul N)
  have ec : Γ ⊢[PRAAx] qmul q (value p q (R*T) T N) ≐ qmul c (sum f N d) :=
    (qmul_associative q _ _).eqSymm.eqTrans (qmul_congr (qmul_congr (.eqRefl _) ew) (.eqRefl _))
  exact distance_radius_mono _ _ _ _ _ _ hW (positive_product _ _ (unit_positive p) hN)
    (le_of_eq_add (d := zero) (by dsimp only [E,W,rowDen]; ipra_ring))
    (distance_congr ec.eqSymm (qsub_congr er el) (.eqRefl _) (.eqRefl _)
      (distance_symmetric _ _ _ _ hW raw))

theorem original_finite_error (p X Y D sign R T N : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianLogGammaEulerResidualDomain.source X Y D sign R)
    (hN : Γ ⊢[PRAAx] le one N) (hS : Γ ⊢[PRAAx] le (R*T) N) :
    Γ ⊢[PRAAx] distanceBounded
      (qmul (qnegative (argument X Y D sign)) (value p (qnegative (argument X Y D sign)) (R*T) T N))
      (qsub (ap2 GaussianBinetLaplaceExponential.nameF p
        (GaussianBinetLaplaceExponential.data X Y D sign R T T one)) qone)
      (numerator p R T N) (unit p*N) := by
  let q := qnegative (argument X Y D sign)
  have hD : Γ ⊢[PRAAx] le one D := hz.andE₁.andE₂
  have hr : Γ ⊢[PRAAx] nonpositiveRows q T N := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let Δ := le (var 0) (s N) :: Γ.map Fm.shift
    have ds : Δ ⊢[PRAAx] le one (s D) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hD.shift.wk
    have ns : Δ ⊢[PRAAx] le one (s N) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hN.shift.wk
    simpa only [nonpositiveRows,nonpositive,q,s,Δ,Syn.shift,GaussianRationalMetric.subst_qnegative,
      GaussianLogGammaEulerRepresentation.subst_argument,exponent,GaussianBinetLaplaceExponential.exponent] using
      GaussianBinetLaplaceExponential.exponent_nonpositive (s X) (s Y) (s D) (s sign) (s T*var 0) (s N) ds ns
  exact finite_error p q R T N (bounded_negative _ _ _ (le_refl one)
    (GaussianBinetLaplaceExponential.parameter_bound X Y D sign R hz)) hN hS hr
    (GaussianBinetLaplaceExponential.exponent_nonpositive X Y D sign T N hD hN)

def uniformCost (R T : PTm n) : PTm n := num 10+two*((R*T)*(R*T))+two

local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

/-- The evaluation clock pays for all panels, and every sufficiently
fine mesh uses the same dyadic error budget as the horizon endpoint. -/
theorem original_cofinal_error (p X Y D sign R T N : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianLogGammaEulerResidualDomain.source X Y D sign R)
    (hS : Γ ⊢[PRAAx] le (R*T) N) (hpN : Γ ⊢[PRAAx] le (unit p) N) :
    Γ ⊢[PRAAx] distanceBounded
      (qmul (qnegative (argument X Y D sign)) (value (p+N) (qnegative (argument X Y D sign)) (R*T) T N))
      (qsub (ap2 GaussianBinetLaplaceExponential.nameF p
        (GaussianBinetLaplaceExponential.data X Y D sign R T T one)) qone)
      (uniformCost R T) (unit p) := by
  let z := qnegative (argument X Y D sign)
  let s := p+N
  let P := unit p
  let U := unit s
  let x := GaussianBinetLaplaceExponential.data X Y D sign R T T one
  let F := GaussianBinetLaplaceExponential.nameF
  let C := num 10+two*((R*T)*(R*T))
  have hp := unit_positive (Γ := Γ) p
  have hs := unit_positive (Γ := Γ) s
  have hN := le_trans hp hpN
  have hsz : Γ ⊢[PRAAx] le (N*P) U := by
    have grow := le_trans (le_succ_self (Γ := Γ) N) (RationalClosure.succ_le_two_pow N)
    exact le_congr (.eqRefl _) ((mul_comm (unit N) P).eqTrans (pw_add two p N).eqSymm) (mul_le_mul_right P grow)
  have error : Γ ⊢[PRAAx] distanceBounded (qmul z (value s z (R*T) T N))
      (qsub (ap2 F s x) qone) C P := by
    apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hs hN) hp _
      (original_finite_error s X Y D sign R T N hz hN hS)
    dsimp only [C,numerator]
    ipra_le 10*𝔞(N)*sl hsz + 2*𝔞((R*T)*(R*T))*𝔞(U)*sl hpN
  have later : Γ ⊢[PRAAx] le p s := le_add_right p N
  have hpu := GaussianExponentialReference.unit_monotone later
  have regular := GaussianBinetLaplaceExponential.regular X Y D sign R T T one hz (le_refl one)
    (le_of_eq_add (d := zero) (by ipra_ring))
  have endpoint : Γ ⊢[PRAAx] distanceBounded (ap2 F s x) (ap2 F p x) two P :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hs hp) hp
      (by ipra_le 𝔞(P)*sl hpu) (point_at _ _ s p regular)
  have diff : Γ ⊢[PRAAx] distanceBounded (qsub (ap2 F s x) qone) (qsub (ap2 F p x) qone) two P :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ hp endpoint
        (GaussianRationalPowerDifference.distance_refl_zero qone P hp))
  exact distance_triangle_same _ _ _ _ _ _ hp error diff

end LeanProofs.IPRA.Analysis.GaussianBinetExponentialIntegral
