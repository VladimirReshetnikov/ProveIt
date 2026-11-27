import IPRADerivations.Analysis.Stirling.Binet.SecondFormula.Decay.FiniteRows.GaussianBinetSecondDecayFinite
import IPRADerivations.Analysis.Stirling.Binet.SecondFormula.Decay.Tails.GaussianBinetSecondDecayTail

/-!
# A common finite mesh and clock for a frozen-pi second Binet tail

The largest index sets one certified time mesh and one actual
observation clock for all rows. The row body evaluates the original
arctangent and frozen-pi exponential at those same time tags. The
resulting finite Gaussian sum has a horizon-independent tail bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBinetSecondDecayFrozenTail

open_ipra
open GaussianBinetSecondDecayFinite (finite_bound)
open GaussianBinetSecondDecayGrid (value rowBody)
open GaussianBinetSecondDecayPointwise (frozenPiNumerator frozen_pi_rate)
open GaussianBinetSecondDecayTail (rowBounds finite_tail)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (sampleData field0 field1 field2 field3 field4 field5
  field0_at field1_at field2_at field3_at field4_at field5_at
  subst_field0 subst_field1 subst_field2 subst_field3 subst_field4 subst_field5)
open GaussianStirlingConstant (piDenominator)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalRiemannRefinement (leftSum)
open GaussianRightHalfPlaneLogarithm (source)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def mesh (T M k : PTm n) : PTm n :=
  let C := frozenPiNumerator M k*T
  succ (C+num 3*(C*C))

def clockFloor (N T M k : PTm n) : PTm n :=
  let H := frozenPiNumerator M k
  num 20*N+(two*(T*N*H)+(M*M)*T*(num 8+num 10*T))

def clock (p T M k : PTm n) : PTm n := p+clockFloor (mesh T M k) T M k

private theorem le_unit (p : PTm n) : Γ ⊢[PRAAx] le p (unit p) :=
  le_trans (le_succ_self p) (RationalClosure.succ_le_two_pow p)

private theorem frozen_order (m M k : PTm n) (h : Γ ⊢[PRAAx] le m M) :
    Γ ⊢[PRAAx] le (frozenPiNumerator m k) (frozenPiNumerator M k) :=
  mul_le_mul_right _ h

theorem mesh_bounds (N T M k m : PTm n) (hM : Γ ⊢[PRAAx] le m M)
    (hn : Γ ⊢[PRAAx] le (mesh T M k) N) :
    let H := frozenPiNumerator m k
    Γ ⊢[PRAAx] le one N ⋏ (le (H*T) (piDenominator k*N) ⋏ le (num 3*((H*T)*(H*T))) N) := by
  let H := frozenPiNumerator m k
  let C := frozenPiNumerator M k*T
  have hC : Γ ⊢[PRAAx] le (H*T) C := mul_le_mul_right T (frozen_order m M k hM)
  have upC : Γ ⊢[PRAAx] le C N := le_trans (le_trans (le_add_right _ _) (le_succ_self _)) hn
  have hJ := (frozen_pi_rate (Γ := Γ) m k).andE₁
  have step := le_trans (le_trans hC upC) (le_congr (one_mul N) (.eqRefl _) (mul_le_mul_right N hJ))
  have sharp := le_trans (mul_le_mul_left (num 3) (sq_le_sq hC))
    (le_trans (le_trans (le_add_left (num 3*(C*C)) C) (le_succ_self _)) hn)
  exact .andI (le_trans (zero_lt_succ _) hn) (.andI step sharp)

theorem clock_bounds (q N T M k m : PTm n) (hM : Γ ⊢[PRAAx] le m M)
    (hq : Γ ⊢[PRAAx] le (clockFloor N T M k) (unit q)) :
    let H := frozenPiNumerator m k
    Γ ⊢[PRAAx] le (num 20*N) (unit q) ⋏
      (le (two*(T*N*H)) (unit q) ⋏ le ((m*m)*T*(num 8+num 10*T)) (unit q)) := by
  let A := num 20*N
  let B := two*(T*N*frozenPiNumerator M k)
  let E := (M*M)*T*(num 8+num 10*T)
  have grow : Γ ⊢[PRAAx] le (A+(B+E)) (unit q) := hq
  have rest := le_trans (le_add_left (B+E) A) grow
  have row := le_trans (mul_le_mul_left two (mul_le_mul_left (T*N) (frozen_order m M k hM)))
    (le_trans (le_add_right B E) rest)
  have slack := le_trans (mul_le_mul_right (num 8+num 10*T) (mul_le_mul_right T (sq_le_sq hM)))
    (le_trans (le_add_left E B) rest)
  exact .andI (le_trans (le_add_right A _) grow) (.andI row slack)

theorem row_bound_at (q N T M k m K X Y D sign : PTm n)
    (hz : Γ ⊢[PRAAx] source X D sign) (hT : Γ ⊢[PRAAx] le one T)
    (hm : Γ ⊢[PRAAx] le one m) (hM : Γ ⊢[PRAAx] le m M) (hK : Γ ⊢[PRAAx] le D (K*X))
    (hn : Γ ⊢[PRAAx] le (mesh T M k) N) (hq : Γ ⊢[PRAAx] le (clockFloor N T M k) (unit q)) :
    Γ ⊢[PRAAx] bounded (value q N T (frozenPiNumerator m k) (piDenominator k) X Y D sign)
      (num 11*K) (m*m) := by
  have rate := frozen_pi_rate (Γ := Γ) m k
  have meshBound := mesh_bounds N T M k m hM hn
  have clockBound := clock_bounds q N T M k m hM hq
  exact finite_bound q N T _ _ m K X Y D sign hz meshBound.andE₁ hT rate.andE₁ hm rate.andE₂ hK
    meshBound.andE₂.andE₁ meshBound.andE₂.andE₂ clockBound.andE₁ clockBound.andE₂.andE₁ clockBound.andE₂.andE₂

private theorem clock_scheduled (p T M k : PTm n) :
    Γ ⊢[PRAAx] le (clockFloor (mesh T M k) T M k) (unit (clock p T M k)) :=
  le_trans (le_add_left _ p) (le_unit _)

theorem scheduled_row_bound (p T M k m K X Y D sign : PTm n)
    (hz : Γ ⊢[PRAAx] source X D sign) (hT : Γ ⊢[PRAAx] le one T)
    (hm : Γ ⊢[PRAAx] le one m) (hM : Γ ⊢[PRAAx] le m M) (hK : Γ ⊢[PRAAx] le D (K*X)) :
    Γ ⊢[PRAAx] bounded
      (value (clock p T M k) (mesh T M k) T (frozenPiNumerator m k) (piDenominator k) X Y D sign)
      (num 11*K) (m*m) :=
  row_bound_at _ _ T M k m K X Y D sign hz hT hm hM hK (le_refl _) (clock_scheduled p T M k)

private theorem val_five {α : Type} {m : ℕ} (a : α) (u : Fin (m+5) → α) :
    Matrix.vecCons a u 5 = Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail u)))) := rfl
private theorem val_six {α : Type} {m : ℕ} (a : α) (u : Fin (m+6) → α) :
    Matrix.vecCons a u 6 = Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail u))))) := rfl

@[simp] private theorem subst_piNumerator {m : ℕ} (σ : Fin n → PTm m) (k : PTm n) :
    Syn.subst σ (GaussianStirlingConstant.piNumerator k) = GaussianStirlingConstant.piNumerator (Syn.subst σ k) := by
  simp [GaussianStirlingConstant.piNumerator,BaselQuadrature.Q,GaussianGammaHalfPiName.clearing,
    GaussianGammaHalfPiName.meshAt,GaussianGammaHalfPiName.meshIndex,GaussianGammaHalfPiName.orderAt,
    GaussianGammaHalfPiName.orderIndex,WallisFinite.Dm,one,two]

@[simp] private theorem subst_piDenominator {m : ℕ} (σ : Fin n → PTm m) (k : PTm n) :
    Syn.subst σ (piDenominator k) = piDenominator (Syn.subst σ k) := by
  simp [piDenominator,Products.fact,GaussianGammaHalfPiName.clearing,GaussianGammaHalfPiName.meshAt,
    GaussianGammaHalfPiName.meshIndex,GaussianGammaHalfPiName.orderAt,GaussianGammaHalfPiName.orderIndex,
    WallisFinite.Dm,one,two]

private def term (i p N T k C x : PTm n) : PTm n :=
  leftSum rowBody N (sampleData p N T (frozenPiNumerator (succ (C+i)) k) (piDenominator k) x) T one

@[simp] private theorem subst_term {m : ℕ} (σ : Fin n → PTm m) (i p N T k C x : PTm n) :
    Syn.subst σ (term i p N T k C x) = term (Syn.subst σ i) (Syn.subst σ p) (Syn.subst σ N)
      (Syn.subst σ T) (Syn.subst σ k) (Syn.subst σ C) (Syn.subst σ x) := by
  simp [term,frozenPiNumerator,one]

def body : PTm 2 := term (var 0) (field0 (var 1)) (field1 (var 1)) (field2 (var 1))
  (field3 (var 1)) (field4 (var 1)) (field5 (var 1))

def data_at (q N T k C X Y D sign : PTm n) : PTm n :=
  sampleData q N T k C (pairT (D*D) (GaussianBinetArctangentQuadrature.fixedData X Y D sign))

ipra_subst data_at

def data (p T k C r X Y D sign : PTm n) : PTm n :=
  let M := succ (C+r)
  data_at (clock p T M k) (mesh T M k) T k C X Y D sign

ipra_subst mesh [frozenPiNumerator]

ipra_subst clockFloor [frozenPiNumerator, one, two]

ipra_subst clock

ipra_subst data

theorem row_at_sample_data (i q N T k C x : PTm n) :
    Γ ⊢[PRAAx] inst2 body i (sampleData q N T k C x) ≐
      leftSum rowBody N (sampleData q N T (frozenPiNumerator (succ (C+i)) k) (piDenominator k) x) T one := by
  let d := sampleData q N T k C x
  change Γ ⊢[PRAAx] inst2 body i d ≐ term i q N T k C x
  simpa only [body,inst2,subst_term,subst_field0,subst_field1,subst_field2,subst_field3,subst_field4,
    subst_field5,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_four,val_five,val_six,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (term (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7)
      (σ := ![i,field0 d,field1 d,field2 d,field3 d,field4 d,field5 d]) (σ' := ![i,q,N,T,k,C,x])
      (fun j => by
        fin_cases j
        exact .eqRefl _
        exact field0_at _ _ _ _ _ _
        exact field1_at _ _ _ _ _ _
        exact field2_at _ _ _ _ _ _
        exact field3_at _ _ _ _ _ _
        exact field4_at _ _ _ _ _ _
        exact field5_at _ _ _ _ _ _)

theorem row_at (i p T k C r X Y D sign : PTm n) :
    let M := succ (C+r)
    Γ ⊢[PRAAx] inst2 body i (data p T k C r X Y D sign) ≐
      value (clock p T M k) (mesh T M k) T (frozenPiNumerator (succ (C+i)) k) (piDenominator k) X Y D sign :=
  row_at_sample_data i _ _ T k C _

theorem tail_bound_at (q N T k C r K X Y D sign : PTm n)
    (hz : Γ ⊢[PRAAx] source X D sign) (hT : Γ ⊢[PRAAx] le one T)
    (hC : Γ ⊢[PRAAx] le one C) (hK : Γ ⊢[PRAAx] le D (K*X))
    (hn : Γ ⊢[PRAAx] le (mesh T (succ (C+r)) k) N)
    (hq : Γ ⊢[PRAAx] le (clockFloor N T (succ (C+r)) k) (unit q)) :
    Γ ⊢[PRAAx] bounded (GaussianRationalFiniteSum.sum body r (data_at q N T k C X Y D sign)) (num 11*K) C := by
  have rows : Γ ⊢[PRAAx] rowBounds body (data_at q N T k C X Y D sign) (num 11*K) C r := by
    refine .allI (.impI ?_)
    let s (z : PTm n) := Syn.shift z
    let i : PTm (n+1) := var 0
    let Δ := lt i (s r) :: Γ.map Fm.shift
    let m := succ (s C+i)
    let M := succ (s C+s r)
    have sz : Δ ⊢[PRAAx] source (s X) (s D) (s sign) := by
      simpa [Δ,s,Fm.shift,Syn.shift,source,GaussianRightHalfPlaneArgument.source] using hz.shift.wk
    have st : Δ ⊢[PRAAx] le one (s T) := (Order.shift_one_le hT).wk
    have sk : Δ ⊢[PRAAx] le (s D) (s K*s X) := by simpa [Δ,s,Fm.shift,Syn.shift] using hK.shift.wk
    have sn : Δ ⊢[PRAAx] le (mesh (s T) M (s k)) (s N) := by
      simpa only [Δ,M,s,Fm.shift,Syn.shift,subst_le,subst_mesh,
        ConciseIPRA.PTm.subst_succ,PTm.subst_add] using hn.shift.wk
    have sq : Δ ⊢[PRAAx] le (clockFloor (s N) (s T) M (s k)) (unit (s q)) := by
      simpa only [Δ,M,s,Fm.shift,Syn.shift,subst_le,subst_clockFloor,
        ConciseIPRA.PTm.subst_succ,PTm.subst_add,GaussianCoefficientNameBounds.subst_unit] using hq.shift.wk
    have hi : Δ ⊢[PRAAx] le i (s r) := le_of_lt Prf.hyp0
    have order : Δ ⊢[PRAAx] le m M :=
      le_congr (succ_eq_add_one _).eqSymm (succ_eq_add_one _).eqSymm
        (add_le_add_right one (add_le_add_left (s C) hi))
    have estimate := row_bound_at (s q) (s N) (s T) M (s k) m (s K) (s X) (s Y) (s D) (s sign)
      sz st (zero_lt_succ _) order sk sn sq
    have read : Δ ⊢[PRAAx] inst2 body i (data_at (s q) (s N) (s T) (s k) (s C) (s X) (s Y) (s D) (s sign)) ≐
        value (s q) (s N) (s T) (frozenPiNumerator m (s k)) (piDenominator (s k)) (s X) (s Y) (s D) (s sign) :=
      row_at_sample_data i (s q) (s N) (s T) (s k) (s C) _
    simpa only [rowBounds,Δ,i,m,M,s,Syn.shift,subst_data_at,PTm.subst_mul,PTm.subst_num] using
      bound_congr read.eqSymm (.eqRefl _) (.eqRefl _) estimate
  exact finite_tail _ _ _ _ _ hC rows

theorem frozen_tail_bound (p T k C r K X Y D sign : PTm n)
    (hz : Γ ⊢[PRAAx] source X D sign) (hT : Γ ⊢[PRAAx] le one T)
    (hC : Γ ⊢[PRAAx] le one C) (hK : Γ ⊢[PRAAx] le D (K*X)) :
    Γ ⊢[PRAAx] bounded (GaussianRationalFiniteSum.sum body r (data p T k C r X Y D sign)) (num 11*K) C :=
  tail_bound_at _ _ T k C r K X Y D sign hz hT hC hK (le_refl _) (clock_scheduled p T _ k)

end LeanProofs.IPRA.Analysis.GaussianBinetSecondDecayFrozenTail
