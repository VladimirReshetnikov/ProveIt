import IPRADerivations.Analysis.GaussianBinetSecondDecayFinite
import IPRADerivations.Analysis.GaussianBinetSecondDecayTail

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

open LeanProofs.ConciseIPRA LeanProofs.IPRA
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
open LeanProofs.IPRA.PTm (num)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def mesh (T M k : PTm n) : PTm n :=
  let C := frozenPiNumerator M k*T
  succ (C+num 3*(C*C))

def clock (p T M k : PTm n) : PTm n :=
  let N := mesh T M k
  let H := frozenPiNumerator M k
  p+(num 20*N+(two*(T*N*H)+(M*M)*T*(num 8+num 10*T)))

private theorem le_unit (p : PTm n) : Γ ⊢[PRAAx] le p (unit p) :=
  le_trans (le_succ_self p) (RationalClosure.succ_le_two_pow p)

private theorem frozen_order (m M k : PTm n) (h : Γ ⊢[PRAAx] le m M) :
    Γ ⊢[PRAAx] le (frozenPiNumerator m k) (frozenPiNumerator M k) :=
  mul_le_mul_right _ h

theorem scheduled_row_bound (p T M k m K X Y D sign : PTm n)
    (hz : Γ ⊢[PRAAx] source X D sign) (hT : Γ ⊢[PRAAx] le one T)
    (hm : Γ ⊢[PRAAx] le one m) (hM : Γ ⊢[PRAAx] le m M) (hK : Γ ⊢[PRAAx] le D (K*X)) :
    Γ ⊢[PRAAx] bounded
      (value (clock p T M k) (mesh T M k) T (frozenPiNumerator m k) (piDenominator k) X Y D sign)
      (num 11*K) (m*m) := by
  let N := mesh T M k
  let q := clock p T M k
  let H := frozenPiNumerator m k
  let Hmax := frozenPiNumerator M k
  let J := piDenominator k
  let C := Hmax*T
  let A := num 20*N
  let B := two*(T*N*Hmax)
  let E := (M*M)*T*(num 8+num 10*T)
  have rate := frozen_pi_rate (Γ := Γ) m k
  have ho := frozen_order m M k hM
  have hN : Γ ⊢[PRAAx] le one N := zero_lt_succ _
  have hC : Γ ⊢[PRAAx] le (H*T) C := mul_le_mul_right T ho
  have upC : Γ ⊢[PRAAx] le C N := le_trans (le_add_right _ _) (le_succ_self _)
  have sharp : Γ ⊢[PRAAx] le (num 3*((H*T)*(H*T))) N :=
    le_trans (le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right (num 3) (sq_le_sq hC)))
      (le_trans (le_add_left (num 3*(C*C)) C) (le_succ_self _))
  have step : Γ ⊢[PRAAx] le (H*T) (J*N) :=
    le_trans (le_trans hC upC) (le_congr (one_mul N) (.eqRefl _) (mul_le_mul_right N rate.andE₁))
  have grow : Γ ⊢[PRAAx] le (A+(B+E)) (unit q) := le_trans (le_add_left _ p) (le_unit q)
  have hA : Γ ⊢[PRAAx] le A (unit q) := le_trans (le_add_right A _) grow
  have hBE : Γ ⊢[PRAAx] le (B+E) (unit q) := le_trans (le_add_left _ A) grow
  have hB : Γ ⊢[PRAAx] le (two*(T*N*H)) (unit q) :=
    le_trans (le_congr (by ipra_ring) (by dsimp only [B]; ipra_ring)
      (mul_le_mul_right (two*T*N) ho)) (le_trans (le_add_right B E) hBE)
  have hE : Γ ⊢[PRAAx] le ((m*m)*T*(num 8+num 10*T)) (unit q) :=
    le_trans (mul_le_mul_right (num 8+num 10*T) (mul_le_mul_right T (sq_le_sq hM)))
      (le_trans (le_add_left E B) hBE)
  exact finite_bound q N T H J m K X Y D sign hz hN hT rate.andE₁ hm rate.andE₂ hK step sharp hA hB hE

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

def data (p T k C r X Y D sign : PTm n) : PTm n :=
  let M := succ (C+r)
  sampleData (clock p T M k) (mesh T M k) T k C
    (pairT (D*D) (GaussianBinetArctangentQuadrature.fixedData X Y D sign))

@[simp] theorem subst_mesh {m : ℕ} (σ : Fin n → PTm m) (T M k : PTm n) :
    Syn.subst σ (mesh T M k) = mesh (Syn.subst σ T) (Syn.subst σ M) (Syn.subst σ k) := by
  simp [mesh,frozenPiNumerator]

@[simp] theorem subst_clock {m : ℕ} (σ : Fin n → PTm m) (p T M k : PTm n) :
    Syn.subst σ (clock p T M k) = clock (Syn.subst σ p) (Syn.subst σ T) (Syn.subst σ M) (Syn.subst σ k) := by
  simp [clock,frozenPiNumerator,one,two]

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (p T k C r X Y D sign : PTm n) :
    Syn.subst σ (data p T k C r X Y D sign) = data (Syn.subst σ p) (Syn.subst σ T) (Syn.subst σ k)
      (Syn.subst σ C) (Syn.subst σ r) (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ D) (Syn.subst σ sign) := by
  simp [data]

theorem row_at (i p T k C r X Y D sign : PTm n) :
    let M := succ (C+r)
    Γ ⊢[PRAAx] inst2 body i (data p T k C r X Y D sign) ≐
      value (clock p T M k) (mesh T M k) T (frozenPiNumerator (succ (C+i)) k) (piDenominator k) X Y D sign := by
  let M := succ (C+r)
  let P := clock p T M k
  let N := mesh T M k
  let x := pairT (D*D) (GaussianBinetArctangentQuadrature.fixedData X Y D sign)
  let d := sampleData P N T k C x
  change Γ ⊢[PRAAx] inst2 body i d ≐ term i P N T k C x
  simpa only [body,inst2,subst_term,subst_field0,subst_field1,subst_field2,subst_field3,subst_field4,
    subst_field5,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_four,val_five,val_six,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (term (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7)
      (σ := ![i,field0 d,field1 d,field2 d,field3 d,field4 d,field5 d]) (σ' := ![i,P,N,T,k,C,x])
      (fun j => by
        fin_cases j
        exact .eqRefl _
        exact field0_at _ _ _ _ _ _
        exact field1_at _ _ _ _ _ _
        exact field2_at _ _ _ _ _ _
        exact field3_at _ _ _ _ _ _
        exact field4_at _ _ _ _ _ _
        exact field5_at _ _ _ _ _ _)

theorem frozen_tail_bound (p T k C r K X Y D sign : PTm n)
    (hz : Γ ⊢[PRAAx] source X D sign) (hT : Γ ⊢[PRAAx] le one T)
    (hC : Γ ⊢[PRAAx] le one C) (hK : Γ ⊢[PRAAx] le D (K*X)) :
    Γ ⊢[PRAAx] bounded (GaussianRationalFiniteSum.sum body r (data p T k C r X Y D sign)) (num 11*K) C := by
  have rows : Γ ⊢[PRAAx] rowBounds body (data p T k C r X Y D sign) (num 11*K) C r := by
    refine .allI (.impI ?_)
    let s (z : PTm n) := Syn.shift z
    let i : PTm (n+1) := var 0
    let Δ := lt i (s r) :: Γ.map Fm.shift
    let m := succ (s C+i)
    let M := succ (s C+s r)
    have sz : Δ ⊢[PRAAx] source (s X) (s D) (s sign) := by
      simpa [Δ,s,Fm.shift,Syn.shift,source,GaussianRightHalfPlaneArgument.source] using hz.shift.wk
    have st : Δ ⊢[PRAAx] le one (s T) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hT.shift.wk
    have sk : Δ ⊢[PRAAx] le (s D) (s K*s X) := by simpa [Δ,s,Fm.shift,Syn.shift] using hK.shift.wk
    have hi : Δ ⊢[PRAAx] le i (s r) := le_of_lt Prf.hyp0
    have order : Δ ⊢[PRAAx] le m M :=
      le_congr (succ_eq_add_one _).eqSymm (succ_eq_add_one _).eqSymm
        (add_le_add_right one (le_congr (add_comm i (s C)) (add_comm (s r) (s C))
          (add_le_add_right (s C) hi)))
    have estimate := scheduled_row_bound (s p) (s T) M (s k) m (s K) (s X) (s Y) (s D) (s sign)
      sz st (zero_lt_succ _) order sk
    have read := row_at (Γ := Δ) i (s p) (s T) (s k) (s C) (s r) (s X) (s Y) (s D) (s sign)
    simpa only [rowBounds,Δ,i,m,M,s,Syn.shift,subst_data,PTm.subst_mul,PTm.subst_num] using
      bound_congr read.eqSymm (.eqRefl _) (.eqRefl _) estimate
  exact finite_tail _ _ _ _ _ hC rows

end LeanProofs.IPRA.Analysis.GaussianBinetSecondDecayFrozenTail
