import IPRADerivations.Analysis.GammaMeshRobinLogBridge
import IPRADerivations.Analysis.PowerIncrement

/-!
# Finite odd-logarithm sums on a harmonic grid

At the i-th endpoint of a grid starting at a positive integer X, the
odd-logarithm argument is i/(2X+i). The raw Robin brackets furnished
by finite polynomial differences are compared directly with the
left and right harmonic rectangles, including near the endpoint 1.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingOddGrid

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogName (Nz Dz Lz)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinGamma (Lv Pv)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLipName (Rv lip_up lip_low)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le cancel_pos)
open GammaMeshRobinLogBridge (leftSum rightSum left_zero right_zero left_succ right_succ)
open Products (fact)
open RationalAlgebra (positive_product)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def parameter (X i : PTm n) : PTm n := two*X+i
def gap (X i : PTm n) : PTm n := num 4*X*(X+i)
def numerator (X K i : PTm n) : PTm n := Nz K i (parameter X i)
def denominator (X K i : PTm n) : PTm n := Dz K i (parameter X i)

@[simp] theorem subst_parameter {l : ℕ} (σ : Fin n → PTm l) (X i : PTm n) :
    Syn.subst σ (parameter X i) = parameter (Syn.subst σ X) (Syn.subst σ i) := by simp [parameter]
@[simp] theorem subst_numerator {l : ℕ} (σ : Fin n → PTm l) (X K i : PTm n) :
    Syn.subst σ (numerator X K i) = numerator (Syn.subst σ X) (Syn.subst σ K) (Syn.subst σ i) := by simp [numerator]
@[simp] theorem subst_denominator {l : ℕ} (σ : Fin n → PTm l) (X K i : PTm n) :
    Syn.subst σ (denominator X K i) = denominator (Syn.subst σ X) (Syn.subst σ K) (Syn.subst σ i) := by simp [denominator,Dz]

theorem parameter_positive (X i : PTm n) (hX : Γ ⊢[PRAAx] le one X) :
    Γ ⊢[PRAAx] le one (parameter X i) := by
  dsimp [parameter]
  ipra_le 2*sl hX+𝔞 i+1

theorem square_split (X i : PTm n) : Γ ⊢[PRAAx]
    parameter X i*parameter X i ≐ gap X i+i*i := by
  dsimp [parameter,gap]
  ipra_ring

theorem denominator_positive (X K i : PTm n) (hX : Γ ⊢[PRAAx] le one X) :
    Γ ⊢[PRAAx] le one (denominator X K i) :=
  le_congr (.eqRefl _) (LeanProofs.IPRA.AnalyticNumberTheory.RobinLogName.Dz_pos
    (pos_of_one_le (parameter_positive X i hX)) K i).eqSymm (zero_lt_succ _)

private theorem power_absorbs (X G K i : PTm n) (hX : Γ ⊢[PRAAx] le one X)
    (hK : Γ ⊢[PRAAx] le one K) (hi : Γ ⊢[PRAAx] le (G*i) K) :
    Γ ⊢[PRAAx] le (G*Rv K i) (Rv K (parameter X i)) := by
  let j := pred (two*K)
  let h := two*X
  have ep : Γ ⊢[PRAAx] two*K ≐ succ j :=
    pos_of_one_le (positive_product RationalAlgebra.two_positive hK)
  have input : Γ ⊢[PRAAx] i+h ≐ parameter X i := by dsimp [parameter,h]; ipra_ring
  have p := natEq (pw_succ (Γ := Γ) i j)
  have e := natEq ep
  have a : Γ ⊢[PRAAx] le (G*Rv K i) (pw i (succ j)+succ j*pw i j*h) := by
    have ex := natEq (congrAp2 powF ep (.eqRefl i))
    dsimp only [h,j]
    ipra_le 𝔞 (pw i j)*sl hi + 𝔞 (pw i j)*𝔞 K*(4*sl hX+3) + 𝔞 (pw i (succ j)) using
      linear_combination -2*𝔞 X*𝔞 (pw i j)*e-𝔞 G*p-𝔞 G*ex
  exact le_trans a (le_congr (.eqRefl _)
    (congrAp2 powF ep.eqSymm input) (PowerIncrement.power_inc_lower i h j))

private theorem upper_step (X K i : PTm n) (hX : Γ ⊢[PRAAx] le one X) :
    Γ ⊢[PRAAx] le ((X+i)*numerator X K (succ i)*denominator X K i)
      ((X+i)*numerator X K i*denominator X K (succ i)+denominator X K i*denominator X K (succ i)) := by
  let s := parameter X i
  let t := parameter X (succ i)
  let a := X+i
  let b := X+succ i
  let L := Lv K zero
  let U := Pv K s
  let V := Pv K t
  let N := numerator X K i
  let M := numerator X K (succ i)
  have delta : Γ ⊢[PRAAx] succ i*s ≐ i*t+two*X := by dsimp [s,t,parameter]; ipra_ring
  have raw := lip_up (square_split X (succ i)) delta K
  have h4 : Γ ⊢[PRAAx] le one (num 4*X) := by ipra_le 4*sl hX+3
  have step : Γ ⊢[PRAAx] le (M*U*s*b) (N*V*s*b+t*L*U*V) := by
    apply cancel_pos h4
    exact le_congr (by dsimp [M,U,s,b,numerator,gap]; ipra_ring)
      (by dsimp [N,V,s,t,b,L,numerator,gap]; ipra_ring) raw
  have Xiff : Γ ⊢[PRAAx] le (a*t) (s*b) := by dsimp [a,b,s,t,parameter]; ipra_le 𝔞 X
  apply cancel_pos (positive_product (parameter_positive X i hX) (le_trans hX (le_add_right X (succ i))))
  change Γ ⊢[PRAAx] le (s*b*(a*M*(L*U))) (s*b*(a*N*(L*V)+(L*U)*(L*V)))
  ipra_le 𝔞 (a*L)*sl step+𝔞 (L*L*U*V)*sl Xiff

private theorem lower_step (X G K i : PTm n) (hX : Γ ⊢[PRAAx] le one X)
    (hK : Γ ⊢[PRAAx] le one K) (hi : Γ ⊢[PRAAx] le (G*i) K) :
    Γ ⊢[PRAAx] le ((X+i)*(X+succ i)*G*numerator X K i*denominator X K (succ i)
      +(X+i)*G*denominator X K i*denominator X K (succ i))
      ((X+i)*(X+succ i)*G*numerator X K (succ i)*denominator X K i
      +(X+succ i)*denominator X K i*denominator X K (succ i)) := by
  let s := parameter X i
  let t := parameter X (succ i)
  let a := X+i
  let b := X+succ i
  let L := Lv K zero
  let U := Pv K s
  let V := Pv K t
  let N := numerator X K i
  let M := numerator X K (succ i)
  let P := Rv K i
  have delta : Γ ⊢[PRAAx] succ i*s ≐ i*t+two*X := by dsimp [s,t,parameter]; ipra_ring
  have raw := lip_low (square_split X i) delta K
  have h4 : Γ ⊢[PRAAx] le one (num 4*X) := by ipra_le 4*sl hX+3
  have step : Γ ⊢[PRAAx] le (N*V*t*a+s*L*U*V) (M*U*t*a+s*s*P*L*V) := by
    apply cancel_pos h4
    exact le_congr (by dsimp [N,V,t,a,s,L,U,numerator,gap]; ipra_ring)
      (by dsimp [M,U,t,a,s,P,L,V,numerator,gap]; ipra_ring) raw
  have expand : Γ ⊢[PRAAx] U ≐ s*Rv K s :=
    (pw_succ s (two*K)).eqTrans (by ipra_ring)
  have error : Γ ⊢[PRAAx] le (G*s*s*P*L*V) (s*L*U*V) := by
    have e := natEq expand
    ipra_le 𝔞 (s*s*L*V)*sl (power_absorbs X G K i hX hK hi) using
      linear_combination 𝔞 s*𝔞 L*𝔞 V*e
  have first : Γ ⊢[PRAAx] le (G*(N*V*t*a)+G*s*L*U*V) (G*(M*U*t*a)+s*L*U*V) := by
    ipra_le 𝔞 G*sl step+sl error
  have Xiff : Γ ⊢[PRAAx] le (a*t) (s*b) := by dsimp [a,b,s,t,parameter]; ipra_le 𝔞 X
  have next : Γ ⊢[PRAAx] le s t := by dsimp [s,t,parameter]; ipra_le 1
  apply cancel_pos (parameter_positive X (succ i) hX)
  change Γ ⊢[PRAAx] le (t*(a*b*G*N*(L*V)+a*G*(L*U)*(L*V)))
    (t*(a*b*G*M*(L*U)+b*(L*U)*(L*V)))
  ipra_le 𝔞 (b*L)*sl first+𝔞 (G*L*L*U*V)*sl Xiff+𝔞 (b*L*L*U*V)*sl next

theorem grid_step (X G K L i : PTm n) (hX : Γ ⊢[PRAAx] le one X)
    (hK : Γ ⊢[PRAAx] le one K) (hpow : Γ ⊢[PRAAx] le (G*i) K)
    (hi : Γ ⊢[PRAAx] le (X+succ i) L) : Γ ⊢[PRAAx]
    le (fact L*numerator X K (succ i)*denominator X K i)
      (fact L*numerator X K i*denominator X K (succ i)+
        quo (fact L) (X+i)*denominator X K i*denominator X K (succ i)) ⋏
    le (fact L*G*numerator X K i*denominator X K (succ i)+
        G*quo (fact L) (X+succ i)*denominator X K i*denominator X K (succ i))
      (fact L*G*numerator X K (succ i)*denominator X K i+
        quo (fact L) (X+i)*denominator X K i*denominator X K (succ i)) := by
  let a := X+i
  let b := X+succ i
  let n := numerator X K i
  let d := denominator X K i
  let n' := numerator X K (succ i)
  let d' := denominator X K (succ i)
  have ha : Γ ⊢[PRAAx] le one a := le_trans hX (le_add_right _ _)
  have hb : Γ ⊢[PRAAx] le one b := le_trans hX (le_add_right _ _)
  have ea := natEq (GammaEulerMesh.factorial_quotient a L ha
    (le_trans (add_le_add₂ (le_refl X) (le_succ_self i)) hi))
  have eb := natEq (GammaEulerMesh.factorial_quotient b L hb hi)
  dsimp only [a,b] at ea eb
  refine .andI ?_ ?_
  · ipra_le 𝔞 (quo (fact L) (X+i))*sl (upper_step X K i hX) using linear_combination (𝔞 n'*𝔞 d-𝔞 n*𝔞 d')*ea
  · have hab : Γ ⊢[PRAAx] le one ((X+i)*(X+succ i)) := positive_product ha hb
    apply cancel_pos hab
    ipra_le 𝔞 (fact L)*sl (lower_step X G K i hX hK hpow) using
      linear_combination (𝔞 X+𝔞 i+1)*𝔞 d*𝔞 d'*ea-(𝔞 X+𝔞 i)*𝔞 G*𝔞 d*𝔞 d'*eb

end LeanProofs.IPRA.Analysis.GaussianStirlingOddGrid
