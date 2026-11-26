import IPRADerivations.Analysis.GaussianGammaDigammaTwoShiftNamedCap
import IPRADerivations.Analysis.GaussianGammaHalfWallisRate

/-!
# The exact cap converges under the closed-window chart repair

Increasing the shift radius by three error units and translating the
base changes the literal rational cap by a fixed multiple of the
common chart pitch. The estimate uses only the original inverse margin
and upper bound of the shift name.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftCapRepair

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF)
open GaussianGammaDigammaTwoShiftRationalWindow (coefficient)
open GaussianGammaDigammaTwoShiftWindowBuffer (enlarged)
open GaussianNamedInverseRate (independentRate)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianStirlingGammaLogarithm (source)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def quadraticBudget (T : PTm n) : PTm n := num 24*T+num 48
def capBudget (T : PTm n) : PTm n := num 4*T*(T+one)
def gain (E T J : PTm n) : PTm n := quadraticBudget T*E+capBudget T*E*E*J

def cap (a b L : PTm n) : PTm n := fraction (coefficient b L) (a*b)

@[simp] theorem subst_gain {m : ℕ} (σ : Fin n → PTm m) (E T J : PTm n) :
    Syn.subst σ (gain E T J) = gain (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ J) := by
  simp [gain,quadraticBudget,capBudget,one]
@[simp] theorem subst_cap {m : ℕ} (σ : Fin n → PTm m) (a b L : PTm n) :
    Syn.subst σ (cap a b L) = cap (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ L) := by
  simp [cap]

theorem coefficient_growth (b L e T : PTm n) (he : Γ ⊢[PRAAx] le e b)
    (hL : Γ ⊢[PRAAx] le L (T*b)) :
    Γ ⊢[PRAAx] le (coefficient b (enlarged L e)) (coefficient b L+quadraticBudget T*e*b) := by
  unfold coefficient enlarged quadraticBudget
  ipra_le 24*𝔞 e*sl hL+36*𝔞 e*sl he

theorem coefficient_bound (b L T : PTm n) (hL : Γ ⊢[PRAAx] le L (T*b)) :
    Γ ⊢[PRAAx] le (coefficient b L) (capBudget T*b*b) := by
  have upper : Γ ⊢[PRAAx] le (L+b) ((T+one)*b) := by ipra_le sl hL
  unfold coefficient capBudget
  ipra_le 4*𝔞(L+b)*sl hL+4*𝔞 T*𝔞 b*sl upper

theorem repaired_distance (a b L e u E T J : PTm n) (ha : Γ ⊢[PRAAx] source a b)
    (hE : Γ ⊢[PRAAx] le b (E*a)) (he : Γ ⊢[PRAAx] le e b) (hL : Γ ⊢[PRAAx] le L (T*b))
    (hu : Γ ⊢[PRAAx] le u (J*e)) :
    Γ ⊢[PRAAx] distanceBounded (cap a b L) (cap (a+u) b (enlarged L e)) (gain E T J*e) b := by
  let K := coefficient b L
  let K' := coefficient b (enlarged L e)
  let H := quadraticBudget T
  let Q := capBudget T
  have hb := ha.andE₂
  have hp := positive_product _ _ ha.andE₁ hb
  have hp' := positive_product _ _ (le_trans ha.andE₁ (le_add_right a u)) hb
  have hE' : Γ ⊢[PRAAx] le b (E*(a+u)) := by ipra_le sl hE+𝔞 E*𝔞 u
  have hK := coefficient_bound b L T hL
  have growth := coefficient_growth b L e T he hL
  have mono : Γ ⊢[PRAAx] le K K' := by
    dsimp only [K,K',coefficient,enlarged]
    ipra_le 24*𝔞 L*𝔞 e+12*𝔞 b*𝔞 e+36*𝔞 e^2
  apply GaussianGammaHalfWallisRate.fraction_distance K (a*b) K' ((a+u)*b) (gain E T J*e) b hp hp' hb
  · change Γ ⊢[PRAAx] le K (Q*b*b) at hK
    unfold gain
    change Γ ⊢[PRAAx] le (b*(K*((a+u)*b)))
      (b*(K'*(a*b))+(H*E+Q*E*E*J)*e*(a*b)*((a+u)*b))
    ipra_le 𝔞(a*b*b)*sl mono+𝔞(u*b*b)*sl hK+𝔞(Q*b*b*b*b)*sl hu+
      𝔞(Q*J*e*b*b*b)*sl hE+𝔞(Q*J*e*b*b*E*a)*sl hE'+𝔞(H*E*e*a*(a+u)*b*b)
  · change Γ ⊢[PRAAx] le K' (K+H*e*b) at growth
    unfold gain
    change Γ ⊢[PRAAx] le (b*(K'*(a*b)))
      (b*(K*((a+u)*b))+(H*E+Q*E*E*J)*e*((a+u)*b)*(a*b))
    ipra_le 𝔞(a*b*b)*sl growth+𝔞(K*u*b*b)+𝔞(H*e*a*b*b)*sl hE'+
      𝔞(Q*E*E*J*e*(a+u)*a*b*b)

theorem repaired_rate (f : PR 2) (x A a b L e u E T J s : PTm n)
    (ha : Γ ⊢[PRAAx] source a b) (hE : Γ ⊢[PRAAx] le b (E*a)) (he : Γ ⊢[PRAAx] le e b)
    (hL : Γ ⊢[PRAAx] le L (T*b)) (hu : Γ ⊢[PRAAx] le u (J*e))
    (pitch : Γ ⊢[PRAAx] b ≐ e*unit s)
    (hr : Γ ⊢[PRAAx] independentRate f constantF x (cap a b L) A (unit s)) :
    Γ ⊢[PRAAx] independentRate f constantF x (cap (a+u) b (enlarged L e)) (A+gain E T J) (unit s) := by
  let C := gain E T J
  let U := unit s
  let c := cap a b L
  let d := cap (a+u) b (enlarged L e)
  have hU := unit_positive (Γ := Γ) s
  have raw := repaired_distance a b L e u E T J ha hE he hL hu
  have eq : Γ ⊢[PRAAx] C*e*U ≐ C*b := (by ipra_ring : Γ ⊢[PRAAx] C*e*U ≐ C*(e*U)).eqTrans (congrMul (.eqRefl _) pitch.eqSymm)
  have meter : Γ ⊢[PRAAx] distanceBounded c d C U :=
    distance_radius_mono _ _ _ _ _ _ ha.andE₂ hU (le_congr eq.eqSymm (.eqRefl _) (le_refl _)) raw
  exact GaussianNamedRateComposition.same_denominator f constantF constantF x c d A U C hU hr
    (GaussianNamedAddRate.constant_rate c d C U hU meter)

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftCapRepair
