import IPRADerivations.Analysis.GaussianHarmonicQuadraticTangent
import IPRADerivations.Analysis.RationalValueBounds
import IPRADerivations.Analysis.GaussianGammaEulerRationalHeadConvexity

/-!
# The weighted sharp quadratic harmonic logarithm gap

The barycenter is read on the shared factorial mesh. Its left and
right tangent terms cancel with the original natural weights. The
remaining quadratic terms give the strong-concavity coefficient
and a single explicit endpoint correction.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianHarmonicWeightedQuadratic

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianGammaEulerRationalHeadConvexity (barycenter weight)
open GaussianHarmonicQuadraticTangent (tangents upperTangent lowerTangent scale)
open GaussianRationalHorner (positive_product)
open Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def squareDen (B r s : PTm n) : PTm n := two*weight r s*B*B
def gapNumerator (a d r s : PTm n) : PTm n := succ r*s*monus d a*monus d a
def meshError (a d r s : PTm n) : PTm n := succ r*s*monus d a

@[simp] theorem subst_squareDen {m : ℕ} (σ : Fin n → PTm m) (B r s : PTm n) :
    Syn.subst σ (squareDen B r s) = squareDen (Syn.subst σ B) (Syn.subst σ r) (Syn.subst σ s) := by simp [squareDen,weight]
@[simp] theorem subst_gapNumerator {m : ℕ} (σ : Fin n → PTm m) (a d r s : PTm n) :
    Syn.subst σ (gapNumerator a d r s) = gapNumerator (Syn.subst σ a) (Syn.subst σ d) (Syn.subst σ r) (Syn.subst σ s) := by simp [gapNumerator]
@[simp] theorem subst_meshError {m : ℕ} (σ : Fin n → PTm m) (a d r s : PTm n) :
    Syn.subst σ (meshError a d r s) = meshError (Syn.subst σ a) (Syn.subst σ d) (Syn.subst σ r) (Syn.subst σ s) := by simp [meshError]

def weightedValue (a d Q L r s : PTm n) : PTm n :=
  succ r*S (Q*(weight r s*a)) (fact L)+s*S (Q*(weight r s*d)) (fact L)

def centerValue (a d Q L r s : PTm n) : PTm n := weight r s*S (Q*barycenter a d r s) (fact L)

def finiteGap (a d B Q L r s : PTm n) : Fm PTm n :=
  le (Q*squareDen B r s*weightedValue a d Q L r s+Q*fact L*gapNumerator a d r s)
    (Q*squareDen B r s*centerValue a d Q L r s+fact L*meshError a d r s)

theorem finite_gap (a d B Q L r s : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (had : Γ ⊢[PRAAx] le a d) (hdB : Γ ⊢[PRAAx] le d B) (hQ : Γ ⊢[PRAAx] le one Q)
    (hL : Γ ⊢[PRAAx] le (Q*(weight r s*B)) L) : Γ ⊢[PRAAx] finiteGap a d B Q L r s := by
  let R := succ r
  let W := weight r s
  let C := barycenter a d r s
  let F := fact L
  let X := Q*(W*a)
  let Y := Q*(W*d)
  let U := Q*C
  let M := Q*(W*B)
  let J := Q*s*monus d a
  let T := Q*R*monus d a
  let K := scale M
  let A := R*S X F+s*S Y F
  let Z := W*S U F
  let g := gapNumerator a d r s
  let e := meshError a d r s
  have eqD := natEq (eq_add_of_le had)
  have eqX : Γ ⊢[PRAAx] X+J ≐ U := by
    dsimp [X,J,U,C,W,weight,barycenter]
    apply deriveNat
    ipra_simps
    linear_combination -(𝔞 Q*𝔞 s)*eqD
  have eqY : Γ ⊢[PRAAx] U+T ≐ Y := by
    dsimp [U,T,Y,C,W,R,weight,barycenter]
    apply deriveNat
    ipra_simps
    linear_combination -(𝔞 Q*(𝔞 r+1))*eqD
  have eqW : Γ ⊢[PRAAx] W ≐ R+s := by dsimp [W,R,weight]; ipra_ring
  have hU : Γ ⊢[PRAAx] le one U := positive_product _ _ hQ
    (le_trans (positive_product _ _ (zero_lt_succ _) ha) (le_add_right _ _))
  have hW : Γ ⊢[PRAAx] le one W := zero_lt_succ _
  have hY : Γ ⊢[PRAAx] le Y M :=
    le_mul_mono (le_refl Q) (le_mul_mono (le_refl W) hdB)
  have huY : Γ ⊢[PRAAx] le U Y :=
    le_congr (.eqRefl _) eqY (le_add_right _ _)
  have fromX := (tangents J X U M L (le_trans huY hY) hL (le_congr eqX.eqSymm (.eqRefl _) (le_refl U))).andE₂
  have toY := (tangents T U Y M L hY hL (le_congr eqY.eqSymm (.eqRefl _) (le_refl Y))).andE₁
  have eX := natEq eqX
  have eY := natEq eqY
  have ew := natEq eqW
  have eSX := natEq (congrAp2 (sumF hB) eqX (.eqRefl F))
  have eSY := natEq (congrAp2 (sumF hB) eqY (.eqRefl F))
  have eJT := natEq (by dsimp only [J,T]; ipra_ring : Γ ⊢[PRAAx] R*J ≐ s*T)
  have aux : Γ ⊢[PRAAx] le (U*(K*A+F*(R*J*J+s*T*T))) (U*(K*Z+F*R*J)) := by
    dsimp only [lowerTangent,upperTangent] at fromX toY
    ipra_le 𝔞 R*sl fromX+𝔞 s*sl toY using
      dsimp only [A,Z,F,K] at ⊢
      dsimp only [F] at eSX eSY
      simp only [IPRA.Q.mk_add,IPRA.Q.mk_mul,map_add,map_mul]
      rw [eSX,eSY,ew]
      linear_combination 𝔞 (scale M)*𝔞 (fact L)*eJT-
        2*𝔞 R*𝔞 U*𝔞 (fact L)*𝔞 J*eX
  have normalized := RationalValueBounds.positive_cancel hU aux
  have hi : Γ ⊢[PRAAx] le (F*R*J) (F*R*J*W) := by
    exact le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (F*R*J) hW)
  have longer : Γ ⊢[PRAAx] le (K*A+F*(R*J*J+s*T*T)) (K*Z+F*R*J*W) :=
    le_trans normalized (le_congr (by ipra_ring) (by ipra_ring) (add_le_add_right (K*Z) hi))
  have final : Γ ⊢[PRAAx] le ((Q*W)*(Q*squareDen B r s*A+Q*F*g))
      ((Q*W)*(Q*squareDen B r s*Z+F*e)) := by
    apply le_congr _ _ longer
    · dsimp only [K,scale,M,J,T,g,gapNumerator,squareDen,W,R]
      apply deriveNat
      ipra_simps
      dsimp only [W,R] at ew
      ipra_simps
      rw [ew]
      ring
    · dsimp [K,scale,M,J,e,meshError,squareDen,W,R]
      ipra_ring
  exact RationalValueBounds.positive_cancel (positive_product _ _ hQ hW) final

end LeanProofs.IPRA.Analysis.GaussianHarmonicWeightedQuadratic
