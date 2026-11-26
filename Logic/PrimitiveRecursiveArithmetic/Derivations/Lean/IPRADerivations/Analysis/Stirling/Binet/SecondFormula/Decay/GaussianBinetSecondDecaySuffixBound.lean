import IPRADerivations.Analysis.Stirling.Binet.SecondFormula.Decay.GaussianBinetSecondDecaySharedTail
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.GaussianRationalSuffixMask
import IPRADerivations.Analysis.Euler.VerticalBounds.GaussianEulerNamedUpperTail

/-!
# The original frozen-row majorant bounds any time suffix

Mask the first cells with Gaussian zero before applying the full
nonnegative scalar envelope. The mask reads exactly the original
offset sum and leaves the denominator and mesh width unchanged.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBinetSecondDecaySuffixBound

open_ipra
open GaussianBinetSecondDecayFinite (terms_majorized dominated_bound)
open GaussianBinetSecondDecayGrid (rowData rowBody envelopeData envelopeBody)
open GaussianBinetSecondDecayFrozenTail (mesh mesh_bounds clock_bounds)
open GaussianBinetSecondDecaySharedTail (clockFloor)
open GaussianBinetSecondDecayPointwise (frozenPiNumerator frozen_pi_rate)
open GaussianCoefficientNameBounds (unit)
open GaussianRationalFiniteSum (sum sum_index_congr)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalRiemannRefinement (leftSum weight)
open GaussianRationalSumMajorant (majorized termsMajorized term_majorized_at majorized_congr)
open GaussianRationalSuffixMask (omitted retained suffix)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRightHalfPlaneLogarithm (source)
open GaussianStirlingConstant (piDenominator)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def value (p N S L T H J X Y D sign : PTm n) : PTm n :=
  qmul (weight T one N) (sum (offB rowBody) L (pairT S (rowData p N T H J X Y D sign)))

private theorem masked_majorants (f g : PTm 2) (S N x y : PTm n)
    (h : Γ ⊢[PRAAx] termsMajorized f g N x y) : Γ ⊢[PRAAx]
    termsMajorized (GaussianRationalSuffixMask.body f) g N (pairT S x) y := by
  refine .allI (.impI ?_)
  let s (v : PTm n) := Syn.shift v
  let i : PTm (n+1) := var 0
  let Δ := lt i (s N)::Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] termsMajorized f g (s N) (s x) (s y) := by
    simpa only [Δ,s,Fm.shift,Syn.shift,GaussianRationalSumMajorant.subst_termsMajorized] using h.shift.wk
  have original := term_majorized_at f g (s N) (s x) (s y) i hs Prf.hyp0
  have mask : Δ ⊢[PRAAx] majorized (inst2 (GaussianRationalSuffixMask.body f) i (pairT (s S) (s x))) (inst2 g i (s y)) := by
    refine .orE (lt_or_le i (s S)) ?_ ?_
    · have pos := RationalArgmin.denominator_positive (Γ := (lt i (s S))::Δ) (inst2 g i (s y))
      exact majorized_congr (omitted f (s S) i (s x) Prf.hyp0).eqSymm (.eqRefl _)
        (.andI original.wk.andE₁ (GaussianEulerNamedUpperTail.zero_bound _ _ pos))
    · exact majorized_congr (retained f (s S) i (s x) Prf.hyp0).eqSymm (.eqRefl _) original.wk
  simpa only [termsMajorized,s,i,Δ,Syn.shift,subst_pairT] using mask

theorem window_bound (p N S L T H J m K X Y D sign : PTm n)
    (hz : Γ ⊢[PRAAx] source X D sign) (hN : Γ ⊢[PRAAx] le one N) (hT : Γ ⊢[PRAAx] le one T)
    (hJ : Γ ⊢[PRAAx] le one J) (hm : Γ ⊢[PRAAx] le one m) (hr : Γ ⊢[PRAAx] le (m*J) H)
    (hK : Γ ⊢[PRAAx] le D (K*X)) (hs : Γ ⊢[PRAAx] N ≐ S+L)
    (hstep : Γ ⊢[PRAAx] le (H*T) (J*N))
    (hmesh : Γ ⊢[PRAAx] le (num 3*((H*T)*(H*T))) N) (hclock : Γ ⊢[PRAAx] le (num 20*N) (unit p))
    (hrow : Γ ⊢[PRAAx] le (two*(T*N*H)) (unit p))
    (hslack : Γ ⊢[PRAAx] le ((m*m)*T*(num 8+num 10*T)) (unit p)) : Γ ⊢[PRAAx]
    bounded (value p N S L T H J X Y D sign) (num 11*K) (m*m) := by
  let f := GaussianRationalSuffixMask.body rowBody
  let x := rowData p N T H J X Y D sign
  let w := weight T one N
  have rows := masked_majorants _ _ S N _ _ (terms_majorized p N T H J m K X Y D sign hz hN hJ hm hr hK hrow)
  have estimate := dominated_bound f (pairT S x) p N T H J m K hN hT hJ hm hr hstep hmesh hclock hslack rows
  have e : Γ ⊢[PRAAx] leftSum f N (pairT S x) T one ≐ value p N S L T H J X Y D sign :=
    qmul_congr (.eqRefl w) ((sum_index_congr f hs (.eqRefl _)).eqTrans (suffix rowBody S L x))
  exact bound_congr e (.eqRefl _) (.eqRefl _) estimate

theorem frozen_window_bound (q N S L T M k m K X Y D sign : PTm n)
    (hz : Γ ⊢[PRAAx] source X D sign) (hT : Γ ⊢[PRAAx] le one T)
    (hm : Γ ⊢[PRAAx] le one m) (hM : Γ ⊢[PRAAx] le m M) (hK : Γ ⊢[PRAAx] le D (K*X))
    (hs : Γ ⊢[PRAAx] N ≐ S+L) (hn : Γ ⊢[PRAAx] le (mesh T M k) N)
    (hq : Γ ⊢[PRAAx] le (clockFloor N T M k) (unit q)) : Γ ⊢[PRAAx]
    bounded (value q N S L T (frozenPiNumerator m k) (piDenominator k) X Y D sign) (num 11*K) (m*m) := by
  have rate := frozen_pi_rate (Γ := Γ) m k
  have meshBound := mesh_bounds N T M k m hM hn
  have clockBound := clock_bounds q N T M k m hM hq
  exact window_bound q N S L T _ _ m K X Y D sign hz meshBound.andE₁ hT rate.andE₁ hm rate.andE₂ hK hs
    meshBound.andE₂.andE₁ meshBound.andE₂.andE₂ clockBound.andE₁ clockBound.andE₂.andE₁ clockBound.andE₂.andE₂



end LeanProofs.IPRA.Analysis.GaussianBinetSecondDecaySuffixBound
