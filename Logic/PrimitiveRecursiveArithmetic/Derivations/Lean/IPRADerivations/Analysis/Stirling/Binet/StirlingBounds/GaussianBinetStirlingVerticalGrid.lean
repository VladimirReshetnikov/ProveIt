import IPRADerivations.Analysis.Stirling.Binet.StirlingBounds.GaussianBinetStirlingVerticalRate

/-!
# Accumulation of the original Stirling estimates over a vertical grid

At an internal grid count the real part is fixed. Every row is read
from its literal common-denominator chart. Quantifier-free induction
accumulates the independent local bounds at one requested clock.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianBinetStirlingVerticalGrid

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ComplexLogarithmRemainder (normSq)
open GaussianBinetStirlingRemainder (nameF data subst_data offset)
open GaussianBinetStirlingVerticalRate (leadingNumerator leadingDenominator)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianNamedInverseRate (diagonal_rate)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same)
open GaussianRationalHorner (positive_product ofGaussian_represents)
open GaussianRationalMetric (bounded bounded_of_cleared distanceBounded)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianRationalReciprocal (bounded_difference)
open GaussianRightHalfPlaneLogarithm (source)
open GaussianRightHalfPlaneLogarithmIncrementMargin (smallStep)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def size (A B : PTm n) : PTm n := two*(A+B)
def offsetRadius (A B : PTm n) : PTm n := A+B+one
def requiredMesh (A B D : PTm n) : PTm n := one+B+num 128*B*(size A B+one)*(D*D)

def sample (p A B D sign x M j : PTm n) : PTm n :=
  ap2 nameF p (data (M*A) (j*B) (M*D) sign x)

def rowNumerator (p A B D M : PTm n) : PTm n :=
  leadingNumerator (M*A) (M*D) B D (offsetRadius A B)*unit p+
    two*leadingDenominator (M*A) (M*D)
def rowDenominator (p A D M : PTm n) : PTm n := leadingDenominator (M*A) (M*D)*unit p

ipra_subst requiredMesh [size, one, two]
ipra_subst sample

theorem mesh_positive (A B D M : PTm n) (h : Γ ⊢[PRAAx] le (requiredMesh A B D) M) :
    Γ ⊢[PRAAx] le one M :=
  le_trans (le_trans (le_add_right one B) (le_add_right (one+B) _)) h

theorem row_denominator_positive (p A B D sign M : PTm n) (h : Γ ⊢[PRAAx] source A D sign)
    (hm : Γ ⊢[PRAAx] le (requiredMesh A B D) M) : Γ ⊢[PRAAx] le one (rowDenominator p A D M) := by
  have hM := mesh_positive A B D M hm
  have ha := positive_product M A hM h.andE₁.andE₁
  have hd := positive_product M D hM h.andE₂
  exact positive_product _ _ (positive_product _ _ (positive_product two _ (le_succ_self one) ha)
    (positive_product _ _ hd hd)) (unit_positive p)

private theorem offset_bound (A B D sign M j : PTm n) (h : Γ ⊢[PRAAx] source A D sign)
    (hM : Γ ⊢[PRAAx] le one M) (hj : Γ ⊢[PRAAx] le j M) :
    Γ ⊢[PRAAx] bounded (offset (M*A) (j*B) (M*D) sign) (offsetRadius A B) one := by
  let a := M*A
  let b := j*B
  let d := M*D
  let z := native a b sign
  let Q := A+B
  have hd := positive_product M D hM h.andE₂
  have hb : Γ ⊢[PRAAx] le b (M*B) := mul_le_mul_right B hj
  have hsq := le_mul_mono hb hb
  have margin : Γ ⊢[PRAAx] le (M*Q) (Q*d) := by
    dsimp only [d]
    ipra_le 𝔞(M)*𝔞(Q)*sl h.andE₂
  have hh : Γ ⊢[PRAAx] le (a*a+b*b) (Q*Q*(d*d)) :=
    le_trans (by dsimp only [a,Q]; ipra_le 2*𝔞(M)^2*𝔞(A)*𝔞(B)+sl hsq)
      (le_congr (.eqRefl _) (by ipra_ring) (le_mul_mono margin margin))
  have hz : Γ ⊢[PRAAx] bounded (argument a b d sign) Q one := by
    apply bounded_of_cleared _ z d Q one hd (le_refl one) (ofGaussian_represents z d hd)
    exact le_congr (by ipra_ring) (.eqRefl _)
      (le_congr (GaussianLogGammaEulerResidualRadius.native_norm a b sign h.andE₁.andE₂).eqSymm (.eqRefl _) hh)
  have ht : Γ ⊢[PRAAx] le one two := le_succ_self one
  have half := GaussianEulerExponentCompactBounds.fraction_bound (Γ := Γ) one two one ht
    (by ipra_le 1)
  have raw := bounded_difference (argument a b d sign) (fraction one two) Q one one one
    (le_refl one) (le_refl one) hz half
  exact bounded_radius_mono _ _ _ _ _ (positive_product one one (le_refl one) (le_refl one))
    (le_refl one) (by dsimp only [Q,offsetRadius]; ipra_le 0) raw

theorem row_distance (p A B D sign x M j : PTm n) (h : Γ ⊢[PRAAx] source A D sign)
    (hm : Γ ⊢[PRAAx] le (requiredMesh A B D) M) (hj : Γ ⊢[PRAAx] lt j M) :
    Γ ⊢[PRAAx] distanceBounded (sample p A B D sign x M (succ j)) (sample p A B D sign x M j)
      (rowNumerator p A B D M) (rowDenominator p A D M) := by
  let a := M*A
  let b := j*B
  let d := M*D
  let C := size A B
  let W := offsetRadius A B
  have hM := mesh_positive A B D M hm
  have ha := positive_product M A hM h.andE₁.andE₁
  have hd := positive_product M D hM h.andE₂
  have src : Γ ⊢[PRAAx] source a d sign := .andI (.andI ha h.andE₁.andE₂) hd
  have margin : Γ ⊢[PRAAx] le d (D*a) := by
    dsimp only [d,a]
    ipra_le 𝔞(M)*𝔞(D)*sl h.andE₁.andE₁
  have hsucc : Γ ⊢[PRAAx] le (succ j) M := hj
  have hc : Γ ⊢[PRAAx] le (a+b+a+(b+B)) (C*d) := by
    dsimp only [a,b,C,size,d]
    ipra_le 𝔞(B)*(sl (le_of_lt hj)+sl hsucc)+2*𝔞(M)*𝔞(A+B)*sl h.andE₂
  have hs : Γ ⊢[PRAAx] smallStep B D C d := by
    unfold smallStep
    have e : Γ ⊢[PRAAx] le (num 128*B*(C+one)*(D*D)) M :=
      le_trans (le_add_left _ (one+B)) hm
    exact le_trans e (by dsimp only [d]; ipra_le 𝔞(M)*sl h.andE₂)
  have hB : Γ ⊢[PRAAx] le B d :=
    le_trans (le_trans (le_add_left B one) (le_trans (le_add_right (one+B) _) hm))
      (by dsimp only [d]; ipra_le 𝔞(M)*sl h.andE₂)
  have hW := offset_bound A B D sign M j h hM (le_of_lt hj)
  have eB : Γ ⊢[PRAAx] b+B ≐ succ j*B := by dsimp only [b]; ipra_ring
  have e : Γ ⊢[PRAAx] data a (b+B) d sign x ≐ data a (succ j*B) d sign x := by
    simpa only [subst_data,Syn.inst_zero,Syn.subst_inst_shift,Syn.subst_var] using
      Prf.eqCongr1 (data (Syn.shift a) (var 0) (Syn.shift d) (Syn.shift sign) (Syn.shift x)) eB
  have hN := positive_product _ _ (positive_product two a (le_succ_self one) ha) (positive_product d d hd hd)
  exact distance_congr (congrAp2 nameF (.eqRefl p) e) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (diagonal_rate nameF nameF _ _ (leadingNumerator a d B D W) (leadingDenominator a d) p hN
      (GaussianBinetStirlingVerticalRate.independent_rate a b d sign B D C W x src h.andE₂ margin hc hs hB hW))

private def prefixLaw (p A B D sign x M C Q j : PTm n) : Fm PTm n :=
  le j M ⟶ distanceBounded (sample p A B D sign x M j) (sample p A B D sign x M zero) (C*j) Q

@[simp] private theorem subst_prefixLaw {m : ℕ} (σ : Fin n → PTm m) (p A B D sign x M C Q j : PTm n) :
    (prefixLaw p A B D sign x M C Q j).subst σ =
      prefixLaw (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ sign)
        (Syn.subst σ x) (Syn.subst σ M) (Syn.subst σ C) (Syn.subst σ Q) (Syn.subst σ j) := by
  simp [prefixLaw]

theorem grid_distance (p A B D sign x M : PTm n) (h : Γ ⊢[PRAAx] source A D sign)
    (hm : Γ ⊢[PRAAx] le (requiredMesh A B D) M) :
    Γ ⊢[PRAAx] distanceBounded (sample p A B D sign x M M) (sample p A B D sign x M zero)
      (rowNumerator p A B D M*M) (rowDenominator p A D M) := by
  let C := rowNumerator p A B D M
  let Q := rowDenominator p A D M
  let s (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have hQ := row_denominator_positive p A B D sign M h hm
  have hs : Δ ⊢[PRAAx] source (s A) (s D) (s sign) := by simpa [s,Δ,Fm.shift,Syn.shift,source,GaussianRightHalfPlaneArgument.source] using h.shift
  have ms : Δ ⊢[PRAAx] le (requiredMesh (s A) (s B) (s D)) (s M) := by simpa [s,Δ,Fm.shift,Syn.shift] using hm.shift
  have Cs : s C = rowNumerator (s p) (s A) (s B) (s D) (s M) := by
    simp [s,Syn.shift,C,rowNumerator,leadingNumerator,leadingDenominator,offsetRadius,GaussianBinetStirlingVerticalRate.quadraticCost,one,two]
  have Qs : s Q = rowDenominator (s p) (s A) (s D) (s M) := by
    simp [s,Syn.shift,Q,rowDenominator,leadingDenominator,two]
  let form := prefixLaw (s p) (s A) (s B) (s D) (s sign) (s x) (s M) (s C) (s Q) (var 0)
  have all : Γ ⊢[PRAAx] .all form := by
    refine PRA.qfInd _ (by unfold form prefixLaw; exact ⟨trivial,trivial⟩) ?_ ?_
    · simp only [form,subst_prefixLaw,Syn.subst_var,Syn.inst_zero,s,Syn.subst_inst_shift]
      refine .impI ?_
      exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
        (distance_refl_zero (sample p A B D sign x M zero) Q hQ.wk)
    · simp only [form,subst_prefixLaw,Syn.subst_var,Syn.repl_zero,s,subst_repl_shift]
      refine .impI ?_
      have hj : (le (succ (var 0)) (s M) :: form :: Δ) ⊢[PRAAx] lt (var 0) (s M) := Prf.hyp0
      have hprev : (le (succ (var 0)) (s M) :: form :: Δ) ⊢[PRAAx]
          distanceBounded (sample (s p) (s A) (s B) (s D) (s sign) (s x) (s M) (var 0))
            (sample (s p) (s A) (s B) (s D) (s sign) (s x) (s M) zero) (s C*var 0) (s Q) :=
        (Prf.hyp0 (Γ := Δ) (φ := form)).wk.impE (le_of_lt hj)
      have row := row_distance (s p) (s A) (s B) (s D) (s sign) (s x) (s M) (var 0) hs.wk.wk ms.wk.wk hj
      have hpos := row_denominator_positive (Γ := le (succ (var 0)) (s M) :: form :: Δ) (s p) (s A) (s B) (s D) (s sign) (s M) hs.wk.wk ms.wk.wk
      change (le (succ (var 0)) (s M) :: form :: Δ) ⊢[PRAAx] distanceBounded _ _ (s C*succ (var 0)) (s Q)
      rw [Cs,Qs] at hprev ⊢
      exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
        (distance_triangle_same _ _ _ _ _ _ hpos row hprev)
  have inst : Γ ⊢[PRAAx] prefixLaw p A B D sign x M C Q M := by
    simpa only [form,subst_prefixLaw,Syn.subst_var,Syn.inst_zero,s,Syn.subst_inst_shift] using all.allE M
  exact inst.impE (le_refl M)

end LeanProofs.IPRA.Analysis.GaussianBinetStirlingVerticalGrid
