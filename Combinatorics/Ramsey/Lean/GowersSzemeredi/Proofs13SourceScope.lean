import GowersSzemeredi.Proofs13Basic

/-! The zero endpoint and negative-sign obstruction for Section13's
vertical-correlation additivity estimates. The obstruction uses a prime
modulus, so it also respects the paper's standing convention. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

def lemma_13_1_unrestricted_alpha : Prop :=
  ∀ (N : Nat) [NeZero N] (f : Pair N → Complex) (B : Finset (ZMod N))
      (sigma : ZMod N → ZMod N) (alpha : Real),
    DiscValued f →
    alpha * (N : Real) ^ 5 ≤
      ∑ h ∈ B, ‖fourier (verticalCorrelation f h) (sigma h)‖ ^ 2 →
    alpha ^ 4 * (N : Real) ^ 3 ≤ phiAdditiveCount B sigma

def lemma_13_1_nonnegative_alpha : Prop :=
  ∀ (N : Nat) [NeZero N] (f : Pair N → Complex) (B : Finset (ZMod N))
      (sigma : ZMod N → ZMod N) (alpha : Real),
    0 ≤ alpha → DiscValued f →
    alpha * (N : Real) ^ 5 ≤
      ∑ h ∈ B, ‖fourier (verticalCorrelation f h) (sigma h)‖ ^ 2 →
    alpha ^ 4 * (N : Real) ^ 3 ≤ phiAdditiveCount B sigma

def corollary_13_2_nonnegative_alpha : Prop :=
  ∀ (N : Nat) [NeZero N] (A : Finset (Pair N)) (B : Finset (ZMod N))
      (sigma : ZMod N → ZMod N) (alpha : Real),
    0 ≤ alpha → alpha * (N : Real) ^ 5 ≤
      ∑ h ∈ B, ‖fourier (verticalEdgeFiberFunction A h) (sigma h)‖ ^ 2 →
    alpha ^ 4 * (N : Real) ^ 3 ≤ phiAdditiveCount B sigma

def corollary_13_2_unrestricted_alpha : Prop :=
  ∀ (N : Nat) [NeZero N] (A : Finset (Pair N)) (B : Finset (ZMod N))
      (sigma : ZMod N → ZMod N) (alpha : Real),
    alpha * (N : Real) ^ 5 ≤
      ∑ h ∈ B, ‖fourier (verticalEdgeFiberFunction A h) (sigma h)‖ ^ 2 →
    alpha ^ 4 * (N : Real) ^ 3 ≤ phiAdditiveCount B sigma

/-- Empty domain and alpha=-1 refute the unrestricted sign reading even at N=2. -/
theorem lemma_13_1_negative_alpha_counterexample :
    ¬ lemma_13_1_unrestricted_alpha := by
  intro h
  have hbad := h 2 (fun _ => 0) ∅ (fun _ => 0) (-1)
    (by simp [DiscValued]) (by simp)
  norm_num [phiAdditiveCount, countWhere, IsPhiAdditive] at hbad

/-- The endpoint alpha=0 has a trivial nonnegative-count conclusion. -/
theorem lemma_13_1_nonnegative_alpha_holds : lemma_13_1_nonnegative_alpha := by
  intro N _ f B sigma alpha ha hf hlarge
  rcases eq_or_lt_of_le ha with hzero | hpos
  · subst alpha
    simp
  · exact lemma_13_1_holds N f B sigma alpha hpos hf hlarge

/-- The characteristic-function corollary has the same valid zero endpoint. -/
theorem corollary_13_2_nonnegative_alpha_holds : corollary_13_2_nonnegative_alpha := by
  intro N _ A B sigma alpha ha hlarge
  rcases eq_or_lt_of_le ha with hzero | hpos
  · subst alpha
    simp
  · exact corollary_13_2_holds N A B sigma alpha hpos hlarge

/-- The empty-set corollary likewise fails for negative alpha at the prime modulus two. -/
theorem corollary_13_2_negative_alpha_counterexample :
    ¬ corollary_13_2_unrestricted_alpha := by
  intro h
  have hbad := h 2 ∅ ∅ (fun _ => 0) (-1) (by simp)
  norm_num [phiAdditiveCount, countWhere, IsPhiAdditive] at hbad

end LeanProofs.GowersSzemeredi
