import IPRADerivations.Analysis.Gamma.Digamma.TwoShift.Rational.Windows.GaussianGammaDigammaTwoShiftRationalWindow

/-!
# Repairing cofinal two-shift charts at a closed window boundary

A common translation of the three observed arguments preserves both
shifts. Enlarging the observed shift bound by three error units repairs
the two closed shift inequalities. A further explicit translation
repairs the relative-error threshold, including equality in the
quadratic constraint.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftWindowBuffer

open_ipra
open GaussianGammaDigammaTwoShiftRationalWindow (input coefficient)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def enlarged (L e : PTm n) : PTm n := L+num 3*e

def translation (S T e : PTm n) : PTm n := (S+num 24*T+num 48)*e

def approximateWindow (a L y e : PTm n) : Fm PTm n :=
  le a (y+enlarged L e) ⋏ le y (a+enlarged L e)

def approximateInput (a b c d L e : PTm n) : Fm PTm n :=
  GaussianStirlingGammaLogarithm.source a b ⋏
    (le b (L+e) ⋏ (le (two*L+b) (a+num 3*e) ⋏ (approximateWindow a L c e ⋏ approximateWindow a L d e)))

def relativeInput (a b L e S T : PTm n) : Fm PTm n :=
  le e b ⋏ (le L (T*b) ⋏ le (coefficient b L) (a*b+S*e*b))

theorem repairs_window (a b c d L e u : PTm n) (hs : Γ ⊢[PRAAx] approximateInput a b c d L e)
    (hu : Γ ⊢[PRAAx] le (num 9*e) u) :
    Γ ⊢[PRAAx] input (a+u) b (c+u) (d+u) (enlarged L e) := by
  have hb := hs.andE₁.andE₂
  have ha := le_trans hs.andE₁.andE₁ (le_add_right a u)
  have low := hs.andE₂.andE₁
  have base := hs.andE₂.andE₂.andE₁
  have left := hs.andE₂.andE₂.andE₂.andE₁
  have right := hs.andE₂.andE₂.andE₂.andE₂
  refine .andI (.andI ha hb) (.andI ?_ (.andI ?_ (.andI (.andI ?_ ?_) (.andI ?_ ?_))))
  · unfold enlarged
    ipra_le sl low+2*𝔞 e
  · unfold enlarged
    ipra_le sl base+sl hu
  · ipra_le sl left.andE₁
  · ipra_le sl left.andE₂
  · ipra_le sl right.andE₁
  · ipra_le sl right.andE₂

theorem repairs_relative_threshold (a b L e S T : PTm n) (hs : Γ ⊢[PRAAx] relativeInput a b L e S T) :
    Γ ⊢[PRAAx] le (coefficient b (enlarged L e)) ((a+translation S T e)*b) := by
  have small := hs.andE₁
  have cap := hs.andE₂.andE₁
  have size := hs.andE₂.andE₂
  change Γ ⊢[PRAAx] le (num 4*L*(L+b)) (a*b+S*e*b) at size
  unfold coefficient enlarged translation
  ipra_le sl size+24*𝔞 e*sl cap+36*𝔞 e*sl small

theorem repairs_relative_window (a b c d L e S T : PTm n)
    (hs : Γ ⊢[PRAAx] approximateInput a b c d L e) (hr : Γ ⊢[PRAAx] relativeInput a b L e S T) :
    Γ ⊢[PRAAx] input (a+translation S T e) b (c+translation S T e) (d+translation S T e) (enlarged L e) ⋏
      le (coefficient b (enlarged L e)) ((a+translation S T e)*b) := by
  refine .andI (repairs_window a b c d L e (translation S T e) hs ?_) (repairs_relative_threshold a b L e S T hr)
  unfold translation
  ipra_le 𝔞 S*𝔞 e+24*𝔞 T*𝔞 e+39*𝔞 e

theorem actual_two_shift_logarithmic_window_buffer_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (approximateInput (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
        input (var 0+num 9*var 5) (var 1) (var 2+num 9*var 5) (var 3+num 9*var 5) (enlarged (var 4) (var 5))) :=
  closeUniv 6 (.impI (repairs_window _ _ _ _ _ _ _ Prf.hyp0 (le_refl _)))

theorem actual_two_shift_relative_window_buffer_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (approximateInput (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
        relativeInput (var 0) (var 1) (var 4) (var 5) (var 6) (var 7) ⟶
        input (var 0+translation (var 6) (var 7) (var 5)) (var 1)
          (var 2+translation (var 6) (var 7) (var 5)) (var 3+translation (var 6) (var 7) (var 5)) (enlarged (var 4) (var 5)) ⋏
          le (coefficient (var 1) (enlarged (var 4) (var 5))) ((var 0+translation (var 6) (var 7) (var 5))*var 1)) :=
  closeUniv 8 (.impI (.impI (repairs_relative_window _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftWindowBuffer
