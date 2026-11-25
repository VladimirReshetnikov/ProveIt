import IPRADerivations.Probability.ProductPower
import IPRADerivations.Probability.ExpectationCorollaries
import IPRADerivations.AnalyticNumberTheory.Valuation
import IPRADerivations.DiophantineNumberTheory.SquareArea
import IPRADerivations.Core.LinearCombination

/-!
# The weak law and Monte Carlo frequencies

Packet: `probability/expected_value_ipra_2026-11-16`, on the `r`-fold product law of
`Probability/ProductPower` (`T = ∑_t P_r`, `A = ∑_t P_r S_r`, `B = ∑_t P_r S_r²`, `W = ∑ w`, `S = ∑ w X`,
`Q = ∑ w X²`):

* `monte_carlo` (`thm:monte-carlo`): for an indicator `X` (`X² = X`), `W A = r S T` and
  `W² T B + r S² T² = W² A² + r W S T²`, i.e. `E[p̂_r] = p` and `Var(p̂_r) = p (1 − p)/r`;
* `dev_identity`: with the cleared deviation `D(t) = |W S_r(t) − r S| = r W |X̄ − μ|`,
  `T ∑_t P_r D² + r T² S² = r T² W Q`, i.e. `E[D²] = r T (W Q − S²)/T`;
* `weak_law` (`thm:weak-law`): for `W ≥ 1` and any threshold `C`,
  `C² ∑_t P_r [D ≥ C] + r T S² ≤ r T W Q`; with `C = r W ε` this is
  `P(|X̄ − μ| ≥ ε) ≤ σ² / (r ε²)`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.WeakLaw

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.ProductPower
open LeanProofs.IPRA.Probability.Expectation (Ew inst2_mul' geB inst2_geB chebyshev)
open LeanProofs.IPRA.Probability.Variance (ad ad_sq)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.Geometry.HypercubeSplit (le_cancel_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (pw_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.DiophantineNumberTheory.SquareArea (le_add_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

section Laws

variable (w X : PTm 2)

/-- `thm:monte-carlo`: for an indicator observable (`X² = X` on outcomes), `E[p̂] = p` and
`Var(p̂) = p (1 − p) / r`. -/
theorem monte_carlo {M x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (hX : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶
      (inst2 X (var 0) (Syn.shift x) * inst2 X (var 0) (Syn.shift x) ≐ inst2 X (var 0) (Syn.shift x)))) (r : PTm n) :
    Γ ⊢[PRAAx] (ap2 (sumF w) M x * At w X r M x ≐ r * ap2 (sumF (w * X)) M x * Tt w r M x) ⋏
      (ap2 (sumF w) M x * ap2 (sumF w) M x * (Tt w r M x * Bt w X r M x) +
          r * (ap2 (sumF (w * X)) M x * ap2 (sumF (w * X)) M x) * (Tt w r M x * Tt w r M x) ≐
        ap2 (sumF w) M x * ap2 (sumF w) M x * (At w X r M x * At w X r M x) +
          r * ap2 (sumF w) M x * ap2 (sumF (w * X)) M x * (Tt w r M x * Tt w r M x)) := by
  have m := sample_moments (Γ := Γ) w X (x := x) hM r
  have qs : Γ ⊢[PRAAx] ap2 (sumF (w * (X * X))) M x ≐ ap2 (sumF (w * X)) M x := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_mul', inst2_mul', inst2_mul']
    exact congrMul (.eqRefl _) (Prf.impE hX.allOpen.wk Prf.hyp0)
  exact .andI (Prf.andE₁ m) ((Prf.andE₂ m).eqTrans (congrAdd (.eqRefl _) (congrMul (congrMul (.eqRefl _) qs) (.eqRefl _))))

/-! ## The deviation -/

/-- Selectors from `z = ⟨⟨K, ⟨R, C⟩⟩, p⟩`. -/
abbrev Kz : PTm 2 := fstT (fstT (var 1))
abbrev Rz : PTm 2 := fstT (sndT (fstT (var 1)))
/-- The threshold, as a function of the parameter. -/
abbrev Cz : PTm 1 := sndT (sndT (fstT (var 0)))

/-- `P_r(t)` at `snd z`. -/
abbrev wz : PTm 2 := sbp (TB w)
/-- The cleared deviation `|K S_r(t) − R|`. -/
abbrev dz : PTm 2 := ad (Kz * sbp (SB X)) Rz

/-- `P_r |K S_r − R|² + 2 K R P_r S_r`, which by `ad_sq` is `K² P_r S_r² + R² P_r`. -/
abbrev GB : PTm 2 := wz w * (dz X * dz X) + two * (Kz * Rz) * (wz w * sbp (SB X))

theorem sel_K {K R C p : PTm n} : Γ ⊢[PRAAx] fstT (fstT (pairT (pairT K (pairT R C)) p)) ≐ K :=
  (congrFst (fst_pair _ _)).eqTrans (fst_pair _ _)
theorem sel_R {K R C p : PTm n} : Γ ⊢[PRAAx] fstT (sndT (fstT (pairT (pairT K (pairT R C)) p))) ≐ R :=
  (congrFst ((congrSnd (fst_pair _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem sel_C {K R C p : PTm n} : Γ ⊢[PRAAx] sndT (sndT (fstT (pairT (pairT K (pairT R C)) p))) ≐ C :=
  (congrSnd ((congrSnd (fst_pair _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)

theorem wz_at (t K R C p : PTm n) : Γ ⊢[PRAAx] inst2 (wz w) t (pairT (pairT K (pairT R C)) p) ≐ inst2 (TB w) t p := by
  have e : inst2 (wz w) t (pairT (pairT K (pairT R C)) p) = inst2 (TB w) t (sndT (pairT (pairT K (pairT R C)) p)) := by
    simp only [inst2, wz, inst2_sbp]
  rw [e]; exact congrInst2 (TB w) (.eqRefl _) (snd_pair _ _)

theorem sb_at (t K R C p : PTm n) :
    Γ ⊢[PRAAx] Syn.subst ![t, pairT (pairT K (pairT R C)) p] (sbp (SB X)) ≐ inst2 (SB X) t p := by
  rw [inst2_sbp]; exact congrInst2 (SB X) (.eqRefl _) (snd_pair _ _)

theorem dz_at (t K R C p : PTm n) :
    Γ ⊢[PRAAx] inst2 (dz X) t (pairT (pairT K (pairT R C)) p) ≐ ad (K * inst2 (SB X) t p) R := by
  have e : inst2 (dz X) t (pairT (pairT K (pairT R C)) p) =
      ad (fstT (fstT (pairT (pairT K (pairT R C)) p)) * Syn.subst ![t, pairT (pairT K (pairT R C)) p] (sbp (SB X)))
        (fstT (sndT (fstT (pairT (pairT K (pairT R C)) p)))) := by
    simp only [inst2, dz, ad, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_fstT, subst_sndT]; simp
  rw [e]
  have a := congrMul (sel_K (Γ := Γ) (K := K) (R := R) (C := C) (p := p)) (sb_at X t K R C p)
  have b := sel_R (Γ := Γ) (K := K) (R := R) (C := C) (p := p)
  exact congrAdd (congrMonus a b) (congrMonus b a)

theorem GB_at (t K R C p : PTm n) : Γ ⊢[PRAAx] inst2 (GB w X) t (pairT (pairT K (pairT R C)) p) ≐
    K * K * inst2 (BB w X) t p + (R * R * inst2 (TB w) t p + zero * inst2 (AB w X) t p) := by
  have e : inst2 (GB w X) t (pairT (pairT K (pairT R C)) p) =
      inst2 (wz w) t (pairT (pairT K (pairT R C)) p) * (inst2 (dz X) t (pairT (pairT K (pairT R C)) p) *
        inst2 (dz X) t (pairT (pairT K (pairT R C)) p)) +
      two * (fstT (fstT (pairT (pairT K (pairT R C)) p)) * fstT (sndT (fstT (pairT (pairT K (pairT R C)) p)))) *
        (inst2 (wz w) t (pairT (pairT K (pairT R C)) p) * Syn.subst ![t, pairT (pairT K (pairT R C)) p] (sbp (SB X))) := by
    simp only [inst2, GB, PTm.subst_add, PTm.subst_mul, subst_fstT, subst_sndT]; simp
  rw [e, inst2_BB, inst2_AB]
  have w0 := wz_at (Γ := Γ) w t K R C p
  have d0 := dz_at (Γ := Γ) X t K R C p
  have s0 := sb_at (Γ := Γ) X t K R C p
  refine (congrAdd (congrMul w0 (congrMul d0 d0)) (congrMul (congrMul (.eqRefl _) (congrMul sel_K sel_R))
    (congrMul w0 s0))).eqTrans ?_
  ipra_lc 𝔞 (inst2 (TB w) t p) * natEq (ad_sq (Γ := Γ) (K * inst2 (SB X) t p) R)

/-- `∑_t P_r |K S_r − R|² + 2 K R A = K² B + R² T`. -/
theorem dev_sum (r M x K R C : PTm n) :
    Γ ⊢[PRAAx] Ew (wz w) (dz X * dz X) (pw M r) (pairT (pairT K (pairT R C)) (pairT r (pairT M x))) +
        two * (K * R) * At w X r M x ≐
      K * K * Bt w X r M x + (R * R * Tt w r M x + zero * At w X r M x) := by
  let z : PTm n := pairT (pairT K (pairT R C)) (pairT r (pairT M x))
  have hz : Syn.shift z = pairT (pairT (Syn.shift K) (pairT (Syn.shift R) (Syn.shift C)))
      (pairT (Syn.shift r) (pairT (Syn.shift M) (Syn.shift x))) := by simp [z, Syn.shift]
  have l := lin3 (Γ := Γ) (BB w X) (TB w) (AB w X) (GB w X) (N := pw M r) (y := z) (K₁ := K * K) (K₂ := R * R)
    (K₃ := zero) (p := pairT r (pairT M x)) (.allI (.impI (by
      rw [hz, shift_mul'', shift_mul'', shift_zero', shift_pairT, shift_pairT]
      exact GB_at w X _ _ _ _ _)))
  have sa : Γ ⊢[PRAAx] ap2 (sumF (GB w X)) (pw M r) z ≐ ap2 (sumF (wz w * (dz X * dz X))) (pw M r) z +
      ap2 (sumF (two * (Kz * Rz) * (wz w * sbp (SB X)))) (pw M r) z :=
    sum_add (wz w * (dz X * dz X)) (two * (Kz * Rz) * (wz w * sbp (SB X))) (pw M r) z
  have sc : Γ ⊢[PRAAx] ap2 (sumF (two * (Kz * Rz) * (wz w * sbp (SB X)))) (pw M r) z ≐ two * (K * R) * At w X r M x := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [hz, shift_mul'', shift_mul'', shift_two', shift_pairT, shift_pairT]
    have e : inst2 (two * (Kz * Rz) * (wz w * sbp (SB X))) (var 0)
        (pairT (pairT (Syn.shift K) (pairT (Syn.shift R) (Syn.shift C))) (pairT (Syn.shift r) (pairT (Syn.shift M) (Syn.shift x)))) =
        two * (fstT (fstT (pairT (pairT (Syn.shift K) (pairT (Syn.shift R) (Syn.shift C))) (pairT (Syn.shift r) (pairT (Syn.shift M) (Syn.shift x))))) *
          fstT (sndT (fstT (pairT (pairT (Syn.shift K) (pairT (Syn.shift R) (Syn.shift C))) (pairT (Syn.shift r) (pairT (Syn.shift M) (Syn.shift x))))))) *
        (inst2 (wz w) (var 0) (pairT (pairT (Syn.shift K) (pairT (Syn.shift R) (Syn.shift C))) (pairT (Syn.shift r) (pairT (Syn.shift M) (Syn.shift x)))) *
          Syn.subst ![var 0, pairT (pairT (Syn.shift K) (pairT (Syn.shift R) (Syn.shift C))) (pairT (Syn.shift r) (pairT (Syn.shift M) (Syn.shift x)))]
            (sbp (SB X))) := by
      simp only [inst2, PTm.subst_mul, subst_fstT, subst_sndT]; simp
    rw [e, inst2_AB]
    exact congrMul (congrMul (.eqRefl _) (congrMul sel_K sel_R)) (congrMul (wz_at w _ _ _ _ _) (sb_at X _ _ _ _ _))
  ipra_lc -natEq sa + natEq l - natEq sc

/-- `thm:weak-law`: for the `r`-fold product law with `W = ∑ w ≥ 1`, `S = ∑ w X`, `Q = ∑ w X²`,
`T = W^r`, the cleared deviation `D = |W S_r − r S|` and any threshold `C`:
`C² ∑_t P_r [D ≥ C] + r T S² ≤ r T W Q`. With `C = r W ε` this reads
`P(|X̄_r − μ| ≥ ε) ≤ (Q/W − (S/W)²) / (r ε²) = σ²/(r ε²)`. -/
theorem weak_law {M x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (hW : Γ ⊢[PRAAx] ap2 (sumF w) M x ≐ succ (pred (ap2 (sumF w) M x))) (r C : PTm n) :
    Γ ⊢[PRAAx] le (C * C * Ew (wz w) (geB Cz (dz X)) (pw M r)
        (pairT (pairT (ap2 (sumF w) M x) (pairT (r * ap2 (sumF (w * X)) M x) C)) (pairT r (pairT M x))) +
        r * Tt w r M x * (ap2 (sumF (w * X)) M x * ap2 (sumF (w * X)) M x))
      (r * Tt w r M x * (ap2 (sumF w) M x * ap2 (sumF (w * (X * X))) M x)) := by
  let W := ap2 (sumF w) M x
  let S := ap2 (sumF (w * X)) M x
  let z : PTm n := pairT (pairT W (pairT (r * S) C)) (pairT r (pairT M x))
  have ch := chebyshev (Γ := Γ) Cz (wz w) (dz X) (pw M r) z
  have e : Syn.subst ![z] (Cz * Cz) = sndT (sndT (fstT z)) * sndT (sndT (fstT z)) := by simp
  rw [e] at ch
  have sc := sel_C (Γ := Γ) (K := W) (R := r * S) (C := C) (p := pairT r (pairT M x))
  have ch' := le_congr (congrMul (congrMul sc sc) (.eqRefl _)) (.eqRefl _) ch
  have m := sample_moments (Γ := Γ) w X (x := x) hM r
  have i2 := natEq (Prf.andE₁ m); have i3 := natEq (Prf.andE₂ m)
  have hP := pw_pos' hW r
  refine le_cancel_pos hP ?_
  refine le_congr (.eqRefl _) ?_ (le_mul_mono (le_refl _) (le_add_mono ch' (le_refl _)))
  ipra_lc 𝔞 (Tt w r M x) * natEq (dev_sum (Γ := Γ) w X r M x W (r * S) C) +
    (𝔞 W * 𝔞 (At w X r M x) - 𝔞 r * 𝔞 S * 𝔞 (Tt w r M x)) * i2 + i3 -
    (𝔞 (Ew (wz w) (dz X * dz X) (pw M r) z) + 𝔞 r * 𝔞 (Tt w r M x) * (𝔞 S * 𝔞 S) - 𝔞 r * 𝔞 (Tt w r M x) * (𝔞 W * 𝔞 (ap2 (sumF (w * (X * X))) M x))) * natEq (total_pow (Γ := Γ) w (x := x) hM r)

end Laws

end LeanProofs.IPRA.Probability.WeakLaw
