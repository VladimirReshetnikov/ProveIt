import IPRADerivations.Foundations.ApproximateWitness
import IPRADerivations.Foundations.ModulusNormalization
import IPRADerivations.Foundations.FrontierSoundness

/-!
# Running intersections of rational intervals

Packets:

* `foundations/ipra_finite_observation`, `tex/analysis.tex`, Theorem `thm:finite-net-infimum`
  ("A primitive-recursive infimum name"), the step "Now take finite running intersections:
  `L*_k = max_{i ≤ k} L_i`, `U*_k = min_{i ≤ k} U_i`. The cross inequalities just proved show
  `L*_k ≤ U*_k`. The intervals are nested, and their width is at most `U_k − L_k`"
  (`eq:infimum-width`, `eq:infimum-lower`);
* `analysis/bohr_mollerup_ipra_2026-11-15`, `eq:strip-name`: "`L_0(k) = max_{i ≤ k} ℓ_i`,
  `U_0(k) = min_{i ≤ k} u_i` is a nested nonempty rational interval of width at most `2^{-k-1}`".

For endpoint bodies `L(i, x)`, `U(i, x)` (numerators over a common denominator):

* `lo L k x = max_{i ≤ k} L(i, x)` (the running maximum of `Probability/UnionUtility`) and
  `hi U k x = min_{i ≤ k} U(i, x)` (the running minimum of `Probability/FiniteLaws`);
* `lo_ge`, `hi_le`: `L_i ≤ lo(k)` and `hi(k) ≤ U_i` for `i ≤ k`;
* `lo_mono`, `hi_mono`: the intervals are nested, `lo(k) ≤ lo(l)` and `hi(l) ≤ hi(k)` for `k ≤ l`;
* `lo_lub`, `hi_glb`: `lo(k)` is some `L_i` and `hi(k)` is some `U_j` with `i, j ≤ k`, so a bound on the
  attaining sample bounds the endpoint;
* `nonempty`: if `L_i ≤ U_j` for all `i, j ≤ k` (the cross inequalities), then `lo(k) ≤ hi(k)`;
* `width`: `U_k ≤ L_k + w` gives `hi(k) ≤ lo(k) + w`.

The maximum and the minimum are attained (argmax, argmin), so no case analysis on the samples is needed.
-/

namespace LeanProofs.IPRA.Foundations.RunningIntersection

open_ipra exports
open LeanProofs.IPRA.Probability.UnionUtility (Mx Ag mx_upper ag_attains)
open LeanProofs.IPRA.Probability.FiniteLaws (Mn mn_le)
open LeanProofs.IPRA.Foundations.ModulusNormalization (mx_mono)
open LeanProofs.IPRA.Foundations.FrontierSoundness (up_shift le_of_lt_succ' lt_succ_of_le')

variable {n : ℕ} {Γ : List (Fm PTm n)} (L U : PTm 2)

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `max_{i ≤ k} L(i, x)`. -/
abbrev lo (k x : PTm n) : PTm n := Mx L (succ k) x

/-- `min_{i ≤ k} U(i, x)`. -/
abbrev hi (k x : PTm n) : PTm n := Mn U k x

/-- `L_i ≤ lo(k)` for `i ≤ k`. -/
theorem lo_ge {i k x : PTm n} (h : Γ ⊢[PRAAx] le i k) : Γ ⊢[PRAAx] le (inst2 L i x) (lo L k x) :=
  mx_upper L (b := i) (K := succ k) (x := x) (lt_succ_of_le' h)

/-- `hi(k) ≤ U_i` for `i ≤ k`. -/
theorem hi_le {i k x : PTm n} (h : Γ ⊢[PRAAx] le i k) : Γ ⊢[PRAAx] le (hi U k x) (inst2 U i x) :=
  mn_le U h

/-- The lower endpoints increase. -/
theorem lo_mono {k l x : PTm n} (h : Γ ⊢[PRAAx] le k l) : Γ ⊢[PRAAx] le (lo L k x) (lo L l x) :=
  mx_mono L h

/-- The index attaining the lower endpoint is at most `k`. -/
theorem lo_index (k x : PTm n) : Γ ⊢[PRAAx] le (Ag L (succ k) x) k :=
  le_of_lt_succ' (Prf.andE₁ (ag_attains L k x))

/-- `lo(k)` is one of the samples: a bound on the attaining sample bounds `lo(k)`. -/
theorem lo_lub {k x c : PTm n} (h : Γ ⊢[PRAAx] le (inst2 L (Ag L (succ k) x) x) c) :
    Γ ⊢[PRAAx] le (lo L k x) c :=
  le_congr (Prf.andE₂ (ag_attains L k x)) (.eqRefl c) h

/-- `hi(k)` is one of the samples: a lower bound of the attaining sample bounds `hi(k)` from below. -/
theorem hi_glb {k x c : PTm n} (h : Γ ⊢[PRAAx] le c (inst2 U (argmin U k x) x)) :
    Γ ⊢[PRAAx] le c (hi U k x) :=
  le_congr (.eqRefl c) (Prf.andE₂ (argmin_spec U k x)) h

/-- The upper endpoints decrease. -/
theorem hi_mono {k l x : PTm n} (h : Γ ⊢[PRAAx] le k l) : Γ ⊢[PRAAx] le (hi U l x) (hi U k x) :=
  hi_glb U (hi_le U (le_trans (Prf.andE₁ (argmin_spec U k x)) h))

/-- The cross inequalities at the two attaining indices give a nonempty interval. -/
theorem nonempty_at {k x : PTm n}
    (h : Γ ⊢[PRAAx] le (inst2 L (Ag L (succ k) x) x) (inst2 U (argmin U k x) x)) :
    Γ ⊢[PRAAx] le (lo L k x) (hi U k x) :=
  lo_lub L (hi_glb U h)

/-- If `L_i ≤ U_j` for all `i, j ≤ k`, then `lo(k) ≤ hi(k)`. -/
theorem nonempty {k x : PTm n}
    (hcross : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift k) ⟶
      Fm.all (le (var 0) (Syn.shift (Syn.shift k)) ⟶
        le (inst2 L (var 1) (Syn.shift (Syn.shift x))) (inst2 U (var 0) (Syn.shift (Syn.shift x)))))) :
    Γ ⊢[PRAAx] le (lo L k x) (hi U k x) := by
  have a := Prf.allE (Ag L (succ k) x) hcross
  simp only [Fm.subst_imp, Fm.subst_all, subst_le, subst_inst2, Syn.subst_var, Syn.inst_zero, Syn.up_zero,
    Syn.up_one, up_shift, Syn.subst_inst_shift] at a
  have b := Prf.allE (argmin U k x) (Prf.impE a (lo_index L k x))
  simp only [Fm.subst_imp, subst_le, subst_inst2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at b
  exact nonempty_at L U (Prf.impE b (Prf.andE₁ (argmin_spec U k x)))

/-- The width of the running intersection is at most the width of the last interval. -/
theorem width {k x w : PTm n} (hw : Γ ⊢[PRAAx] le (inst2 U k x) (inst2 L k x + w)) :
    Γ ⊢[PRAAx] le (hi U k x) (lo L k x + w) := by
  have h₁ := hi_le (Γ := Γ) U (x := x) (le_refl k)
  have h₂ := lo_ge (Γ := Γ) L (x := x) (le_refl k)
  ipra_le sl h₁ + sl hw + sl h₂

end LeanProofs.IPRA.Foundations.RunningIntersection
