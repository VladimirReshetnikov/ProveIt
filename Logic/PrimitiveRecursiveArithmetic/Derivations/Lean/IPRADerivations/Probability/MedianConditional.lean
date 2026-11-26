import IPRADerivations.Probability.MedianWeighted
import IPRADerivations.Probability.MedianSymmetry

/-!
# Conditional and coordinatewise medians

Packet: `probability/median_ipra_constructive_proofs`, Theorem `thm:conditional` (the finite
conditional median is Bayes `L¹` optimal) and Theorem `thm:marginal` (coordinatewise optimality).
A finite joint law has weights `w(i, ⟨y, p⟩)` on values `x(i, ⟨y, p⟩)` for `i < N`, indexed by
`y < Y`. With

  `L_m = ∑_{y<Y} ∑_{i<N} w_{iy} |x_{iy} − m(y)|`,

* `outer_at`: the outer body evaluates to the inner deviation `D_1(m(y))` of
  `Probability/MedianWeighted`;
* `conditional_l1` (`thm:conditional`): if `m(y)` is a weighted median of the `y`-th conditional list
  for every `y < Y`, then `L_m ≤ L_g` for every `g(y, p)`;

`thm:marginal` is the same statement with `y` the coordinate index `j < d`, `x_{ij}` the
coordinates, unit weights, and `L` the `ℓ¹` objective `∑_i ‖x_i − a‖₁` written by coordinates.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.MedianConditional

open_ipra
open LeanProofs.IPRA.Probability.Expectation (Ew)
open LeanProofs.IPRA.Probability.MedianCounts (subst_data)
open LeanProofs.IPRA.Probability.MedianWeighted
open LeanProofs.IPRA.Probability.MedianSymmetry (shift_pairT')

variable {n : ℕ} {Γ : List (Fm PTm n)}

section Joint

variable (w X : PTm 2)

/-- The inner deviation at `y`, over `0 = y`, `1 = ⟨N, p⟩`:
`∑_{i<N} w(i, ⟨y, p⟩) |x(i, ⟨y, p⟩) − M(y, p)|`. -/
def outerB (M : PTm 2) : PTm 2 :=
  ap2 (sumF (wY w * Yb X)) (fstT (var 1))
    (pairT one (pairT (Syn.subst ![var 0, sndT (var 1)] M) (pairT (var 0) (sndT (var 1)))))

theorem inst2_outer (M : PTm 2) (y z : PTm n) :
    inst2 (outerB w X M) y z = ap2 (sumF (wY w * Yb X)) (fstT z)
      (pairT one (pairT (inst2 M y (sndT z)) (pairT y (sndT z)))) := by
  have e := subst_data y z M
  simp only [inst2, outerB, subst_ap2, subst_pairT, subst_fstT, subst_sndT, Syn.subst_var] at e ⊢
  rw [e]
  simp

theorem outer_at (M : PTm 2) (y N p : PTm n) :
    Γ ⊢[PRAAx] inst2 (outerB w X M) y (pairT N p) ≐ Dw w X N one (inst2 M y p) (pairT y p) := by
  rw [inst2_outer]
  have hp : Γ ⊢[PRAAx] sndT (pairT N p) ≐ p := snd_pair _ _
  exact congrAp2 (sumF (wY w * Yb X)) (fst_pair _ _) (LeanProofs.IPRA.congrPairT (.eqRefl _)
    (LeanProofs.IPRA.congrPairT (congrInst2 M (.eqRefl _) hp) (LeanProofs.IPRA.congrPairT (.eqRefl _) hp)))

/-- `L_M = ∑_{y<Y} ∑_{i<N} w_{iy} |x_{iy} − M(y)|`. -/
abbrev Lc (M : PTm 2) (Y N p : PTm n) : PTm n := ap2 (sumF (outerB w X M)) Y (pairT N p)

/-- `thm:conditional`: conditional medians minimize the expected absolute error among all
decision rules `g`. -/
theorem conditional_l1 (M G : PTm 2) {Y N p : PTm n}
    (hmed : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift Y) ⟶
      isMedW w X (Syn.shift N) (inst2 M (var 0) (Syn.shift p)) (pairT (var 0) (Syn.shift p)))) :
    Γ ⊢[PRAAx] le (Lc w X M Y N p) (Lc w X G Y N p) := by
  refine sum_le_params (outerB w X M) (outerB w X G) _ _ Y (.allI (.impI ?_))
  rw [shift_pairT']
  refine le_congr (outer_at w X M _ _ _).eqSymm (outer_at w X G _ _ _).eqSymm ?_
  exact le_congr (congrDw w X _ _ _ (one_mul _)) (.eqRefl _)
    (weighted_l1 w X (Prf.impE hmed.allOpen.wk Prf.hyp0) one _)

end Joint

end LeanProofs.IPRA.Probability.MedianConditional
