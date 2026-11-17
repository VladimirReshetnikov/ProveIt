import IPRADerivations.Probability.MedianTransport

/-!
# The finite Jensen inequality for medians

Packet: `probability/median_ipra_constructive_proofs`, Theorem `thm:jensen-median`, in the
certificate form the packet prescribes for iPRA. For a sample `x(i, p)` of length `N`, a map
`f(y, p)` and a threshold `t`, let

  `C(t) = #{i < N : f(x_i) ≤ t} = B_{f x}(t) + E_{f x}(t)`.

The interval hypothesis on the sublevel set `{f ≤ t}` enters through its consequence on the sample:
when `U ∉ {f ≤ t}`, every sample point with `f(x_i) ≤ t` lies on one side of `U` (`sideB`, `sideA`).

* `pt_side_below`, `pt_side_above`: `[f x ≤ t] ≤ [x < U]` (resp. `[U < x]`) under the side
  condition;
* `count_side`: then `C(t) ≤ B_x(U)` or `C(t) ≤ A_x(U)`;
* `jensen_count`: for a balance median `U`, `2 C(t) ≤ N`, i.e. at most `⌊N/2⌋` transformed
  observations are `≤ t`;
* `jensen_median` (`thm:jensen-median`): if `V` has `2 C(V) > N` (more than half of the transformed
  observations are `≤ V`, as for the upper median of `f x`) and the side certificate holds at `V`
  whenever `V < f(U)`, then `f(U) ≤ V`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.MedianJensen

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Algebra.CubeRootTwo (sg)
open LeanProofs.IPRA.AnalyticNumberTheory.Totatives (sg_lt sg_le)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Probability.MedianCounts
open LeanProofs.IPRA.Probability.MedianSymmetry (shift_pairT')
open LeanProofs.IPRA.Probability.MedianTransport (shift_inst2)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Pointwise -/

/-- `[y < t] + [y = t] ≤ 1`. -/
theorem le_bits_le_one (y t : PTm n) : Γ ⊢[PRAAx] le (sg (monus t y) + eqb y t) one := by
  have e := natEq (trichotomy_bits (Γ := Γ) y t)
  refine le_of_eq_add (d := sg (monus y t)) ?_
  apply deriveNat; ipra_simps; linear_combination -e

theorem le_bits_zero {y t : PTm n} (h : Γ ⊢[PRAAx] lt t y) : Γ ⊢[PRAAx] sg (monus t y) + eqb y t ≐ zero :=
  (congrAdd (sg_le (le_of_lt h)) (eqb_zero_of_gt h)).eqTrans (add_zero _)

/-- `[y ≤ t] ≤ [x < U]` when `y ≤ t` forces `x < U`. -/
theorem side_bit_below {y t x U : PTm n} (h : Γ ⊢[PRAAx] le y t ⟶ lt x U) :
    Γ ⊢[PRAAx] le (sg (monus t y) + eqb y t) (sg (monus U x)) := by
  refine .orE (lt_or_le t y) (le_congr (le_bits_zero Prf.hyp0).eqSymm (.eqRefl _) (zero_le _)) ?_
  exact le_congr (.eqRefl _) (sg_lt (.impE h.wk Prf.hyp0)).eqSymm (le_bits_le_one _ _)

/-- `[y ≤ t] ≤ [U < x]` when `y ≤ t` forces `U < x`. -/
theorem side_bit_above {y t x U : PTm n} (h : Γ ⊢[PRAAx] le y t ⟶ lt U x) :
    Γ ⊢[PRAAx] le (sg (monus t y) + eqb y t) (sg (monus x U)) := by
  refine .orE (lt_or_le t y) (le_congr (le_bits_zero Prf.hyp0).eqSymm (.eqRefl _) (zero_le _)) ?_
  exact le_congr (.eqRefl _) (sg_lt (.impE h.wk Prf.hyp0)).eqSymm (le_bits_le_one _ _)

section Map

variable (F X : PTm 2)

/-- `f x`, the transformed sample. -/
abbrev FX : PTm 2 := Permutation.FS F X

theorem pt_side_below {i t U p : PTm n}
    (h : Γ ⊢[PRAAx] le (inst2 F (inst2 X i p) p) t ⟶ lt (inst2 X i p) U) :
    Γ ⊢[PRAAx] le (inst2 (addBody (belowB (FX F X)) (equalB (FX F X))) i (pairT t p)) (inst2 (belowB X) i (pairT U p)) := by
  rw [inst2_addBody]
  have b := below_pt (Γ := Γ) (FX F X) i t p; have e := equal_pt (Γ := Γ) (FX F X) i t p
  rw [Permutation.inst2_FS] at b e
  exact le_congr (congrAdd b e).eqSymm (below_pt X i U p).eqSymm (side_bit_below h)

theorem pt_side_above {i t U p : PTm n}
    (h : Γ ⊢[PRAAx] le (inst2 F (inst2 X i p) p) t ⟶ lt U (inst2 X i p)) :
    Γ ⊢[PRAAx] le (inst2 (addBody (belowB (FX F X)) (equalB (FX F X))) i (pairT t p)) (inst2 (aboveB X) i (pairT U p)) := by
  rw [inst2_addBody]
  have b := below_pt (Γ := Γ) (FX F X) i t p; have e := equal_pt (Γ := Γ) (FX F X) i t p
  rw [Permutation.inst2_FS] at b e
  exact le_congr (congrAdd b e).eqSymm (above_pt X i U p).eqSymm (side_bit_above h)

/-! ## Counts -/

/-- `C(t) = #{i < N : f(x_i) ≤ t}`. -/
abbrev Cf (N t p : PTm n) : PTm n := Bc (FX F X) N t p + Ec (FX F X) N t p

/-- Every sample point with `f(x_i) ≤ t` lies below `U`. -/
abbrev sideB (N t U p : PTm n) : Fm PTm n :=
  Fm.all (lt (var 0) (Syn.shift N) ⟶ (le (inst2 F (inst2 X (var 0) (Syn.shift p)) (Syn.shift p)) (Syn.shift t) ⟶
    lt (inst2 X (var 0) (Syn.shift p)) (Syn.shift U)))

/-- Every sample point with `f(x_i) ≤ t` lies above `U`. -/
abbrev sideA (N t U p : PTm n) : Fm PTm n :=
  Fm.all (lt (var 0) (Syn.shift N) ⟶ (le (inst2 F (inst2 X (var 0) (Syn.shift p)) (Syn.shift p)) (Syn.shift t) ⟶
    lt (Syn.shift U) (inst2 X (var 0) (Syn.shift p))))

theorem count_side_below {N t U p : PTm n} (hs : Γ ⊢[PRAAx] sideB F X N t U p) :
    Γ ⊢[PRAAx] le (Cf F X N t p) (Bc X N U p) := by
  refine le_congr (sum_add _ _ _ _) (.eqRefl _)
    (sum_le_params (addBody (belowB (FX F X)) (equalB (FX F X))) (belowB X) _ _ N (.allI (.impI ?_)))
  rw [shift_pairT', shift_pairT']
  exact pt_side_below F X (Prf.impE hs.allOpen.wk Prf.hyp0)

theorem count_side_above {N t U p : PTm n} (hs : Γ ⊢[PRAAx] sideA F X N t U p) :
    Γ ⊢[PRAAx] le (Cf F X N t p) (Ac X N U p) := by
  refine le_congr (sum_add _ _ _ _) (.eqRefl _)
    (sum_le_params (addBody (belowB (FX F X)) (equalB (FX F X))) (aboveB X) _ _ N (.allI (.impI ?_)))
  rw [shift_pairT', shift_pairT']
  exact pt_side_above F X (Prf.impE hs.allOpen.wk Prf.hyp0)

/-- For a balance median `U` and a side certificate at `t`: `2 C(t) ≤ N`. -/
theorem jensen_count {N t U p : PTm n} (hm : Γ ⊢[PRAAx] isMed X N U p)
    (hs : Γ ⊢[PRAAx] sideB F X N t U p ⋎ sideA F X N t U p) : Γ ⊢[PRAAx] le (two * Cf F X N t p) N :=
  .orE hs (le_trans (le_mul_mono (le_refl two) (count_side_below F X Prf.hyp0)) (Prf.andE₁ hm).wk)
    (le_trans (le_mul_mono (le_refl two) (count_side_above F X Prf.hyp0)) (Prf.andE₂ hm).wk)

/-- `thm:jensen-median`: if `2 C(V) > N` and the side certificate holds at `V` whenever `V < f(U)`,
then `f(U) ≤ V`. -/
theorem jensen_median {N U V p : PTm n} (hm : Γ ⊢[PRAAx] isMed X N U p) (hV : Γ ⊢[PRAAx] lt N (two * Cf F X N V p))
    (hcert : Γ ⊢[PRAAx] lt V (inst2 F U p) ⟶ (sideB F X N V U p ⋎ sideA F X N V U p)) :
    Γ ⊢[PRAAx] le (inst2 F U p) V := by
  refine .orE (lt_or_le V (inst2 F U p)) ?_ Prf.hyp0
  exact lt_irrefl N _ (lt_of_lt_of_le hV.wk (jensen_count F X hm.wk (.impE hcert.wk Prf.hyp0)))

end Map

end LeanProofs.IPRA.Probability.MedianJensen
