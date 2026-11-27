import IPRADerivations.Core.Gcd
import IPRADerivations.Core.SumOrder
import IPRADerivations.Core.SumReflect
import IPRADerivations.Core.InductionTactic
import IPRADerivations.Core.Header

/-!
# The eigenvalue bound in every dimension (`ipra_presentations_to_witnesses`, `lem:integer-eigenvalue`)

Packet: `foundations/ipra_presentations_to_witnesses`, lemma `lem:integer-eigenvalue`, second
part: with `R(A) = max_j ∑_i |A_ij|`, "choose the first index `j` attaining `W = max_i |w_i|`.
... The `j`-th coordinate gives

`|λ| W = |∑_i w_i A_ij| ≤ ∑_i |w_i| |A_ij| ≤ W ∑_i |A_ij| ≤ W R(A)`.

Cancel the positive integer `W`."

`Foundations/WitnessAlgebra` has the integrality of `λ` in dimensions `2` and `3`. Here the
dimension `D` is a variable and the displayed chain is derived for one column `j`. Signed
quantities are pairs of natural terms, with `|P - N| = (P ∸ N) + (N ∸ P)` (`ad`):

* `ad_le_of`, `le_add_ad`, `ad_triangle`: `|x - y| ≤ z` from the two one-sided bounds, and
  `|(a + c) - (b + d)| ≤ |a - b| + |c - d|`;
* `sum_triangle`: `|∑_{i<D} p_i - ∑_{i<D} n_i| ≤ ∑_{i<D} |p_i - n_i|`, by quantifier-free
  induction on `D`;
* `sum_scale`, `major`: `∑_{i<D} ω_i α_i ≤ W ∑_{i<D} α_i` when `ω_i ≤ W` for `i < D`;
* `eigen_bound`: let `p_i`, `n_i` be the positive and negative parts of `w_i A_ij`,
  `ω_i = |w_i|`, `α_i = |A_ij|`, with `|p_i - n_i| ≤ ω_i α_i` and `ω_i ≤ W` for `i < D`, and
  `W ≥ 1`. If `L W = |∑ p_i - ∑ n_i|` (the `j`-th coordinate of `w A = λ w`, with `L = |λ|` and
  `W = |w_j|`), then `L ≤ ∑_{i<D} α_i`.

The column sum is at most `R(A)` by definition of the maximum. Not derived: the selection of
the maximizing index by a bounded scan, the integrality of `λ` for a variable dimension, and
`cor:eigenvalue-grid`.
-/

namespace LeanProofs.IPRA.Foundations.EigenvalueBound

open_ipra exports

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-! ## Absolute differences -/

/-- `|a - b|` for natural numbers. -/
abbrev ad (a b : PTm k) : PTm k := monus a b + monus b a

theorem ad_congr {a a' b b' : PTm k} (h₁ : Γ ⊢[PRAAx] a ≐ a') (h₂ : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] ad a b ≐ ad a' b' :=
  congrAdd (congrMonus h₁ h₂) (congrMonus h₂ h₁)

/-- `x ≤ y + |x - y|`. -/
theorem le_add_ad (x y : PTm k) : Γ ⊢[PRAAx] le x (y + ad x y) := by
  refine .orE (lt_or_le x y) ?_ ?_
  · have e := natEq (eq_add_of_le (le_of_lt (Prf.hyp0 (Γ := Γ) (φ := lt x y))))
    refine le_of_eq_add (d := monus y x + monus x y + monus y x) ?_
    ipra_lc e
  · have e := natEq (eq_add_of_le (Prf.hyp0 (Γ := Γ) (φ := le y x)))
    refine le_of_eq_add (d := monus y x) ?_
    ipra_lc -e

/-- `|x - y| ≤ z` from `x ≤ y + z` and `y ≤ x + z`. -/
theorem ad_le_of {x y z : PTm k} (h₁ : Γ ⊢[PRAAx] le x (y + z))
    (h₂ : Γ ⊢[PRAAx] le y (x + z)) : Γ ⊢[PRAAx] le (ad x y) z := by
  refine .orE (le_total x y) ?_ ?_
  · exact le_congr ((congrAdd Prf.hyp0 (.eqRefl _)).eqTrans (zero_add _)).eqSymm (.eqRefl _)
      (Order.monus_le_of_le_add h₂.wk)
  · exact le_congr ((congrAdd (.eqRefl _) Prf.hyp0).eqTrans (add_zero _)).eqSymm (.eqRefl _)
      (Order.monus_le_of_le_add h₁.wk)

/-- `|(a + c) - (b + d)| ≤ |a - b| + |c - d|`. -/
theorem ad_triangle (a b c d : PTm k) :
    Γ ⊢[PRAAx] le (ad (a + c) (b + d)) (ad a b + ad c d) := by
  refine ad_le_of ?_ ?_
  · exact le_congr (.eqRefl _) (by ipra_ring)
      (add_le_add₂ (le_add_ad a b) (le_add_ad c d))
  · exact le_congr (.eqRefl _) (by ipra_ring)
      (add_le_add₂ (le_add_ad b a) (le_add_ad d c))

/-! ## The triangle inequality for a signed finite sum -/

variable (p n : PTm 2)

/-- The body `|p(i, x) - n(i, x)|`. -/
def adB : PTm 2 := monus p n + monus n p

theorem inst2_adB (i x : PTm k) :
    inst2 (adB p n) i x = ad (inst2 p i x) (inst2 n i x) := by
  simp [inst2, adB]

theorem tri_step {D x : PTm k}
    (ih : Γ ⊢[PRAAx] le (ad (ap2 (sumF p) D x) (ap2 (sumF n) D x)) (ap2 (sumF (adB p n)) D x)) :
    Γ ⊢[PRAAx] le (ad (ap2 (sumF p) (succ D) x) (ap2 (sumF n) (succ D) x))
      (ap2 (sumF (adB p n)) (succ D) x) := by
  have t := ad_triangle (Γ := Γ) (ap2 (sumF p) D x) (ap2 (sumF n) D x) (inst2 p D x)
    (inst2 n D x)
  have u := add_le_add₂ ih (le_refl (ad (inst2 p D x) (inst2 n D x)))
  have e₂ : Γ ⊢[PRAAx] ap2 (sumF (adB p n)) D x + ad (inst2 p D x) (inst2 n D x) ≐
      ap2 (sumF (adB p n)) (succ D) x := by
    have s := sum_succ' (Γ := Γ) (adB p n) D x
    rw [inst2_adB] at s
    exact s.eqSymm
  exact le_congr (ad_congr (sum_succ' p D x).eqSymm (sum_succ' n D x).eqSymm) e₂ (le_trans t u)

/-- Variables: `0 = D`, `1 = x`. -/
private abbrev triF : Fm PTm 2 :=
  le (ad (ap2 (sumF p) (var 0) (var 1)) (ap2 (sumF n) (var 0) (var 1)))
    (ap2 (sumF (adB p n)) (var 0) (var 1))

private theorem tri₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] triF p n := by
  ipra_ind [subst_le, subst_ap2]
  · have e₁ := natEq ((congrMonus (sum_zero (Γ := ([] : List (Fm PTm 1))) p (var 0))
      (sum_zero n (var 0))).eqTrans (le_refl zero))
    have e₂ := natEq ((congrMonus (sum_zero (Γ := ([] : List (Fm PTm 1))) n (var 0))
      (sum_zero p (var 0))).eqTrans (le_refl zero))
    refine le_of_eq_add (d := zero) ?_
    ipra_lc natEq (sum_zero (Γ := ([] : List (Fm PTm 1))) (adB p n) (var 0)) - e₁ - e₂
  · exact tri_step p n Prf.hyp0

/-- `|∑_{i<D} p_i - ∑_{i<D} n_i| ≤ ∑_{i<D} |p_i - n_i|`. -/
theorem sum_triangle (D x : PTm k) :
    Γ ⊢[PRAAx] le (ad (ap2 (sumF p) D x) (ap2 (sumF n) D x)) (ap2 (sumF (adB p n)) D x) := by
  have i := inst (Γ := Γ) (tri₀ p n) (![D, x] : Fin 2 → PTm k)
  simpa using i

/-! ## Majorization of a weighted sum -/

variable (ω α : PTm 2)

/-- The body `ω(i, x) α(i, x)`. -/
def wB : PTm 2 := ω * α

theorem inst2_wB (i x : PTm k) : inst2 (wB ω α) i x = inst2 ω i x * inst2 α i x := by
  simp [inst2, wB]

/-- The body `W α(i, x)`; variables `0 = i`, `1 = ⟨W, x⟩`. -/
def mB : PTm 2 := fstT (var 1) * Syn.subst ![var 0, sndT (var 1)] α

theorem mB_at (i W x : PTm k) :
    Γ ⊢[PRAAx] inst2 (mB α) i (pairT W x) ≐ W * inst2 α i x := by
  have e₁ : Syn.subst ![i, pairT W x] (Syn.subst ![(var 0 : PTm 2), sndT (var 1)] α) =
      inst2 α i (sndT (pairT W x)) := by
    simp only [inst2, Syn.subst_subst]
    congr 1; funext j; fin_cases j <;> simp
  have e : inst2 (mB α) i (pairT W x) =
      fstT (pairT W x) * inst2 α i (sndT (pairT W x)) := by
    rw [← e₁]
    show Syn.subst ![i, pairT W x] (mB α) = _
    simp [mB]
  rw [e]
  exact congrMul (fst_pair _ _) (congrInst2 α (.eqRefl _) (snd_pair _ _))

/-- Variables: `0 = D`, `1 = W`, `2 = x`. -/
private abbrev scaleF : Fm PTm 3 :=
  ap2 (sumF (mB α)) (var 0) (pairT (var 1) (var 2)) ≐ var 1 * ap2 (sumF α) (var 0) (var 2)

private theorem scale₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] scaleF α := by
  refine ind _ trivial ?_ ?_
  · ipra_lc [Fm.subst_eq, subst_ap2, subst_pairT, PTm.subst_mul, Syn.subst_var, Syn.inst_zero, Syn.inst_one, inst_two, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] natEq (sum_zero (Γ := ([] : List (Fm PTm 2))) (mB α) (pairT (var 0) (var 1))) -
      𝔞 (var 0 : PTm 2) * natEq (sum_zero (Γ := ([] : List (Fm PTm 2))) α (var 1))
  · simp only [Fm.subst_eq, subst_ap2, subst_pairT, PTm.subst_mul, Syn.subst_var, Syn.repl_zero, repl_one, repl_two]
    have ih : [scaleF α] ⊢[PRAAx] ap2 (sumF (mB α)) (var 0) (pairT (var 1) (var 2)) ≐
        var 1 * ap2 (sumF α) (var 0) (var 2) := Prf.hyp0
    ipra_lc natEq (sum_succ' (Γ := [scaleF α]) (mB α) (var 0) (pairT (var 1) (var 2))) + natEq ih +
      natEq (mB_at (Γ := [scaleF α]) α (var 0) (var 1) (var 2)) -
      𝔞 (var 1 : PTm 3) * natEq (sum_succ' (Γ := [scaleF α]) α (var 0) (var 2))

/-- `∑_{i<D} W α_i = W ∑_{i<D} α_i`. -/
theorem sum_scale (D W x : PTm k) :
    Γ ⊢[PRAAx] ap2 (sumF (mB α)) D (pairT W x) ≐ W * ap2 (sumF α) D x := by
  have i := inst (Γ := Γ) (scale₀ α) (![D, W, x] : Fin 3 → PTm k)
  simpa using i

theorem mul_le_right {a b c : PTm k} (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx] le (a * c) (b * c) := by
  refine le_of_eq_add (d := monus b a * c) ?_
  ipra_lc 𝔞 c * natEq (eq_add_of_le h)

/-- `∑_{i<D} ω_i α_i ≤ W ∑_{i<D} α_i` when `ω_i ≤ W` for `i < D`. -/
theorem major {D W x : PTm k}
    (hW : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift D) ⟶
      le (inst2 ω (var 0) (Syn.shift x)) (Syn.shift W))) :
    Γ ⊢[PRAAx] le (ap2 (sumF (wB ω α)) D x) (W * ap2 (sumF α) D x) := by
  refine le_congr (.eqRefl _) (sum_scale α D W x)
    (sum_le_params (wB ω α) (mB α) x (pairT W x) D (.allI (.impI ?_)))
  rw [shift_pairT, inst2_wB]
  exact le_congr (.eqRefl _) (mB_at α _ _ _).eqSymm
    (mul_le_right (.impE hW.allOpen.wk Prf.hyp0))

/-! ## The bound -/

/-- `lem:integer-eigenvalue`, the bound, for one column and any dimension `D`: from
`L W = |∑ p_i - ∑ n_i|` with `|p_i - n_i| ≤ ω_i α_i` and `ω_i ≤ W` for `i < D`, and `W ≥ 1`,
`L ≤ ∑_{i<D} α_i`. -/
theorem eigen_bound {D W' L x : PTm k}
    (hW : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift D) ⟶
      le (inst2 ω (var 0) (Syn.shift x)) (Syn.shift (succ W'))))
    (hT : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift D) ⟶
      le (inst2 (adB p n) (var 0) (Syn.shift x)) (inst2 (wB ω α) (var 0) (Syn.shift x))))
    (hE : Γ ⊢[PRAAx] L * succ W' ≐ ad (ap2 (sumF p) D x) (ap2 (sumF n) D x)) :
    Γ ⊢[PRAAx] le L (ap2 (sumF α) D x) := by
  have c₁ := sum_triangle (Γ := Γ) p n D x
  have c₂ := sum_le_params (adB p n) (wB ω α) x x D hT
  have c₃ := major ω α hW
  have c := le_trans c₁ (le_trans c₂ c₃)
  exact mul_le_cancel (le_congr (hE.eqSymm.eqTrans (mul_comm _ _)) (.eqRefl _) c)

end LeanProofs.IPRA.Foundations.EigenvalueBound
