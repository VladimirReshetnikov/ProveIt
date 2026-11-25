import IPRADerivations.DiophantineNumberTheory.ProjectiveNormalize
import IPRADerivations.Probability.Independence
import IPRADerivations.Core.LinearCombination

/-!
# Uniqueness of Bézout-primitive representatives in every dimension

Packet: `diophantine-number-theory/diophantine_geometry_ipra`, Lemma `lem:normalize`, the uniqueness clause
in arbitrary dimension: "Suppose primitive vectors `v, w` satisfy `v_i w_j = v_j w_i` for all `i, j`. Choose
... Bezout coefficients `c_i` with `∑_i c_i v_i = 1`. Set `a = ∑_i c_i w_i`. The proportionality equations
give `v_j a = w_j` ... so cancellation gives `w_i = a v_i` for every `i`. As `w` is primitive, `|a| = 1`."

A vector of length `N` is a body `V` over `0 = i`, `1 = x` (entries `V(i, x)`, `i < N`), with natural
entries. Primitivity is certified as in the packet by Bézout coefficients, the integer coefficients split into
natural parts: `∑ C_i V_i = ∑ C'_i V_i + 1`.

* `cross_sum`: `v_j ∑ C_i w_i = w_j ∑ C_i v_i` from the proportionality equations at `j`;
* `mul_of_add`: `v a = v a' + w` gives `w = v (a ∸ a')`;
* `scale_at`: `w_j = v_j t` for `t = ∑ C_i w_i ∸ ∑ C'_i w_i`;
* `one_of_mul`: `t s = 1` gives `t = 1`;
* `vector_unique`: two Bézout-primitive vectors with `v_i w_j = v_j w_i` for all `i, j < N` are equal.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.ProjectiveVectorUnique

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem shift_mul2 (a b : PTm k) : Syn.shift (a * b) = Syn.shift a * Syn.shift b := by simp [Syn.shift]

theorem inst2_mul (f g : PTm 2) (i y : PTm k) : inst2 (f * g) i y = inst2 f i y * inst2 g i y := by
  simp [inst2]

/-- `C(i, snd y)`. -/
abbrev liftS (C : PTm 2) : PTm 2 := Syn.subst ![var 0, sndT (var 1)] C
/-- `W(fst y, snd y)`. -/
abbrev atJ (W : PTm 2) : PTm 2 := Syn.subst ![fstT (var 1), sndT (var 1)] W

theorem inst2_liftS (C : PTm 2) (i y : PTm k) : inst2 (liftS C) i y = inst2 C i (sndT y) := by
  simp only [inst2, Syn.subst_subst]
  congr 1; funext j; fin_cases j <;> simp

theorem inst2_atJ (W : PTm 2) (i y : PTm k) : inst2 (atJ W) i y = inst2 W (fstT y) (sndT y) := by
  simp only [inst2, Syn.subst_subst]
  congr 1; funext j; fin_cases j <;> simp

/-- `C_i V_i W_j`, over `1 = ⟨j, x⟩`. -/
abbrev hB (C V W : PTm 2) : PTm 2 := liftS C * liftS V * atJ W

theorem hB_at (C V W : PTm 2) (i j x : PTm k) :
    Γ ⊢[PRAAx] inst2 (hB C V W) i (pairT j x) ≐ inst2 C i x * inst2 V i x * inst2 W j x := by
  rw [inst2_mul, inst2_mul, inst2_liftS, inst2_liftS, inst2_atJ]
  exact congrMul (congrMul (congrInst2 _ (.eqRefl _) (snd_pair _ _)) (congrInst2 _ (.eqRefl _) (snd_pair _ _)))
    (congrInst2 _ (fst_pair _ _) (snd_pair _ _))

/-- The proportionality equations at a fixed `j`: `v_j w_i = v_i w_j` for `i < N`. -/
abbrev propJ (V W : PTm 2) (j N x : PTm k) : Fm PTm k :=
  Fm.all (lt (var 0) (Syn.shift N) ⟶ inst2 V (Syn.shift j) (Syn.shift x) * inst2 W (var 0) (Syn.shift x) ≐
    inst2 V (var 0) (Syn.shift x) * inst2 W (Syn.shift j) (Syn.shift x))

/-- `v_j ∑ C_i w_i = w_j ∑ C_i v_i`. -/
theorem cross_sum (C V W : PTm 2) {j N x : PTm k} (hp : Γ ⊢[PRAAx] propJ V W j N x) :
    Γ ⊢[PRAAx] inst2 V j x * ap2 (sumF (C * W)) N x ≐ inst2 W j x * ap2 (sumF (C * V)) N x := by
  have s1 := sum_scale (Γ := Γ) (hB C V W) (C * W) N (inst2 V j x) x (pairT j x) (.allI (.impI (by
    rw [shift_pairT, inst2_mul C W, show Syn.shift (inst2 V j x) = inst2 V (Syn.shift j) (Syn.shift x) from
      subst_inst2 _ _ _ _]
    have e := natEq (Prf.impE hp.allOpen.wk Prf.hyp0)
    have h := natEq (hB_at (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) C V W (var 0) (Syn.shift j) (Syn.shift x))
    apply deriveNat; ipra_simps
    linear_combination h - 𝔞 (inst2 C (var 0) (Syn.shift x)) * e)))
  have s2 := sum_scale (Γ := Γ) (hB C V W) (C * V) N (inst2 W j x) x (pairT j x) (.allI (.impI (by
    rw [shift_pairT, inst2_mul C V, show Syn.shift (inst2 W j x) = inst2 W (Syn.shift j) (Syn.shift x) from
      subst_inst2 _ _ _ _]
    have h := natEq (hB_at (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) C V W (var 0) (Syn.shift j) (Syn.shift x))
    apply deriveNat; ipra_simps
    linear_combination h)))
  exact s1.eqSymm.eqTrans s2

/-- `v a = v a' + w` gives `w = v (a ∸ a')`. -/
theorem mul_of_add {v a a' w : PTm k} (h : Γ ⊢[PRAAx] v * a ≐ v * a' + w) : Γ ⊢[PRAAx] w ≐ v * monus a a' := by
  refine .orE (lt_or_le a a') ?_ ?_
  · have hl : (lt a a' :: Γ) ⊢[PRAAx] le (succ a) a' := Prf.hyp0
    have z : (lt a a' :: Γ) ⊢[PRAAx] monus a a' ≐ zero := le_of_lt Prf.hyp0
    have e := natEq (h.wk : (lt a a' :: Γ) ⊢[PRAAx] _)
    have w0 : (lt a a' :: Γ) ⊢[PRAAx] le w zero := by
      ipra_le 𝔞 v + 𝔞 v * sl hl using linear_combination e
    exact ((monus_zero w).eqSymm.eqTrans w0).eqTrans ((congrMul (.eqRefl _) z).eqTrans (mul_zero _)).eqSymm
  · have ea := natEq (eq_add_of_le (Prf.hyp0 : (le a' a :: Γ) ⊢[PRAAx] le a' a))
    have e := natEq (h.wk : (le a' a :: Γ) ⊢[PRAAx] _)
    apply deriveNat; ipra_simps; linear_combination -e + 𝔞 v * ea

/-- `w_j = v_j t` for `t = ∑ C_i w_i ∸ ∑ C'_i w_i`. -/
theorem scale_at (C C' V W : PTm 2) {j N x : PTm k}
    (hv : Γ ⊢[PRAAx] ap2 (sumF (C * V)) N x ≐ ap2 (sumF (C' * V)) N x + one)
    (hp : Γ ⊢[PRAAx] propJ V W j N x) :
    Γ ⊢[PRAAx] inst2 W j x ≐ inst2 V j x * monus (ap2 (sumF (C * W)) N x) (ap2 (sumF (C' * W)) N x) := by
  refine mul_of_add ?_
  ipra_lc natEq (cross_sum C V W hp) - natEq (cross_sum C' V W hp) + 𝔞 (inst2 W j x) * natEq hv

/-- `t s = 1` gives `t = 1`. -/
theorem one_of_mul {t s : PTm k} (h : Γ ⊢[PRAAx] t * s ≐ one) : Γ ⊢[PRAAx] t ≐ one := by
  have hs : Γ ⊢[PRAAx] s ≐ succ (pred s) := by
    refine .orE (zero_or_succ s) ?_ Prf.hyp0
    have e := natEq (h.wk : ((s ≐ zero) :: Γ) ⊢[PRAAx] _)
    have z := natEq (Prf.hyp0 : ((s ≐ zero) :: Γ) ⊢[PRAAx] s ≐ zero)
    exact succ_ne_zero' _ (by apply deriveNat; ipra_simps; linear_combination -e + 𝔞 t * z :
      ((s ≐ zero) :: Γ) ⊢[PRAAx] succ (zero : PTm k) ≐ zero)
  have ht : Γ ⊢[PRAAx] t ≐ succ (pred t) := by
    refine .orE (zero_or_succ t) ?_ Prf.hyp0
    have e := natEq (h.wk : ((t ≐ zero) :: Γ) ⊢[PRAAx] _)
    have z := natEq (Prf.hyp0 : ((t ≐ zero) :: Γ) ⊢[PRAAx] t ≐ zero)
    exact succ_ne_zero' _ (by apply deriveNat; ipra_simps; linear_combination -e + 𝔞 s * z :
      ((t ≐ zero) :: Γ) ⊢[PRAAx] succ (zero : PTm k) ≐ zero)
  have e := natEq h; have es := natEq hs; have et := natEq ht
  have l1 : Γ ⊢[PRAAx] le t one := by
    ipra_le 𝔞 t * 𝔞 (pred s) using linear_combination -e + 𝔞 t * es
  have l2 : Γ ⊢[PRAAx] le one t := by ipra_le 𝔞 (pred t) using linear_combination et
  exact le_antisymm l1 l2

/-- The proportionality equations `v_i w_j = v_j w_i` for all `i, j < N`. -/
abbrev propAll (V W : PTm 2) (N x : PTm k) : Fm PTm k :=
  Fm.all (lt (var 0) (Syn.shift N) ⟶ propJ V W (var 0) (Syn.shift N) (Syn.shift x))

theorem shift_sum_eq {f g : PTm 2} {N x : PTm k}
    (h : Γ ⊢[PRAAx] ap2 (sumF f) N x ≐ ap2 (sumF g) N x + one) :
    Γ.map Fm.shift ⊢[PRAAx] ap2 (sumF f) (Syn.shift N) (Syn.shift x) ≐
      ap2 (sumF g) (Syn.shift N) (Syn.shift x) + one := by
  have e := h.shift
  simpa [Fm.shift, Syn.shift] using e

/-- The symmetric proportionality equations. -/
theorem propJ_symm {V W : PTm 2} {j N x : PTm k} (h : Γ ⊢[PRAAx] propJ V W j N x) :
    Γ ⊢[PRAAx] propJ W V j N x := by
  refine .allI (.impI ?_)
  ipra_lc -natEq (Prf.impE h.allOpen.wk Prf.hyp0)

/-- `∑ C_i W_i ∸ ∑ C'_i W_i`. -/
abbrev tT (C C' W : PTm 2) (N x : PTm k) : PTm k := monus (ap2 (sumF (C * W)) N x) (ap2 (sumF (C' * W)) N x)

theorem shift_tT (C C' W : PTm 2) (N x : PTm k) :
    Syn.shift (tT C C' W N x) = tT C C' W (Syn.shift N) (Syn.shift x) := by simp [Syn.shift]

/-- `lem:normalize`, uniqueness: two Bézout-primitive vectors on the same projective point are equal. -/
theorem vector_unique (C C' D D' V W : PTm 2) {N x : PTm k}
    (hv : Γ ⊢[PRAAx] ap2 (sumF (C * V)) N x ≐ ap2 (sumF (C' * V)) N x + one)
    (hw : Γ ⊢[PRAAx] ap2 (sumF (D * W)) N x ≐ ap2 (sumF (D' * W)) N x + one)
    (hp : Γ ⊢[PRAAx] propAll V W N x) :
    Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ inst2 W (var 0) (Syn.shift x) ≐ inst2 V (var 0) (Syn.shift x)) := by
  have hv' := shift_sum_eq hv
  have hw' := shift_sum_eq hw
  have sW : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ inst2 W (var 0) (Syn.shift x) ≐
      inst2 V (var 0) (Syn.shift x) * tT C C' W (Syn.shift N) (Syn.shift x)) :=
    .allI (.impI (scale_at C C' V W hv'.wk (Prf.impE hp.allOpen.wk Prf.hyp0)))
  have sV : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ inst2 V (var 0) (Syn.shift x) ≐
      inst2 W (var 0) (Syn.shift x) * tT D D' V (Syn.shift N) (Syn.shift x)) :=
    .allI (.impI (scale_at D D' W V hw'.wk (propJ_symm (Prf.impE hp.allOpen.wk Prf.hyp0))))
  -- `v_i = (t s) v_i`, summed against `C`
  have vts : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ inst2 V (var 0) (Syn.shift x) ≐
      (tT C C' W (Syn.shift N) (Syn.shift x) * tT D D' V (Syn.shift N) (Syn.shift x)) *
        inst2 V (var 0) (Syn.shift x)) := by
    refine .allI (.impI ?_)
    have a := natEq (Prf.impE sW.allOpen.wk Prf.hyp0)
    have b := natEq (Prf.impE sV.allOpen.wk Prf.hyp0)
    apply deriveNat; ipra_simps
    linear_combination b + 𝔞 (tT D D' V (Syn.shift N) (Syn.shift x)) * a
  have scaled : Γ ⊢[PRAAx] ap2 (sumF (C * V)) N x ≐
      (tT C C' W N x * tT D D' V N x) * ap2 (sumF (C * V)) N x := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_mul2, shift_tT, shift_tT, inst2_mul C V]
    have a := natEq (Prf.impE vts.allOpen.wk Prf.hyp0)
    apply deriveNat; ipra_simps
    linear_combination 𝔞 (inst2 C (var 0) (Syn.shift x)) * a
  have x1 := natEq scaled; have e := natEq hv
  have ts : Γ ⊢[PRAAx] tT C C' W N x * tT D D' V N x ≐ one := by
    refine (mul_cancel (D := succ (ap2 (sumF (C' * V)) N x)) (congrSucc (pred_succ _).eqSymm) ?_).eqSymm
    ipra_lc x1 - (1 - 𝔞 (tT C C' W N x) * 𝔞 (tT D D' V N x)) * e
  have t1 := one_of_mul ts
  have t1s : Γ.map Fm.shift ⊢[PRAAx] tT C C' W (Syn.shift N) (Syn.shift x) ≐ one := by
    have h0 := t1.shift
    rw [show Fm.shift (tT C C' W N x ≐ one) = (Syn.shift (tT C C' W N x) ≐ Syn.shift one) from rfl,
      shift_tT, show Syn.shift (one : PTm k) = one by simp [Syn.shift]] at h0
    exact h0
  refine .allI (.impI ?_)
  exact (Prf.impE sW.allOpen.wk Prf.hyp0).eqTrans ((congrMul (.eqRefl _) t1s.wk).eqTrans
    (by ipra_ring))

end LeanProofs.IPRA.DiophantineNumberTheory.ProjectiveVectorUnique
