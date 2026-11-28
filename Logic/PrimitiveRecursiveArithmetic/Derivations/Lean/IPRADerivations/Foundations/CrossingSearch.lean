import IPRADerivations.Foundations.BoundedReflection
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.Fubini

/-!
# A bounded first crossing (`pnt_ipra_constructive_2026-11-14`, `con:deficit`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `contraction.tex`, proof of Lemma
`con:deficit` (Finite block deficit), third case: "a bounded search finds an index `i₀` in the first half with
`b_{i₀} ≥ a/4` and an index in the second half with `b_i ≤ −a/4`. Let `v` be the first index after `i₀` with
`b_v ≤ −a/4`, and let `u < v` be the last index at or after `i₀` with `b_u ≥ a/4`. These are minima and maxima of
finite decidable sets. For `u < i < v`, `−a/4 < b_i < a/4`."

For two decidable bodies `H(i, x)` ("high") and `L(i, x)` ("low"), read as true when nonzero, a high index `i₀`
and a later low index `j₀` give primitive recursive indices

* `vT`: the least low index after `i₀` (`wit` of the shifted body `Ls L`), and
* `uT`: the greatest high index in `[i₀, v)` (`pred v` minus the least witness of the reflected body `Hr H`),

with `H(u) ≠ 0`, `L(v) ≠ 0`, `i₀ ≤ u < v ≤ j₀` (`v_low`, `v_le`, `u_high`, `u_ge`, `u_lt`) and, for every
`u < i < v`, `H(i) = 0` and `L(i) = 0` (`between_not_high`, `between_not_low`). No sign decision about a real
number occurs: only least witnesses of bounded searches (`BoundedReflection.ex_elim`, `ex_least`).
-/

namespace LeanProofs.IPRA.Foundations.CrossingSearch

open_ipra exports
open LeanProofs.IPRA.Foundations.BoundedReflection (exB wit ex_intro ex_elim ex_least)
export LeanProofs.IPRA.Common (monus_of_eq)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Generic facts -/

/-- `a = b` and `a ≠ 0` give `b ≠ 0`. -/
theorem ne_transport {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) (ha : Γ ⊢[PRAAx] neg (a ≐ zero)) :
    Γ ⊢[PRAAx] neg (b ≐ zero) :=
  Order.ne_zero_congr h ha

/-- The least witness is at most every witness. -/
theorem wit_le_of (f : PTm 2) {N k x : PTm n} (hk : Γ ⊢[PRAAx] neg (inst2 f k x ≐ zero)) :
    Γ ⊢[PRAAx] le (wit f N x) k :=
  .orE (lt_or_le k (wit f N x)) (.botE _ (.impE hk.wk (ex_least f Prf.hyp0))) Prf.hyp0

/-! ## The shifted and reflected bodies -/

/-- `L(i₀ + 1 + k, x)` over `0 = k`, `1 = ⟨i₀, x⟩`. -/
def Ls (L : PTm 2) : PTm 2 := Syn.subst ![succ (fstT (var 1)) + var 0, sndT (var 1)] L

/-- `H(p − k, x)` over `0 = k`, `1 = ⟨p, x⟩`. -/
def Hr (H : PTm 2) : PTm 2 := Syn.subst ![monus (fstT (var 1)) (var 0), sndT (var 1)] H

theorem inst2_Ls (L : PTm 2) (k z : PTm n) : inst2 (Ls L) k z = inst2 L (succ (fstT z) + k) (sndT z) := by
  simp only [inst2, Ls, Syn.subst_subst]; congr 1; funext i; fin_cases i <;> simp

theorem inst2_Hr (H : PTm 2) (k z : PTm n) : inst2 (Hr H) k z = inst2 H (monus (fstT z) k) (sndT z) := by
  simp only [inst2, Hr, Syn.subst_subst]; congr 1; funext i; fin_cases i <;> simp

theorem Ls_at (L : PTm 2) (k i0 x : PTm n) :
    Γ ⊢[PRAAx] inst2 (Ls L) k (pairT i0 x) ≐ inst2 L (succ i0 + k) x := by
  rw [inst2_Ls]
  exact congrInst2 L (congrAdd (congrSucc (fst_pair _ _)) (.eqRefl _)) (snd_pair _ _)

theorem Hr_at (H : PTm 2) (k p x : PTm n) :
    Γ ⊢[PRAAx] inst2 (Hr H) k (pairT p x) ≐ inst2 H (monus p k) x := by
  rw [inst2_Hr]
  exact congrInst2 H (congrMonus (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)

/-! ## The first low index after `i₀` -/

/-- The search offset of `v`. -/
abbrev wv (L : PTm 2) (i0 j0 x : PTm n) : PTm n := wit (Ls L) (monus j0 i0) (pairT i0 x)

/-- `v`: the least low index after `i₀`. -/
abbrev vT (L : PTm 2) (i0 j0 x : PTm n) : PTm n := succ i0 + wv L i0 j0 x

theorem wv_spec (L : PTm 2) {i0 j0 x : PTm n} (hj0 : Γ ⊢[PRAAx] neg (inst2 L j0 x ≐ zero))
    (hlt : Γ ⊢[PRAAx] lt i0 j0) :
    Γ ⊢[PRAAx] lt (wv L i0 j0 x) (monus j0 i0) ⋏ neg (inst2 L (vT L i0 j0 x) x ≐ zero) := by
  have e0 : Γ ⊢[PRAAx] j0 ≐ succ i0 + monus j0 (succ i0) := eq_add_of_le hlt
  have e1 := natEq (eq_add_of_le (le_of_lt hlt))
  have e0' := natEq e0
  have hk : Γ ⊢[PRAAx] lt (monus j0 (succ i0)) (monus j0 i0) := by ipra_le 0 with e0' - e1
  have hf : Γ ⊢[PRAAx] neg (inst2 (Ls L) (monus j0 (succ i0)) (pairT i0 x) ≐ zero) :=
    ne_transport ((congrInst2 L e0 (.eqRefl _)).eqTrans (Ls_at L _ i0 x).eqSymm) hj0
  have el := ex_elim (Ls L) (ex_intro (Ls L) hf hk)
  exact .andI (Prf.andE₁ el) (ne_transport (Ls_at L _ i0 x) (Prf.andE₂ el))

/-- `L(v) ≠ 0`. -/
theorem v_low (L : PTm 2) {i0 j0 x : PTm n} (hj0 : Γ ⊢[PRAAx] neg (inst2 L j0 x ≐ zero))
    (hlt : Γ ⊢[PRAAx] lt i0 j0) : Γ ⊢[PRAAx] neg (inst2 L (vT L i0 j0 x) x ≐ zero) :=
  Prf.andE₂ (wv_spec L hj0 hlt)

/-- `v ≤ j₀`. -/
theorem v_le (L : PTm 2) {i0 j0 x : PTm n} (hj0 : Γ ⊢[PRAAx] neg (inst2 L j0 x ≐ zero))
    (hlt : Γ ⊢[PRAAx] lt i0 j0) : Γ ⊢[PRAAx] le (vT L i0 j0 x) j0 := by
  have hw := Prf.andE₁ (wv_spec L hj0 hlt)
  have e1 := natEq (eq_add_of_le (le_of_lt hlt))
  ipra_le sl hw with e1

/-- `i₀ < v`. -/
theorem v_gt (L : PTm 2) (i0 j0 x : PTm n) : Γ ⊢[PRAAx] lt i0 (vT L i0 j0 x) := by
  ipra_le 𝔞 (wv L i0 j0 x)

/-- `pred v = i₀ + w`. -/
theorem pred_v (L : PTm 2) (i0 j0 x : PTm n) : Γ ⊢[PRAAx] pred (vT L i0 j0 x) ≐ i0 + wv L i0 j0 x :=
  (congrPred (succ_add i0 _)).eqTrans (pred_succ _)

/-- No low index strictly between `i₀` and `v`. -/
theorem between_not_low (L : PTm 2) {i0 j0 x i : PTm n} (h1 : Γ ⊢[PRAAx] lt i0 i)
    (h2 : Γ ⊢[PRAAx] lt i (vT L i0 j0 x)) : Γ ⊢[PRAAx] inst2 L i x ≐ zero := by
  have ei : Γ ⊢[PRAAx] i ≐ succ i0 + monus i (succ i0) := eq_add_of_le h1
  have ei' := natEq ei
  have hk : Γ ⊢[PRAAx] lt (monus i (succ i0)) (wv L i0 j0 x) := by ipra_le sl h2 with ei'
  have z := ex_least (Ls L) hk
  exact (congrInst2 L ei (.eqRefl _)).eqTrans ((Ls_at L _ i0 x).eqSymm.eqTrans z)

/-! ## The last high index before `v` -/

/-- The search offset of `u`. -/
abbrev wu (H L : PTm 2) (i0 j0 x : PTm n) : PTm n :=
  wit (Hr H) (monus (vT L i0 j0 x) i0) (pairT (pred (vT L i0 j0 x)) x)

/-- `u`: the greatest high index in `[i₀, v)`. -/
abbrev uT (H L : PTm 2) (i0 j0 x : PTm n) : PTm n := monus (pred (vT L i0 j0 x)) (wu H L i0 j0 x)

/-- The reflected search succeeds at offset `w` (the index `i₀`). -/
theorem wu_spec (H L : PTm 2) {i0 j0 x : PTm n} (hi0 : Γ ⊢[PRAAx] neg (inst2 H i0 x ≐ zero)) :
    Γ ⊢[PRAAx] lt (wu H L i0 j0 x) (monus (vT L i0 j0 x) i0) ⋏
      neg (inst2 H (uT H L i0 j0 x) x ≐ zero) ⋏ le (wu H L i0 j0 x) (wv L i0 j0 x) := by
  have ep := pred_v (Γ := Γ) L i0 j0 x
  have em : Γ ⊢[PRAAx] monus (pred (vT L i0 j0 x)) (wv L i0 j0 x) ≐ i0 :=
    monus_of_eq (ep.eqTrans (add_comm _ _))
  have hf : Γ ⊢[PRAAx] neg (inst2 (Hr H) (wv L i0 j0 x) (pairT (pred (vT L i0 j0 x)) x) ≐ zero) :=
    ne_transport ((congrInst2 H em.eqSymm (.eqRefl _)).eqTrans (Hr_at H _ _ x).eqSymm) hi0
  have e1 := natEq (eq_add_of_le (le_of_lt (v_gt (Γ := Γ) L i0 j0 x)))
  have hk : Γ ⊢[PRAAx] lt (wv L i0 j0 x) (monus (vT L i0 j0 x) i0) := by ipra_le 0 with e1
  have el := ex_elim (Hr H) (ex_intro (Hr H) hf hk)
  exact .andI (Prf.andE₁ el) (.andI (ne_transport (Hr_at H _ _ x) (Prf.andE₂ el)) (wit_le_of (Hr H) hf))

/-- `pred v = w_u + u`. -/
theorem pred_v_u (H L : PTm 2) {i0 j0 x : PTm n} (hi0 : Γ ⊢[PRAAx] neg (inst2 H i0 x ≐ zero)) :
    Γ ⊢[PRAAx] pred (vT L i0 j0 x) ≐ wu H L i0 j0 x + uT H L i0 j0 x := by
  have hww := Prf.andE₂ (Prf.andE₂ (wu_spec H L (j0 := j0) hi0))
  have ep := natEq (pred_v (Γ := Γ) L i0 j0 x)
  have hle : Γ ⊢[PRAAx] le (wu H L i0 j0 x) (pred (vT L i0 j0 x)) := by ipra_le sl hww + 𝔞 i0 with ep
  exact eq_add_of_le hle

/-- `H(u) ≠ 0`. -/
theorem u_high (H L : PTm 2) {i0 j0 x : PTm n} (hi0 : Γ ⊢[PRAAx] neg (inst2 H i0 x ≐ zero)) :
    Γ ⊢[PRAAx] neg (inst2 H (uT H L i0 j0 x) x ≐ zero) :=
  Prf.andE₁ (Prf.andE₂ (wu_spec H L hi0))

/-- `i₀ ≤ u`. -/
theorem u_ge (H L : PTm 2) {i0 j0 x : PTm n} (hi0 : Γ ⊢[PRAAx] neg (inst2 H i0 x ≐ zero)) :
    Γ ⊢[PRAAx] le i0 (uT H L i0 j0 x) := by
  have hww := Prf.andE₂ (Prf.andE₂ (wu_spec H L (j0 := j0) hi0))
  have ep := natEq (pred_v (Γ := Γ) L i0 j0 x)
  have eu := natEq (pred_v_u H L (j0 := j0) hi0)
  ipra_le sl hww with eu - ep

/-- `u < v`. -/
theorem u_lt (H L : PTm 2) {i0 j0 x : PTm n} (hi0 : Γ ⊢[PRAAx] neg (inst2 H i0 x ≐ zero)) :
    Γ ⊢[PRAAx] lt (uT H L i0 j0 x) (vT L i0 j0 x) := by
  have ep := natEq (pred_v (Γ := Γ) L i0 j0 x)
  have eu := natEq (pred_v_u H L (j0 := j0) hi0)
  ipra_le 𝔞 (wu H L i0 j0 x) with eu - ep

/-- No high index strictly between `u` and `v`. -/
theorem between_not_high (H L : PTm 2) {i0 j0 x i : PTm n} (hi0 : Γ ⊢[PRAAx] neg (inst2 H i0 x ≐ zero))
    (h1 : Γ ⊢[PRAAx] lt (uT H L i0 j0 x) i) (h2 : Γ ⊢[PRAAx] lt i (vT L i0 j0 x)) :
    Γ ⊢[PRAAx] inst2 H i x ≐ zero := by
  have ep := natEq (pred_v (Γ := Γ) L i0 j0 x)
  have eu := natEq (pred_v_u H L (j0 := j0) hi0)
  have hip : Γ ⊢[PRAAx] le i (pred (vT L i0 j0 x)) := by ipra_le sl h2 with ep
  have ek : Γ ⊢[PRAAx] pred (vT L i0 j0 x) ≐ i + monus (pred (vT L i0 j0 x)) i := eq_add_of_le hip
  have ek' := natEq ek
  have hk : Γ ⊢[PRAAx] lt (monus (pred (vT L i0 j0 x)) i) (wu H L i0 j0 x) := by ipra_le sl h1 with ek' - eu
  have z := ex_least (Hr H) hk
  have hi : Γ ⊢[PRAAx] monus (pred (vT L i0 j0 x)) (monus (pred (vT L i0 j0 x)) i) ≐ i :=
    monus_of_eq (ek.eqTrans (add_comm _ _))
  exact (congrInst2 H hi.eqSymm (.eqRefl _)).eqTrans ((Hr_at H _ _ x).eqSymm.eqTrans z)

/-- The crossing, assembled: a high index `i₀` before a low index `j₀` give `i₀ ≤ u < v ≤ j₀` with `u` high and
`v` low (and nothing high or low strictly between, by `between_not_high`, `between_not_low`). -/
theorem crossing (H L : PTm 2) {i0 j0 x : PTm n} (hi0 : Γ ⊢[PRAAx] neg (inst2 H i0 x ≐ zero))
    (hj0 : Γ ⊢[PRAAx] neg (inst2 L j0 x ≐ zero)) (hlt : Γ ⊢[PRAAx] lt i0 j0) :
    Γ ⊢[PRAAx] (neg (inst2 H (uT H L i0 j0 x) x ≐ zero) ⋏ neg (inst2 L (vT L i0 j0 x) x ≐ zero)) ⋏
      (le i0 (uT H L i0 j0 x) ⋏ lt (uT H L i0 j0 x) (vT L i0 j0 x) ⋏ le (vT L i0 j0 x) j0) :=
  .andI (.andI (u_high H L hi0) (v_low L hj0 hlt)) (.andI (u_ge H L hi0) (.andI (u_lt H L hi0) (v_le L hj0 hlt)))

end LeanProofs.IPRA.Foundations.CrossingSearch

export_ipra Common (monus_of_eq)
