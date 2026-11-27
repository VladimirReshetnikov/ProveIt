import IPRADerivations.Core.IntCertificates
import IPRADerivations.Core.Pairing
import IPRADerivations.Foundations.SignedCone

/-!
# Absolute values, maximum norms and row-sum norms of integer terms

A signed rational array of iPRA is an array of integer terms (`ZT`, pairs of natural terms read as differences)
over a positive natural denominator. This module gives the norms of such arrays as natural terms and connects
them with the algebra of two-sided bounds of `Foundations/SignedCone`:

* `nnCone`: the values of terms (`Nonneg Γ`) form a cone of the ring of differences `Groth (Q Γ)`. Halving
  (`nn_half`) holds because every element of the ring is the value of an integer term (`exists_zt`) and
  `2a ≤ 2b` gives `a ≤ b`; `nn_anti`: a natural sum that is zero has zero summands.
* `abs u = (u⁺ ∸ u⁻) + (u⁻ ∸ u⁺)` is `|u|`, and `abs_bd : |u| ≤ abs u` holds in the sense of `Bd`;
  `bd_of_le`: a derived `σ · abs u ≤ c` is the two-sided bound `|σ u| ≤ c`; `le_abs_of_bd`: conversely a
  two-sided bound `|σ u| ≤ c − e` is the derivation of `σ · abs u + e ≤ c` (by the cases `u⁺ ≤ u⁻`, `u⁻ ≤ u⁺`).
* `natSum f = ∑_i f i` for natural terms, `rowSum M i = ∑_k abs (M i k)` is the absolute row sum of a matrix of
  integer terms, and `rowBd_of_le`: derived bounds `σ · rowSum M i ≤ A` for all rows give the row-sum bound
  `RowBd` of the matrix `σ M`.
* `nrm v = max_i abs (v i)` is the maximum norm, with `nrm_le`, `mul_nrm_le` (a bound of all components bounds
  the norm, also with a scale factor) and `le_nrm` (every component is bounded by the norm).
-/

namespace LeanProofs.IPRA.Foundations.SignedNorms

open_ipra
open LeanProofs.IPRA.Foundations.SignedCone

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The values of terms form a cone -/

/-- Every element of the ring of differences is the value of an integer term. -/
theorem exists_zt (z : Groth (Q Γ)) : ∃ u : ZT n, z = ZT.toZ Γ u := by
  refine Groth.ind (fun a b => ?_) z
  refine Q.ind (fun s => ?_) a
  refine Q.ind (fun t => ?_) b
  exact ⟨⟨s, t⟩, Groth.mk_eq_sub _ _⟩

theorem nn_half {z : Groth (Q Γ)} (h : Nonneg Γ (2 * z)) : Nonneg Γ z := by
  obtain ⟨u, rfl⟩ := exists_zt z
  obtain ⟨d, hd⟩ := h
  refine nn_zle0 (zle_of_comb_two (Groth.ι (Q.mk Γ d)) ?_ (nn_term d))
  rw [ZT.toZ_natLit, Nat.cast_zero, sub_zero]
  exact hd

theorem nn_anti {z : Groth (Q Γ)} (h : Nonneg Γ z) (h' : Nonneg Γ (-z)) : z = 0 := by
  obtain ⟨s, rfl⟩ := h
  obtain ⟨t, ht⟩ := h'
  have e : Γ ⊢[PRAAx] s + t ≐ zero := by
    apply deriveNat
    simp only [Q.mk_add, Q.mk_zero, map_add, map_zero]
    linear_combination -ht
  have e0 := natEq (add_eq_zero_left e)
  simpa only [Q.mk_zero, map_zero] using e0

/-- The values of terms form a cone of the ring of differences. -/
theorem nnCone : Cone (Nonneg Γ) :=
  ⟨nn_zero, nn_one, nn_add, nn_mul, nn_half, nn_anti⟩

/-! ## The absolute value -/

/-- `|u|` as a natural term. -/
def abs (u : ZT n) : PTm n := monus u.pos u.neg + monus u.neg u.pos

@[simp] theorem subst_abs {m : ℕ} (σ : Fin n → PTm m) (u : ZT n) :
    Syn.subst σ (abs u) = abs (u.subst σ) := by
  simp only [abs, PTm.subst_add, PTm.subst_monus, ZT.subst]

theorem toZ_abs (u : ZT n) :
    𝔞 (abs u) = (Groth.ι (Q.mk Γ (monus u.pos u.neg)) + Groth.ι (Q.mk Γ (monus u.neg u.pos)) : Groth (Q Γ)) := by
  simp only [abs, Q.mk_add, map_add]

/-- `|u| ≤ abs u`: both `abs u − u = 2 (u⁻ ∸ u⁺)` and `abs u + u = 2 (u⁺ ∸ u⁻)` are values of terms. -/
theorem abs_bd (u : ZT n) : Bd (Nonneg Γ) (ZT.toZ Γ u) (𝔞 (abs u)) := by
  have m := natEq (monus_max (Γ := Γ) u.pos u.neg)
  simp only [Q.mk_add, map_add] at m
  refine ⟨?_, ?_⟩
  · refine Cone.of_eq (nn_add (nn_term (monus u.neg u.pos)) (nn_term (monus u.neg u.pos))) ?_
    rw [toZ_abs, toZ_def]
    linear_combination -m
  · refine Cone.of_eq (nn_add (nn_term (monus u.pos u.neg)) (nn_term (monus u.pos u.neg))) ?_
    rw [toZ_abs, toZ_def]
    linear_combination m

/-- A derived bound `σ · abs u ≤ c` as a two-sided bound of `σ u`. -/
theorem bd_of_le {u : ZT n} {σ c : PTm n} (h : Γ ⊢[PRAAx] le (σ * abs u) c) :
    Bd (Nonneg Γ) (𝔞 σ * ZT.toZ Γ u) (𝔞 c) := by
  refine ((abs_bd u).smul nnCone (nn_term σ)).mono nnCone (Cone.of_eq (nn_sl h) ?_)
  simp only [sl_def, Q.mk_mul, map_mul]

/-- A derived bound `abs u ≤ c` as a two-sided bound of `u`. -/
theorem bd_of_le₁ {u : ZT n} {c : PTm n} (h : Γ ⊢[PRAAx] le (abs u) c) :
    Bd (Nonneg Γ) (ZT.toZ Γ u) (𝔞 c) :=
  (abs_bd u).mono nnCone (Cone.of_eq (nn_sl h) (sl_def h))

/-- A derived bound `σ · abs u + e ≤ c` as the two-sided bound `|σ u| ≤ c − e`. -/
theorem bd_of_le_add {u : ZT n} {σ e c : PTm n} (h : Γ ⊢[PRAAx] le (σ * abs u + e) c) :
    Bd (Nonneg Γ) (𝔞 σ * ZT.toZ Γ u) (𝔞 c - 𝔞 e) := by
  refine ((abs_bd u).smul nnCone (nn_term σ)).mono nnCone (Cone.of_eq (nn_sl h) ?_)
  rw [sl_def, Q.mk_add, map_add, Q.mk_mul, map_mul]; ring

/-- A two-sided bound `|σ u| ≤ c − e` gives the derivation of `σ · abs u + e ≤ c`. -/
theorem le_abs_of_bd {u : ZT n} {σ e c : PTm n}
    (h : Bd (Nonneg Γ) (𝔞 σ * ZT.toZ Γ u) (𝔞 c - 𝔞 e)) : Γ ⊢[PRAAx] le (σ * abs u + e) c := by
  have h₁ : Γ ⊢[PRAAx] le (σ * u.pos + e) (c + σ * u.neg) := by
    refine le_of_comb _ ?_ h.1
    simp only [toZ_def, Q.mk_add, Q.mk_mul, map_add, map_mul]
    ring
  have h₂ : Γ ⊢[PRAAx] le (σ * u.neg + e) (c + σ * u.pos) := by
    refine le_of_comb _ ?_ h.2
    simp only [toZ_def, Q.mk_add, Q.mk_mul, map_add, map_mul]
    ring
  refine .orE (le_total u.pos u.neg) ?_ ?_
  · -- `u⁺ ≤ u⁻`: `abs u = u⁻ ∸ u⁺`.
    have hle : (le u.pos u.neg :: Γ) ⊢[PRAAx] le u.pos u.neg := Prf.hyp0
    have z := natEq (show (le u.pos u.neg :: Γ) ⊢[PRAAx] monus u.pos u.neg ≐ zero from hle)
    have w := natEq (eq_add_of_le hle)
    have h₂' := h₂.wk (ψ := le u.pos u.neg)
    show (le u.pos u.neg :: Γ) ⊢[PRAAx] le (σ * (monus u.pos u.neg + monus u.neg u.pos) + e) c
    ipra_le sl h₂' with 𝔞 σ * w - 𝔞 σ * z
  · -- `u⁻ ≤ u⁺`: `abs u = u⁺ ∸ u⁻`.
    have hle : (le u.neg u.pos :: Γ) ⊢[PRAAx] le u.neg u.pos := Prf.hyp0
    have z := natEq (show (le u.neg u.pos :: Γ) ⊢[PRAAx] monus u.neg u.pos ≐ zero from hle)
    have w := natEq (eq_add_of_le hle)
    have h₁' := h₁.wk (ψ := le u.neg u.pos)
    show (le u.neg u.pos :: Γ) ⊢[PRAAx] le (σ * (monus u.pos u.neg + monus u.neg u.pos) + e) c
    ipra_le sl h₁' with 𝔞 σ * w - 𝔞 σ * z

/-- A two-sided bound `|σ u| ≤ c` gives the derivation of `σ · abs u ≤ c`. -/
theorem le_abs_of_bd₀ {u : ZT n} {σ c : PTm n} (h : Bd (Nonneg Γ) (𝔞 σ * ZT.toZ Γ u) (𝔞 c)) :
    Γ ⊢[PRAAx] le (σ * abs u) c := by
  have h' : Bd (Nonneg Γ) (𝔞 σ * ZT.toZ Γ u) (𝔞 c - 𝔞 (zero : PTm n)) :=
    h.congr rfl (by simp only [Q.mk_zero, map_zero, sub_zero])
  exact le_congr (add_zero _) (.eqRefl _) (le_abs_of_bd h')

/-- A two-sided bound `|u| ≤ c` gives the derivation of `abs u ≤ c`. -/
theorem le_abs_of_bd₁ {u : ZT n} {c : PTm n} (h : Bd (Nonneg Γ) (ZT.toZ Γ u) (𝔞 c)) :
    Γ ⊢[PRAAx] le (abs u) c := by
  have e : Γ ⊢[PRAAx] succ zero * abs u ≐ abs u := by ipra_ring
  refine le_congr e (.eqRefl _) (le_abs_of_bd₀ (h.congr ?_ rfl))
  rw [Q.mk_one, map_one]; ring

/-- The absolute value of the integer zero is bounded by every term. -/
theorem abs_zero_le (c : PTm n) : Γ ⊢[PRAAx] le (abs (ZT.natLit 0 : ZT n)) c :=
  le_abs_of_bd₁ ((Bd.zero (nn_term c)).congr (by simp only [ZT.toZ_natLit, Nat.cast_zero]) rfl)

/-! ## Finite sums of natural terms and row sums -/

/-- `∑_i f i` for natural terms. -/
def natSum : {d : ℕ} → (Fin d → PTm n) → PTm n
  | 0, _ => zero
  | _ + 1, f => f 0 + natSum fun i => f i.succ

theorem mk_natSum : {d : ℕ} → (f : Fin d → PTm n) →
    (𝔞 (natSum f) : Groth (Q Γ)) = ∑ i, Groth.ι (Q.mk Γ (f i))
  | 0, _ => by simp only [natSum, Q.mk_zero, map_zero, Finset.univ_eq_empty, Finset.sum_empty]
  | d + 1, f => by
    rw [Fin.sum_univ_succ, ← mk_natSum fun i => f i.succ]
    simp only [natSum, Q.mk_add, map_add]

@[simp] theorem subst_natSum {m : ℕ} (σ : Fin n → PTm m) : {d : ℕ} → (f : Fin d → PTm n) →
    Syn.subst σ (natSum f) = natSum fun i => Syn.subst σ (f i)
  | 0, _ => by simp only [natSum, ConciseIPRA.PTm.subst_zero]
  | d + 1, f => by
    simp only [natSum, PTm.subst_add]
    rw [subst_natSum σ fun i => f i.succ]

/-- The absolute row sum `∑_k |M i k|` of a matrix of integer terms. -/
def rowSum {d : ℕ} (M : Fin d → Fin d → ZT n) (i : Fin d) : PTm n := natSum fun k => abs (M i k)

@[simp] theorem subst_rowSum {m d : ℕ} (σ : Fin n → PTm m) (M : Fin d → Fin d → ZT n) (i : Fin d) :
    Syn.subst σ (rowSum M i) = rowSum (fun i k => (M i k).subst σ) i := by
  simp only [rowSum, subst_natSum, subst_abs]

/-- Derived bounds `σ · rowSum M i ≤ A` of the rows give the row-sum bound of the matrix `σ M`. -/
theorem rowBd_of_le {d : ℕ} {M : Fin d → Fin d → ZT n} {σ A : PTm n}
    (h : ∀ i, Γ ⊢[PRAAx] le (σ * rowSum M i) A) :
    RowBd (Nonneg Γ) (fun i k => 𝔞 σ * ZT.toZ Γ (M i k)) (𝔞 A) := by
  refine ⟨fun i k => 𝔞 σ * 𝔞 (abs (M i k)), fun i k => (abs_bd (M i k)).smul nnCone (nn_term σ), fun i => ?_⟩
  refine Cone.of_eq (nn_sl (h i)) ?_
  simp only [sl_def, Q.mk_mul, map_mul, rowSum, mk_natSum, Finset.mul_sum]

/-- Derived bounds `rowSum M i ≤ A` of the rows give the row-sum bound of `M`. -/
theorem rowBd_of_le₁ {d : ℕ} {M : Fin d → Fin d → ZT n} {A : PTm n}
    (h : ∀ i, Γ ⊢[PRAAx] le (rowSum M i) A) :
    RowBd (Nonneg Γ) (fun i k => ZT.toZ Γ (M i k)) (𝔞 A) := by
  refine ⟨fun i k => 𝔞 (abs (M i k)), fun i k => abs_bd (M i k), fun i => ?_⟩
  refine Cone.of_eq (nn_sl (h i)) ?_
  simp only [sl_def, rowSum, mk_natSum]

/-- A row-sum bound of a matrix that is entrywise equal. -/
theorem rowBd_congr {R : Type*} [CommRing R] {P : R → Prop} {d : ℕ} {M M' : Fin d → Fin d → R} {A A' : R}
    (h : RowBd P M A) (e : ∀ i k, M i k = M' i k) (eA : A = A') : RowBd P M' A' := by
  have : M = M' := funext fun i => funext fun k => e i k
  subst this; subst eA; exact h

/-! ## The maximum norm -/

/-- `max(a, b) = a + (b ∸ a)`. -/
def mx (a b : PTm n) : PTm n := a + monus b a

theorem le_mx_left (a b : PTm n) : Γ ⊢[PRAAx] le a (mx a b) := le_add_right a _

theorem le_mx_right (a b : PTm n) : Γ ⊢[PRAAx] le b (mx a b) :=
  Common.le_add_monus b a

theorem mx_le {a b c : PTm n} (ha : Γ ⊢[PRAAx] le a c) (hb : Γ ⊢[PRAAx] le b c) : Γ ⊢[PRAAx] le (mx a b) c := by
  refine .orE (le_total a b) ?_ ?_
  · exact le_congr (eq_add_of_le Prf.hyp0) (.eqRefl c) hb.wk
  · have z : (le b a :: Γ) ⊢[PRAAx] monus b a ≐ zero := Prf.hyp0
    exact le_congr ((congrAdd (.eqRefl a) z).eqTrans (add_zero a)).eqSymm (.eqRefl c) ha.wk

/-- The maximum of finitely many natural terms (`0` for none). -/
def maxFin : {d : ℕ} → (Fin d → PTm n) → PTm n
  | 0, _ => zero
  | _ + 1, f => mx (f 0) (maxFin fun i => f i.succ)

theorem maxFin_le : {d : ℕ} → {f : Fin d → PTm n} → {c : PTm n} → (∀ i, Γ ⊢[PRAAx] le (f i) c) →
    (Γ ⊢[PRAAx] le (maxFin f) c)
  | 0, _, c, _ => zero_le c
  | _ + 1, _, _, h => mx_le (h 0) (maxFin_le fun i => h i.succ)

theorem le_maxFin : {d : ℕ} → (f : Fin d → PTm n) → (i : Fin d) → (Γ ⊢[PRAAx] le (f i) (maxFin f))
  | 0, _, i => i.elim0
  | d + 1, f, i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact le_mx_left _ _
    · exact le_trans (le_maxFin (fun i => f i.succ) j) (le_mx_right _ _)

/-- The maximum norm `max_i |v i|` of a vector of integer terms. -/
def nrm {d : ℕ} (v : Fin d → ZT n) : PTm n := maxFin fun i => abs (v i)

/-- A bound of all components bounds the norm. -/
theorem nrm_le {d : ℕ} {v : Fin d → ZT n} {c : PTm n} (h : ∀ i, Γ ⊢[PRAAx] le (abs (v i)) c) :
    Γ ⊢[PRAAx] le (nrm v) c := maxFin_le h

/-- Every component is bounded by the norm. -/
theorem le_nrm {d : ℕ} (v : Fin d → ZT n) (i : Fin d) : Γ ⊢[PRAAx] le (abs (v i)) (nrm v) :=
  le_maxFin (fun i => abs (v i)) i

theorem mul_mx_le {σ a b c : PTm n} (ha : Γ ⊢[PRAAx] le (σ * a) c) (hb : Γ ⊢[PRAAx] le (σ * b) c) :
    Γ ⊢[PRAAx] le (σ * mx a b) c := by
  refine .orE (le_total a b) ?_ ?_
  · exact le_congr (congrMul (.eqRefl σ) (eq_add_of_le Prf.hyp0)) (.eqRefl c) hb.wk
  · have z : (le b a :: Γ) ⊢[PRAAx] monus b a ≐ zero := Prf.hyp0
    exact le_congr (congrMul (.eqRefl σ) ((congrAdd (.eqRefl a) z).eqTrans (add_zero a)).eqSymm) (.eqRefl c)
      ha.wk

theorem mul_maxFin_le : {d : ℕ} → {f : Fin d → PTm n} → {σ c : PTm n} → (∀ i, Γ ⊢[PRAAx] le (σ * f i) c) →
    (Γ ⊢[PRAAx] le (σ * maxFin f) c)
  | 0, _, σ, c, _ => le_congr (mul_zero σ).eqSymm (.eqRefl c) (zero_le c)
  | _ + 1, _, _, _, h => mul_mx_le (h 0) (mul_maxFin_le fun i => h i.succ)

/-- A scaled bound of all components bounds the scaled norm: `σ ‖v‖ ≤ c`. -/
theorem mul_nrm_le {d : ℕ} {v : Fin d → ZT n} {σ c : PTm n} (h : ∀ i, Γ ⊢[PRAAx] le (σ * abs (v i)) c) :
    Γ ⊢[PRAAx] le (σ * nrm v) c := mul_maxFin_le h

end LeanProofs.IPRA.Foundations.SignedNorms
