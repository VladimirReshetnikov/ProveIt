import IPRADerivations.Foundations.HenselSystem

/-!
# Uniqueness of the filtered lift for polynomial systems over `ℤ`

Packet: `foundations/ipra_coherent_methods_2026-11-15`, `paper/sections/04_lifting.tex`, Theorem
`thm:filtered-lifting`, the uniqueness clause for a system: "`0 = P(x) − P(y) = J(y) d + R` ...
Multiplying by `U` and rearranging gives `d = (I − U J(a)) d − U (J(y) − J(a)) d − U R`" (2), so
`d ∈ (F^k)^m` gives `d ∈ (F^{k+1})^m`.

For a system `P : Fin m → PE m` over the integers with `F^k = q^k ℤ` (`Foundations/HenselSystem`), with the
left inverse `U J(a) = I − q E`:

* `taylor_y` (per equation): `∑_l d_l J_{il}(y) + ∑_{j,l} d_j d_l τ^i_{jl} = q^N (s^x_i − s^y_i)`, from the
  Taylor identity at `y` (`FilteredTaylor.taylor_exact`, with `HenselUniqueness.toZ_ev_congr`);
* `sum_left`, `sum_right`, `sum_lin_E`, `sum_lin_g`, `sum_quad'`: the contraction with `U` and the
  substitution `d = q^{K'+1} ω`;
* `unique_step_system`: if `P(x)`, `P(y)` lie in `q^N`, `y − a = q σ`, `U J(a) = I − q E`,
  `x − y = q^{K'+1} ω` and `q^N = q · q^{K'+1} · q_r`, then `x − y = q^{K'+2} ω''` with an explicit
  witness (the final combination found by polynomial reduction);
* `unique_root_system`: two roots of the system modulo `q^N`, both congruent to `a` modulo `q`, agree modulo
  `q^{j+1}` for every `j + 1 ≤ N`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.HenselSystemUniqueness

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.PolynomialRemainder (PE ev dv)
open LeanProofs.IPRA.Foundations.FilteredTaylor (pd tq ls taylor_exact diff_exact dv_eq zsum toZ_zsum toZ_zero)
open LeanProofs.IPRA.Foundations.HenselUniqueness (toZ_ev_congr pw_split)
open LeanProofs.IPRA.Foundations.HenselSystem (jac kron kron_toZ g)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k m : ℕ} {Γ : List (Fm PTm k)}

set_option hygiene false in
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

/-- The difference `d = x − y`. -/
def dvec (x y : Fin m → ZT k) (l : Fin m) : ZT k := x l + -y l

variable {P : Fin m → PE m} {U : Fin m → Fin m → ZT k}

/-- The new witness `ω''`. -/
def omega'' (P : Fin m → PE m) (U E : Fin m → Fin m → ZT k) (a x y σ ω sx sy : Fin m → ZT k)
    (qKp qr : PTm k) (p : Fin m) : ZT k :=
  zsum (fun l => E p l * ω l) + -(zsum fun i => U p i * zsum fun l => g P a y σ i l * ω l) +
    -(ZT.ofNat qKp * zsum fun i => U p i * zsum fun j => zsum fun l => ω j * ω l * tq (P i) y (dvec x y) j l) +
    ZT.ofNat qr * zsum fun i => U p i * (sx i + -sy i)

section Step

variable {a x y σ ω sx sy : Fin m → ZT k} {E : Fin m → Fin m → ZT k} {q Nt K' qr : PTm k}

/-- The Taylor identity at `y`, one equation. -/
theorem taylor_y (hx : ∀ i, ZT.toZ Γ (ev (P i) x) = 𝔞 (pw q Nt) * ZT.toZ Γ (sx i))
    (hy : ∀ i, ZT.toZ Γ (ev (P i) y) = 𝔞 (pw q Nt) * ZT.toZ Γ (sy i)) (i : Fin m) :
    ∑ l, ZT.toZ Γ (dvec x y l) * ZT.toZ Γ (jac P y i l) +
      ∑ j, ∑ l, ZT.toZ Γ (dvec x y j) * ZT.toZ Γ (dvec x y l) * ZT.toZ Γ (tq (P i) y (dvec x y) j l) =
      𝔞 (pw q Nt) * (ZT.toZ Γ (sx i) + -ZT.toZ Γ (sy i)) := by
  have eT := taylor_exact (Γ := Γ) (x := y) (v := dvec x y) (P i)
  have eV := dv_eq (Γ := Γ) (x := y) (v := dvec x y) (P i)
  have ec := toZ_ev_congr (Γ := Γ) (x := fun l => y l + dvec x y l) (y := x)
    (fun l => by simp only [dvec, ZT.toZ_add, ZT.toZ_neg]; ring) (P i)
  simp only [Analysis.PolynomialRemainder.rem, ZT.toZ_sub] at eT
  rw [ec, hx i, hy i, eV] at eT
  simp only [jac]
  linear_combination -eT

/-- `∑_i U_{pi} A_i` from `U J(a) = I − q E` and `J(y) = J(a) + q g`. -/
theorem sum_left
    (hσ : ∀ l, ZT.toZ Γ (y l) - ZT.toZ Γ (a l) = 𝔞 q * ZT.toZ Γ (σ l))
    (hE : ∀ p l, ∑ i, ZT.toZ Γ (U p i) * ZT.toZ Γ (jac P a i l) =
      ZT.toZ Γ (kron (k := k) p l) - 𝔞 q * ZT.toZ Γ (E p l)) (p : Fin m) :
    ∑ i, ZT.toZ Γ (U p i) * ∑ l, ZT.toZ Γ (dvec x y l) * ZT.toZ Γ (jac P y i l) =
      ZT.toZ Γ (dvec x y p) - 𝔞 q * ∑ l, ZT.toZ Γ (E p l) * ZT.toZ Γ (dvec x y l) +
        𝔞 q * ∑ i, ZT.toZ Γ (U p i) * ∑ l, ZT.toZ Γ (g P a y σ i l) * ZT.toZ Γ (dvec x y l) := by
  have hJ : ∀ i l, ZT.toZ Γ (jac P y i l) = ZT.toZ Γ (jac P a i l) + 𝔞 q * ZT.toZ Γ (g P a y σ i l) := by
    intro i l
    have d := diff_exact (Γ := Γ) (x := y) (y := a) (pd (P i) l)
    simp only [ZT.toZ_sub] at d
    simp only [g, toZ_zsum, ZT.toZ_mul, jac]
    rw [Finset.mul_sum]
    have : ZT.toZ Γ (ev (pd (P i) l) y) = ZT.toZ Γ (ev (pd (P i) l) a) +
        ∑ t, (ZT.toZ Γ (y t) - ZT.toZ Γ (a t)) * ZT.toZ Γ (ls (pd (P i) l) y a t) := by
      rw [← d]; ring
    rw [this]
    congr 1
    exact Finset.sum_congr rfl fun t _ => by rw [hσ t]; ring
  -- split `J(y)`
  have h1 : ∑ i, ZT.toZ Γ (U p i) * ∑ l, ZT.toZ Γ (dvec x y l) * ZT.toZ Γ (jac P y i l) =
      ∑ l, ZT.toZ Γ (dvec x y l) * ∑ i, ZT.toZ Γ (U p i) * ZT.toZ Γ (jac P a i l) +
        𝔞 q * ∑ i, ZT.toZ Γ (U p i) * ∑ l, ZT.toZ Γ (g P a y σ i l) * ZT.toZ Γ (dvec x y l) := by
    simp only [hJ, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hk : ∑ l, ZT.toZ Γ (dvec x y l) * ZT.toZ Γ (kron (k := k) p l) = ZT.toZ Γ (dvec x y p) := by
    rw [Finset.sum_eq_single p]
    · simp [kron_toZ]
    · intro l _ hl; simp [kron_toZ, Ne.symm hl]
    · simp
  rw [h1]
  simp only [hE]
  have h2 : ∑ l, ZT.toZ Γ (dvec x y l) * (ZT.toZ Γ (kron (k := k) p l) - 𝔞 q * ZT.toZ Γ (E p l)) =
      ∑ l, ZT.toZ Γ (dvec x y l) * ZT.toZ Γ (kron (k := k) p l) -
        𝔞 q * ∑ l, ZT.toZ Γ (E p l) * ZT.toZ Γ (dvec x y l) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [h2, hk]

/-- `∑_i U_{pi} A_i = q^N ∑_i U_{pi} (s^x_i − s^y_i) − ∑_i U_{pi} H_i`. -/
theorem sum_right (hx : ∀ i, ZT.toZ Γ (ev (P i) x) = 𝔞 (pw q Nt) * ZT.toZ Γ (sx i))
    (hy : ∀ i, ZT.toZ Γ (ev (P i) y) = 𝔞 (pw q Nt) * ZT.toZ Γ (sy i)) (p : Fin m) :
    ∑ i, ZT.toZ Γ (U p i) * ∑ l, ZT.toZ Γ (dvec x y l) * ZT.toZ Γ (jac P y i l) =
      𝔞 (pw q Nt) * ∑ i, ZT.toZ Γ (U p i) * (ZT.toZ Γ (sx i) + -ZT.toZ Γ (sy i)) -
        ∑ i, ZT.toZ Γ (U p i) * ∑ j, ∑ l, ZT.toZ Γ (dvec x y j) * ZT.toZ Γ (dvec x y l) *
          ZT.toZ Γ (tq (P i) y (dvec x y) j l) := by
  have h : ∀ i, ∑ l, ZT.toZ Γ (dvec x y l) * ZT.toZ Γ (jac P y i l) =
      𝔞 (pw q Nt) * (ZT.toZ Γ (sx i) + -ZT.toZ Γ (sy i)) -
        ∑ j, ∑ l, ZT.toZ Γ (dvec x y j) * ZT.toZ Γ (dvec x y l) * ZT.toZ Γ (tq (P i) y (dvec x y) j l) :=
    fun i => by linear_combination taylor_y (P := P) hx hy i
  simp only [h]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

variable (hd : ∀ l, ZT.toZ Γ (dvec x y l) = 𝔞 (pw q (succ K')) * ZT.toZ Γ (ω l))
include hd

theorem sum_lin_E (p : Fin m) :
    ∑ l, ZT.toZ Γ (E p l) * ZT.toZ Γ (dvec x y l) = 𝔞 (pw q (succ K')) * ∑ l, ZT.toZ Γ (E p l) * ZT.toZ Γ (ω l) := by
  simp only [hd, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem sum_lin_g (p : Fin m) :
    ∑ i, ZT.toZ Γ (U p i) * ∑ l, ZT.toZ Γ (g P a y σ i l) * ZT.toZ Γ (dvec x y l) =
      𝔞 (pw q (succ K')) * ∑ i, ZT.toZ Γ (U p i) * ∑ l, ZT.toZ Γ (g P a y σ i l) * ZT.toZ Γ (ω l) := by
  simp only [hd, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring

theorem sum_quad' (p : Fin m) :
    ∑ i, ZT.toZ Γ (U p i) * ∑ j, ∑ l, ZT.toZ Γ (dvec x y j) * ZT.toZ Γ (dvec x y l) *
        ZT.toZ Γ (tq (P i) y (dvec x y) j l) =
      𝔞 (pw q (succ K')) * 𝔞 (pw q (succ K')) * ∑ i, ZT.toZ Γ (U p i) * ∑ j, ∑ l, ZT.toZ Γ (ω j) *
        ZT.toZ Γ (ω l) * ZT.toZ Γ (tq (P i) y (dvec x y) j l) := by
  simp only [hd, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring

omit hd in
/-- One step of the uniqueness argument for a system. -/
theorem unique_step_system
    (hx : ∀ i, Γ ⊢[PRAAx] ZT.eq (ev (P i) x) (ZT.ofNat (pw q Nt) * sx i))
    (hy : ∀ i, Γ ⊢[PRAAx] ZT.eq (ev (P i) y) (ZT.ofNat (pw q Nt) * sy i))
    (hσ : ∀ l, Γ ⊢[PRAAx] ZT.eq (y l + -a l) (ZT.ofNat q * σ l))
    (hE : ∀ p l, Γ ⊢[PRAAx] ZT.eq (zsum fun i => U p i * jac P a i l) (kron p l + -(ZT.ofNat q * E p l)))
    (hdd : ∀ l, Γ ⊢[PRAAx] ZT.eq (x l + -y l) (ZT.ofNat (pw q (succ K')) * ω l))
    (hN : Γ ⊢[PRAAx] pw q Nt ≐ q * pw q (succ K') * qr) (p : Fin m) :
    Γ ⊢[PRAAx] ZT.eq (x p + -y p)
      (ZT.ofNat (pw q (succ (succ K'))) * omega'' P U E a x y σ ω sx sy (pw q K') qr p) := by
  have hx' : ∀ i, ZT.toZ Γ (ev (P i) x) = 𝔞 (pw q Nt) * ZT.toZ Γ (sx i) := fun i => by
    have h := ZT.toZ_eq (hx i); simpa only [ZT.toZ_mul, ZT.toZ_ofNat] using h
  have hy' : ∀ i, ZT.toZ Γ (ev (P i) y) = 𝔞 (pw q Nt) * ZT.toZ Γ (sy i) := fun i => by
    have h := ZT.toZ_eq (hy i); simpa only [ZT.toZ_mul, ZT.toZ_ofNat] using h
  have hσ' : ∀ l, ZT.toZ Γ (y l) - ZT.toZ Γ (a l) = 𝔞 q * ZT.toZ Γ (σ l) := fun l => by
    have h := ZT.toZ_eq (hσ l)
    simp only [ZT.toZ_add, ZT.toZ_neg, ZT.toZ_mul, ZT.toZ_ofNat] at h
    linear_combination h
  have hE' : ∀ p l, ∑ i, ZT.toZ Γ (U p i) * ZT.toZ Γ (jac P a i l) =
      ZT.toZ Γ (kron (k := k) p l) - 𝔞 q * ZT.toZ Γ (E p l) := fun p l => by
    have h := ZT.toZ_eq (hE p l)
    simp only [toZ_zsum, ZT.toZ_add, ZT.toZ_neg, ZT.toZ_mul, ZT.toZ_ofNat] at h
    rw [h]; ring
  have hd' : ∀ l, ZT.toZ Γ (dvec x y l) = 𝔞 (pw q (succ K')) * ZT.toZ Γ (ω l) := fun l => by
    have h := ZT.toZ_eq (hdd l)
    simpa only [dvec, ZT.toZ_mul, ZT.toZ_ofNat] using h
  have hdp : ZT.toZ Γ (dvec x y p) = ZT.toZ Γ (x p) + -ZT.toZ Γ (y p) := by
    simp only [dvec, ZT.toZ_add, ZT.toZ_neg]
  have L1 := sum_left (x := x) hσ' hE' p
  have L2 := sum_right (U := U) hx' hy' p
  have L3 := sum_lin_E (E := E) hd' p
  have L4 := sum_lin_g (P := P) (U := U) (a := a) (σ := σ) hd' p
  have L5 := sum_quad' (P := P) (U := U) hd' p
  have eK := natEq (pw_succ (Γ := Γ) q K')
  have eK1 := natEq (pw_succ (Γ := Γ) q (succ K'))
  have eN := natEq hN
  simp only [Q.mk_mul, map_mul] at eK eK1 eN
  refine ZT.derive ?_
  simp only [omega'', toZ_zsum, ZT.toZ_add, ZT.toZ_neg, ZT.toZ_mul, ZT.toZ_ofNat]
  linear_combination -L1 + L2 + 𝔞 q * L3 - 𝔞 q * L4 - L5 -
    𝔞 (pw q (succ K')) * (∑ i, ZT.toZ Γ (U p i) * ∑ j, ∑ l, ZT.toZ Γ (ω j) * ZT.toZ Γ (ω l) *
      ZT.toZ Γ (tq (P i) y (dvec x y) j l)) * eK +
    (∑ i, ZT.toZ Γ (U p i) * (ZT.toZ Γ (sx i) + -ZT.toZ Γ (sy i))) * eN +
    (𝔞 (pw q K') * (∑ i, ZT.toZ Γ (U p i) * ∑ j, ∑ l, ZT.toZ Γ (ω j) * ZT.toZ Γ (ω l) *
        ZT.toZ Γ (tq (P i) y (dvec x y) j l)) -
      𝔞 qr * (∑ i, ZT.toZ Γ (U p i) * (ZT.toZ Γ (sx i) + -ZT.toZ Γ (sy i))) -
      (∑ l, ZT.toZ Γ (E p l) * ZT.toZ Γ (ω l)) +
      (∑ i, ZT.toZ Γ (U p i) * ∑ l, ZT.toZ Γ (g P a y σ i l) * ZT.toZ Γ (ω l))) * eK1 - hdp

end Step

/-- Uniqueness for a system: two roots modulo `q^N`, both congruent to `a` modulo `q`, agree modulo `q^{j+1}`
for every `j + 1 ≤ N`. -/
theorem unique_root_system {a x y σx σy sx sy : Fin m → ZT k} {E : Fin m → Fin m → ZT k} {q : PTm k} {N : ℕ}
    (hx : ∀ i, Γ ⊢[PRAAx] ZT.eq (ev (P i) x) (ZT.ofNat (pw q (num N)) * sx i))
    (hy : ∀ i, Γ ⊢[PRAAx] ZT.eq (ev (P i) y) (ZT.ofNat (pw q (num N)) * sy i))
    (hσx : ∀ l, Γ ⊢[PRAAx] ZT.eq (x l + -a l) (ZT.ofNat q * σx l))
    (hσy : ∀ l, Γ ⊢[PRAAx] ZT.eq (y l + -a l) (ZT.ofNat q * σy l))
    (hE : ∀ p l, Γ ⊢[PRAAx] ZT.eq (zsum fun i => U p i * jac P a i l) (kron p l + -(ZT.ofNat q * E p l))) :
    ∀ j : ℕ, j + 1 ≤ N → ∃ δ : Fin m → ZT k,
      ∀ l, Γ ⊢[PRAAx] ZT.eq (x l + -y l) (ZT.ofNat (pw q (num (j + 1))) * δ l) := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨fun l => σx l + -σy l, fun l => ZT.derive ?_⟩
    have e1 := ZT.toZ_eq (hσx l)
    have e2 := ZT.toZ_eq (hσy l)
    have e3 := natEq (pw_one (Γ := Γ) q)
    simp only [ZT.toZ_add, ZT.toZ_neg, ZT.toZ_mul, ZT.toZ_ofNat] at e1 e2 ⊢
    change _ = 𝔞 (pw q one) * _
    linear_combination e1 - e2 - (ZT.toZ Γ (σx l) - ZT.toZ Γ (σy l)) * e3
  | succ j ih =>
    intro hj
    obtain ⟨δ, hδ⟩ := ih (by omega)
    obtain ⟨E', hE'⟩ : ∃ E', N = j + 2 + E' := ⟨N - (j + 2), by omega⟩
    have hN : Γ ⊢[PRAAx] pw q (num N) ≐ q * pw q (succ (num j)) * pw q (num E') := by
      rw [hE']; exact pw_split q j E'
    exact ⟨_, fun p => unique_step_system (K' := num j) hx hy hσy hE hδ hN p⟩

end LeanProofs.IPRA.Foundations.HenselSystemUniqueness
