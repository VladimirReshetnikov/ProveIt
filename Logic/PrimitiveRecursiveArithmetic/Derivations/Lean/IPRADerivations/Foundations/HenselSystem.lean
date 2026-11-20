import IPRADerivations.Foundations.HenselUniqueness

/-!
# Filtered lifting for polynomial systems over `ℤ`

Packet: `foundations/ipra_coherent_methods_2026-11-15`, `paper/sections/04_lifting.tex`, Theorem
`thm:filtered-lifting` ("Finite filtered lifting") for a system `P ∈ B[X_1, …, X_m]^m`, `B = ℤ`,
`F^k = q^k ℤ`: from `P(a) ∈ F^1` and `I − J(a) U ∈ F^1` (H), the iteration `b_{r+1} = b_r − U P(b_r)` (L)
satisfies `b_r − a ∈ F^1` and `P(b_r) ∈ F^{r+1}` (I). "Put `x = b_r`, `v = P(x)`, and `h = −U v` ... the
first term belongs to `F^{k+1}` by (H). The second belongs to `F^{k+1}` because `J(x) − J(a) ∈ F^1`."

The system is `P : Fin m → PE m` (polynomial expressions of `Analysis/PolynomialRemainder`), `U` an integer
`m × m` matrix; membership is an exact equation with an explicit witness vector.

* `corr`, `stepV`: `h = −U P(b)` and `b' = b + h`; `W`, `g`, `omega'`: the witnesses
  `W = U ω`, `g_{ij} = ∑_l σ_l ℓ^{ij}_l` (`J_{ij}(b) − J_{ij}(a) = q g_{ij}`) and
  `ω'_i = ∑_l E_{il} ω_l − ∑_j W_j g_{ij} + q^{K'} ∑_{j,l} W_j W_l τ^i_{jl}`;
* `step_system` (one step of (I)): from `J(a) U = I − q E`, `b − a = q σ`, `P(b) = q^{K'+1} ω`:
  `b' − a = q (σ − q^{K'} W)` and `P(b') = q^{K'+2} ω'`. The three sum identities are `sum_corr` (the
  correction against `J(b)`), `sum_inverse` (`J(a) U = I − q E` contracted with `ω`, by exchanging the sums)
  and `sum_quad`; the final combination was found by polynomial reduction;
* `seqV`, `witV`, `invariant_system` ((I) for every metalevel `r`): `b_r − a = q σ_r` and
  `P(b_r) = q^{r+1} ω_r`; at `r = N − 1`, `b_{N−1}` is a root of the system modulo `q^N`.

Derivative inverses are not recomputed; the only data are `a`, `U`, and the witnesses `E`, `w₀` of (H).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.HenselSystem

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.PolynomialRemainder (PE ev dv)
open LeanProofs.IPRA.Foundations.FilteredTaylor (pd tq ls taylor_exact diff_exact dv_eq zsum toZ_zsum toZ_zero)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k m : ℕ} {Γ : List (Fm PTm k)}

set_option hygiene false in
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

variable (P : Fin m → PE m) (U : Fin m → Fin m → ZT k)

/-- `J_{ij}(b) = ∂_j P_i(b)`. -/
abbrev jac (b : Fin m → ZT k) (i j : Fin m) : ZT k := ev (pd (P i) j) b

/-- The correction `h = −U P(b)`. -/
def corr (b : Fin m → ZT k) (j : Fin m) : ZT k := -(zsum fun l => U j l * ev (P l) b)

/-- One step of (L): `b' = b − U P(b)`. -/
def stepV (b : Fin m → ZT k) : Fin m → ZT k := fun i => b i + corr P U b i

/-- The Kronecker delta. -/
def kron (i l : Fin m) : ZT k := if i = l then ZT.natLit 1 else ZT.ofNat zero

/-- `W = U ω`. -/
def W (ω : Fin m → ZT k) (j : Fin m) : ZT k := zsum fun l => U j l * ω l

/-- `g_{ij} = ∑_l σ_l ℓ^{ij}_l`, the witness of `J_{ij}(b) − J_{ij}(a) ∈ q`. -/
def g (a b σ : Fin m → ZT k) (i j : Fin m) : ZT k := zsum fun l => σ l * ls (pd (P i) j) b a l

/-- The new witness `ω'`. -/
def omega' (a b σ ω : Fin m → ZT k) (E : Fin m → Fin m → ZT k) (qKp : PTm k) (i : Fin m) : ZT k :=
  zsum (fun l => E i l * ω l) + -(zsum fun j => W U ω j * g P a b σ i j) +
    ZT.ofNat qKp * zsum (fun j => zsum fun l => W U ω j * W U ω l * tq (P i) b (corr P U b) j l)

theorem kron_toZ (i l : Fin m) : ZT.toZ Γ (kron (k := k) i l) = if i = l then 1 else 0 := by
  unfold kron; split_ifs <;> simp [toZ_zero]

variable {P U}

section Step

variable {a b σ ω : Fin m → ZT k} {E : Fin m → Fin m → ZT k} {q K' : PTm k}

/-- `h_j = −q^{K'+1} W_j`. -/
theorem corr_toZ (hω : ∀ i, ZT.toZ Γ (ev (P i) b) = 𝔞 (pw q (succ K')) * ZT.toZ Γ (ω i)) (j : Fin m) :
    ZT.toZ Γ (corr P U b j) = -(𝔞 (pw q (succ K')) * ZT.toZ Γ (W U ω j)) := by
  simp only [corr, W, ZT.toZ_neg, toZ_zsum, ZT.toZ_mul, hω]
  rw [Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun l _ => by ring

/-- The correction against `J(b)`. -/
theorem sum_corr (hω : ∀ i, ZT.toZ Γ (ev (P i) b) = 𝔞 (pw q (succ K')) * ZT.toZ Γ (ω i))
    (hσ : ∀ l, ZT.toZ Γ (b l) - ZT.toZ Γ (a l) = 𝔞 q * ZT.toZ Γ (σ l)) (i : Fin m) :
    ∑ j, ZT.toZ Γ (corr P U b j) * ZT.toZ Γ (jac P b i j) =
      -𝔞 (pw q (succ K')) * ∑ j, ZT.toZ Γ (W U ω j) * ZT.toZ Γ (jac P a i j) -
        𝔞 (pw q (succ K')) * 𝔞 q * ∑ j, ZT.toZ Γ (W U ω j) * ZT.toZ Γ (g P a b σ i j) := by
  have hJ : ∀ j, ZT.toZ Γ (jac P b i j) = ZT.toZ Γ (jac P a i j) + 𝔞 q * ZT.toZ Γ (g P a b σ i j) := by
    intro j
    have d := diff_exact (Γ := Γ) (x := b) (y := a) (pd (P i) j)
    simp only [ZT.toZ_sub] at d
    simp only [g, toZ_zsum, ZT.toZ_mul, jac]
    rw [Finset.mul_sum]
    have : ZT.toZ Γ (ev (pd (P i) j) b) = ZT.toZ Γ (ev (pd (P i) j) a) +
        ∑ l, (ZT.toZ Γ (b l) - ZT.toZ Γ (a l)) * ZT.toZ Γ (ls (pd (P i) j) b a l) := by
      rw [← d]; ring
    rw [this]
    congr 1
    exact Finset.sum_congr rfl fun l _ => by rw [hσ l]; ring
  simp only [corr_toZ hω, hJ]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- `J(a) U = I − q E` contracted with `ω`. -/
theorem sum_inverse
    (hE : ∀ i l, ∑ j, ZT.toZ Γ (jac P a i j) * ZT.toZ Γ (U j l) =
      ZT.toZ Γ (kron (k := k) i l) - 𝔞 q * ZT.toZ Γ (E i l)) (i : Fin m) :
    ∑ j, ZT.toZ Γ (W U ω j) * ZT.toZ Γ (jac P a i j) =
      ZT.toZ Γ (ω i) - 𝔞 q * ∑ l, ZT.toZ Γ (E i l) * ZT.toZ Γ (ω l) := by
  have h1 : ∑ j, ZT.toZ Γ (W U ω j) * ZT.toZ Γ (jac P a i j) =
      ∑ l, ZT.toZ Γ (ω l) * ∑ j, ZT.toZ Γ (jac P a i j) * ZT.toZ Γ (U j l) := by
    simp only [W, toZ_zsum, ZT.toZ_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hk : ∑ l, ZT.toZ Γ (ω l) * ZT.toZ Γ (kron (k := k) i l) = ZT.toZ Γ (ω i) := by
    rw [Finset.sum_eq_single i]
    · simp [kron_toZ]
    · intro l _ hl; simp [kron_toZ, Ne.symm hl]
    · simp
  rw [h1]
  simp only [hE]
  have h2 : ∑ l, ZT.toZ Γ (ω l) * (ZT.toZ Γ (kron (k := k) i l) - 𝔞 q * ZT.toZ Γ (E i l)) =
      ∑ l, ZT.toZ Γ (ω l) * ZT.toZ Γ (kron (k := k) i l) - 𝔞 q * ∑ l, ZT.toZ Γ (E i l) * ZT.toZ Γ (ω l) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [h2, hk]

/-- The quadratic term. -/
theorem sum_quad (hω : ∀ i, ZT.toZ Γ (ev (P i) b) = 𝔞 (pw q (succ K')) * ZT.toZ Γ (ω i)) (i : Fin m) :
    ∑ j, ∑ l, ZT.toZ Γ (corr P U b j) * ZT.toZ Γ (corr P U b l) * ZT.toZ Γ (tq (P i) b (corr P U b) j l) =
      𝔞 (pw q (succ K')) * 𝔞 (pw q (succ K')) *
        ∑ j, ∑ l, ZT.toZ Γ (W U ω j) * ZT.toZ Γ (W U ω l) * ZT.toZ Γ (tq (P i) b (corr P U b) j l) := by
  simp only [corr_toZ hω]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- One step of (I) for a system. -/
theorem step_system
    (hE : ∀ i l, Γ ⊢[PRAAx] ZT.eq (zsum fun j => jac P a i j * U j l) (kron i l + -(ZT.ofNat q * E i l)))
    (hσ : ∀ l, Γ ⊢[PRAAx] ZT.eq (b l + -a l) (ZT.ofNat q * σ l))
    (hω : ∀ i, Γ ⊢[PRAAx] ZT.eq (ev (P i) b) (ZT.ofNat (pw q (succ K')) * ω i)) :
    (∀ l, Γ ⊢[PRAAx] ZT.eq (stepV P U b l + -a l)
      (ZT.ofNat q * (σ l + -(ZT.ofNat (pw q K') * W U ω l)))) ∧
    (∀ i, Γ ⊢[PRAAx] ZT.eq (ev (P i) (stepV P U b))
      (ZT.ofNat (pw q (succ (succ K'))) * omega' P U a b σ ω E (pw q K') i)) := by
  have hω' : ∀ i, ZT.toZ Γ (ev (P i) b) = 𝔞 (pw q (succ K')) * ZT.toZ Γ (ω i) := fun i => by
    have h := ZT.toZ_eq (hω i); simpa only [ZT.toZ_mul, ZT.toZ_ofNat] using h
  have hσ' : ∀ l, ZT.toZ Γ (b l) - ZT.toZ Γ (a l) = 𝔞 q * ZT.toZ Γ (σ l) := fun l => by
    have h := ZT.toZ_eq (hσ l)
    simp only [ZT.toZ_add, ZT.toZ_neg, ZT.toZ_mul, ZT.toZ_ofNat] at h
    linear_combination h
  have hE' : ∀ i l, ∑ j, ZT.toZ Γ (jac P a i j) * ZT.toZ Γ (U j l) =
      ZT.toZ Γ (kron (k := k) i l) - 𝔞 q * ZT.toZ Γ (E i l) := fun i l => by
    have h := ZT.toZ_eq (hE i l)
    simp only [toZ_zsum, ZT.toZ_add, ZT.toZ_neg, ZT.toZ_mul, ZT.toZ_ofNat] at h
    rw [h]; ring
  have eK := natEq (pw_succ (Γ := Γ) q K')
  have eK1 := natEq (pw_succ (Γ := Γ) q (succ K'))
  simp only [Q.mk_mul, map_mul] at eK eK1
  refine ⟨fun l => ZT.derive ?_, fun i => ZT.derive ?_⟩
  · have hc := corr_toZ (U := U) hω' l
    simp only [stepV, ZT.toZ_add, ZT.toZ_neg, ZT.toZ_mul, ZT.toZ_ofNat, hc]
    linear_combination hσ' l - ZT.toZ Γ (W U ω l) * eK
  · have eT := taylor_exact (Γ := Γ) (x := b) (v := corr P U b) (P i)
    have eV := dv_eq (Γ := Γ) (x := b) (v := corr P U b) (P i)
    have s1 := sum_corr (U := U) hω' hσ' i
    have s2 := sum_inverse (ω := ω) hE' i
    have s3 := sum_quad (U := U) hω' i
    simp only [Analysis.PolynomialRemainder.rem, ZT.toZ_sub] at eT
    rw [show stepV P U b = fun i => b i + corr P U b i from rfl]
    simp only [omega', toZ_zsum, ZT.toZ_add, ZT.toZ_neg, ZT.toZ_mul, ZT.toZ_ofNat]
    linear_combination eT + eV + s1 - 𝔞 (pw q (succ K')) * s2 + s3 + hω' i +
      (𝔞 (pw q (succ K')) * ∑ j, ∑ l, ZT.toZ Γ (W U ω j) * ZT.toZ Γ (W U ω l) *
        ZT.toZ Γ (tq (P i) b (corr P U b) j l)) * eK +
      (-𝔞 (pw q K') * (∑ j, ∑ l, ZT.toZ Γ (W U ω j) * ZT.toZ Γ (W U ω l) *
        ZT.toZ Γ (tq (P i) b (corr P U b) j l)) - ∑ l, ZT.toZ Γ (E i l) * ZT.toZ Γ (ω l) +
        ∑ j, ZT.toZ Γ (W U ω j) * ZT.toZ Γ (g P a b σ i j)) * eK1

end Step

variable (P U)

/-- The iterates `b_r` of (L). -/
def seqV (a : Fin m → ZT k) : ℕ → Fin m → ZT k
  | 0 => a
  | r + 1 => stepV P U (seqV a r)

/-- The witnesses `σ_r`, `ω_r`. -/
def witV (a w₀ : Fin m → ZT k) (E : Fin m → Fin m → ZT k) (q : PTm k) :
    ℕ → (Fin m → ZT k) × (Fin m → ZT k)
  | 0 => (fun _ => ZT.ofNat zero, w₀)
  | r + 1 =>
    ((fun l => (witV a w₀ E q r).1 l + -(ZT.ofNat (pw q (num r)) * W U (witV a w₀ E q r).2 l)),
      omega' P U a (seqV P U a r) (witV a w₀ E q r).1 (witV a w₀ E q r).2 E (pw q (num r)))

variable {P U}

/-- (I) for a system: for every `r`, `b_r − a = q σ_r` and `P(b_r) = q^{r+1} ω_r`. -/
theorem invariant_system {a w₀ : Fin m → ZT k} {E : Fin m → Fin m → ZT k} {q : PTm k}
    (hE : ∀ i l, Γ ⊢[PRAAx] ZT.eq (zsum fun j => jac P a i j * U j l) (kron i l + -(ZT.ofNat q * E i l)))
    (hP : ∀ i, Γ ⊢[PRAAx] ZT.eq (ev (P i) a) (ZT.ofNat q * w₀ i)) (r : ℕ) :
    (∀ l, Γ ⊢[PRAAx] ZT.eq (seqV P U a r l + -a l) (ZT.ofNat q * (witV P U a w₀ E q r).1 l)) ∧
    (∀ i, Γ ⊢[PRAAx] ZT.eq (ev (P i) (seqV P U a r))
      (ZT.ofNat (pw q (num (r + 1))) * (witV P U a w₀ E q r).2 i)) := by
  induction r with
  | zero =>
    refine ⟨fun l => ZT.derive ?_, fun i => ZT.derive ?_⟩
    · simp only [seqV, witV, ZT.toZ_add, ZT.toZ_neg, ZT.toZ_mul, ZT.toZ_ofNat, Q.mk_zero, map_zero]
      ring
    · have e := ZT.toZ_eq (hP i)
      have e1 := natEq (pw_one (Γ := Γ) q)
      simp only [ZT.toZ_mul, ZT.toZ_ofNat] at e
      simp only [seqV, witV, ZT.toZ_mul, ZT.toZ_ofNat]
      change ZT.toZ Γ (ev (P i) a) = 𝔞 (pw q one) * ZT.toZ Γ (w₀ i)
      linear_combination e - ZT.toZ Γ (w₀ i) * e1
  | succ r ih =>
    have hb : ∀ l, Γ ⊢[PRAAx] ZT.eq (seqV P U a r l + -a l) (ZT.ofNat q * (witV P U a w₀ E q r).1 l) := ih.1
    have hω : ∀ i, Γ ⊢[PRAAx] ZT.eq (ev (P i) (seqV P U a r))
        (ZT.ofNat (pw q (succ (num r))) * (witV P U a w₀ E q r).2 i) := ih.2
    exact step_system (K' := num r) hE hb hω

end LeanProofs.IPRA.Foundations.HenselSystem
