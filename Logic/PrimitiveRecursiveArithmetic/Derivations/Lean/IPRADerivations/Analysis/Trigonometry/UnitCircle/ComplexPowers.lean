import IPRADerivations.Core.IntCertificates
import IPRADerivations.Core.Pairing
import IPRADerivations.Core.Powers
import IPRADerivations.Core.Gcd

/-!
# Powers of complex integers and moduli without square roots

The reusable base of the cosine and sine names of `Analysis/Trigonometry/UnitCircle`. A complex (Gaussian)
integer is a pair `x + i y` of integer terms (`ZT`, `Core/Integers`), and `|x + i y| ≤ A` for a natural term `A`
is the quantifier-free formula `x² + y² ≤ A²` (`nle x y A`), so no square root is needed.

Moduli (`Core/IntCertificates` certificates):

* `nle_of_comb`, `nle_sl`: the certificate form of `nle`, with slack `A² − (x² + y²)`;
* `nle_mul`: `|z₁| ≤ A₁`, `|z₂| ≤ A₂` give `|z₁ z₂| ≤ A₁ A₂`, from `|z₁ z₂|² = |z₁|² |z₂|²`;
* `nle_scale`, `nle_neg`: `|c z| ≤ c A` for a natural `c`, and `|−z| ≤ A`;
* `nle_add`: the triangle inequality `|z₁ + z₂| ≤ A₁ + A₂` (`triangle` of `Core/IntOrder`);
* `nle_of`: transport along equal values and a larger bound; `nle_of_eq`: `|z|² = A²` gives `|z| ≤ A`;
* `nle_cancel`: `|m z| ≤ m A` with `m ≥ 1` gives `|z| ≤ A`.
* `nle_swap`, `zle_of_nle`: `|y + i x| ≤ A`, and the real part is at most the modulus, `x ≤ A`.

Powers: `(p + i q)^j = cRe j + i cIm j` for an integer base `p + i q`, by simultaneous primitive recursion on
the two coded pairs `⟨x⁺, x⁻⟩`, `⟨y⁺, y⁻⟩` of the positive and negative parts (`sim₁`, `sim₂` of `Core/Pairing`);
the exponent `j` is a term, so it may be a variable of a formula.

* `cRe_zero`, `cIm_zero`, `cRe_succ`, `cIm_succ`: the values `1`, `0` and the recurrence
  `x' = p x − q y`, `y' = q x + p y` in the ring of differences;
* `subst_cRe`, `subst_cIm`, `subst_zle`: substitution, for inductions on the exponent;
* `cnorm_zero`, `cnorm_step`: `|p + i q|² = M²` gives `|(p + i q)^j|² = (M^j)²`, base case and step.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.ComplexPowers

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.Variance (ad)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Moduli without square roots -/

/-- `|x + i y| ≤ A`: `x² + y² ≤ A²`. -/
abbrev nle (x y : ZT n) (A : PTm n) : Fm PTm n := zle (ZT.sq x + ZT.sq y) (ZT.ofNat (A * A))

theorem nle_slack (x y : ZT n) (A : PTm n) :
    ZT.toZ Γ (ZT.ofNat (A * A)) - ZT.toZ Γ (ZT.sq x + ZT.sq y) =
      𝔟 A * 𝔟 A - (ZT.toZ Γ x ^ 2 + ZT.toZ Γ y ^ 2) := by
  simp only [ZT.toZ_ofNat, ZT.toZ_add, ZT.toZ_sq, Q.mk_mul, map_mul]

/-- `|x + i y| ≤ A` from a certificate for `A² − (x² + y²)`. -/
theorem nle_of_comb {x y : ZT n} {A : PTm n} (z : Groth (Q Γ))
    (hz : 𝔟 A * 𝔟 A - (ZT.toZ Γ x ^ 2 + ZT.toZ Γ y ^ 2) = z) (h : Nonneg Γ z) : Γ ⊢[PRAAx] nle x y A :=
  zle_of_comb z ((nle_slack x y A).trans hz) h

/-- The slack of a derived `|x + i y| ≤ A`. -/
theorem nle_sl {x y : ZT n} {A : PTm n} (h : Γ ⊢[PRAAx] nle x y A) :
    zsl h = 𝔟 A * 𝔟 A - (ZT.toZ Γ x ^ 2 + ZT.toZ Γ y ^ 2) :=
  nle_slack x y A

/-- `|z₁ z₂| ≤ A₁ A₂`. -/
theorem nle_mul {x₁ y₁ x₂ y₂ : ZT n} {A₁ A₂ : PTm n} (h₁ : Γ ⊢[PRAAx] nle x₁ y₁ A₁)
    (h₂ : Γ ⊢[PRAAx] nle x₂ y₂ A₂) :
    Γ ⊢[PRAAx] nle (x₁ * x₂ - y₁ * y₂) (x₁ * y₂ + y₁ * x₂) (A₁ * A₂) := by
  refine nle_of_comb (zsl h₁ * (𝔟 A₂ * 𝔟 A₂) + (ZT.toZ Γ x₁ ^ 2 + ZT.toZ Γ y₁ ^ 2) * zsl h₂) ?_
    (nn_add (nn_mul (nn_zsl _) (nn_mul (nn_term _) (nn_term _)))
      (nn_mul (nn_add (nn_zsq _) (nn_zsq _)) (nn_zsl _)))
  rw [nle_sl h₁, nle_sl h₂]
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, Q.mk_mul, map_mul]
  ring

/-- `|c z| ≤ c A` for a natural `c`. -/
theorem nle_scale {x y : ZT n} {A : PTm n} (c : PTm n) (h : Γ ⊢[PRAAx] nle x y A) :
    Γ ⊢[PRAAx] nle (ZT.ofNat c * x) (ZT.ofNat c * y) (c * A) := by
  refine nle_of_comb (𝔟 c * 𝔟 c * zsl h) ?_ (nn_mul (nn_mul (nn_term _) (nn_term _)) (nn_zsl _))
  rw [nle_sl h]
  simp only [ZT.toZ_mul, ZT.toZ_ofNat, Q.mk_mul, map_mul]
  ring

/-- `|−z| ≤ A`. -/
theorem nle_neg {x y : ZT n} {A : PTm n} (h : Γ ⊢[PRAAx] nle x y A) : Γ ⊢[PRAAx] nle (-x) (-y) A := by
  refine nle_of_comb (zsl h) ?_ (nn_zsl _)
  rw [nle_sl h]
  simp only [ZT.toZ_neg]
  ring

/-- The triangle inequality `|z₁ + z₂| ≤ A₁ + A₂`. -/
theorem nle_add {x₁ y₁ x₂ y₂ : ZT n} {A₁ A₂ : PTm n} (h₁ : Γ ⊢[PRAAx] nle x₁ y₁ A₁)
    (h₂ : Γ ⊢[PRAAx] nle x₂ y₂ A₂) : Γ ⊢[PRAAx] nle (x₁ + x₂) (y₁ + y₂) (A₁ + A₂) :=
  triangle h₁ h₂

/-- Transport along equal values and a larger bound. -/
theorem nle_of {x y x' y' : ZT n} {A A' : PTm n} (h : Γ ⊢[PRAAx] nle x y A)
    (hx : ZT.toZ Γ x' = ZT.toZ Γ x) (hy : ZT.toZ Γ y' = ZT.toZ Γ y) (hA : Γ ⊢[PRAAx] le A A') :
    Γ ⊢[PRAAx] nle x' y' A' := by
  refine nle_of_comb (zsl h + sl hA * (𝔟 A' + 𝔟 A)) ?_
    (nn_add (nn_zsl _) (nn_mul (nn_sl _) (nn_add (nn_term _) (nn_term _))))
  rw [nle_sl h, sl_def]
  linear_combination (-(ZT.toZ Γ x' + ZT.toZ Γ x)) * hx - (ZT.toZ Γ y' + ZT.toZ Γ y) * hy

/-- `|z|² = A²` gives `|z| ≤ A`. -/
theorem nle_of_eq {x y : ZT n} {A : PTm n} (h : ZT.toZ Γ x ^ 2 + ZT.toZ Γ y ^ 2 = 𝔟 A * 𝔟 A) :
    Γ ⊢[PRAAx] nle x y A :=
  nle_of_comb 0 (by rw [h, sub_self]) nn_zero

/-- `|y + i x| ≤ A` from `|x + i y| ≤ A`. -/
theorem nle_swap {x y : ZT n} {A : PTm n} (h : Γ ⊢[PRAAx] nle x y A) : Γ ⊢[PRAAx] nle y x A := by
  refine nle_of_comb (zsl h) ?_ (nn_zsl _)
  rw [nle_sl h]
  ring

/-- The real part is at most the modulus: `|x + i y| ≤ A` gives `x ≤ A`. -/
theorem zle_of_nle {x y : ZT n} {A : PTm n} (h : Γ ⊢[PRAAx] nle x y A) :
    Γ ⊢[PRAAx] zle x (ZT.ofNat A) := by
  refine .orE (le_total x.pos x.neg) ?_ ?_
  · -- `x ≤ 0 ≤ A`
    have e := natEq (eq_add_of_le (Prf.hyp0 (Ax := PRAAx) (Γ := Γ) (φ := le x.pos x.neg)))
    refine zle_of_toZ (monus x.neg x.pos + A) ?_
    rw [toZ_def x, ZT.toZ_ofNat]
    simp only [Q.mk_add, map_add] at e ⊢
    linear_combination -e
  · -- `x = σ ≥ 0` with `σ² ≤ A²`
    have e := natEq (eq_add_of_le (Prf.hyp0 (Ax := PRAAx) (Γ := Γ) (φ := le x.neg x.pos)))
    simp only [Q.mk_add, map_add] at e
    have h' := h.wk (ψ := le x.neg x.pos)
    have tσ : ZT.toZ (le x.neg x.pos :: Γ) x = Groth.ι (Q.mk _ (monus x.pos x.neg)) := by
      rw [toZ_def]
      linear_combination e
    have hs : (le x.neg x.pos :: Γ) ⊢[PRAAx] le (monus x.pos x.neg * monus x.pos x.neg) (A * A) := by
      refine le_of_comb (zsl h' + ZT.toZ _ y ^ 2) ?_ (nn_add (nn_zsl _) (nn_zsq _))
      rw [nle_sl h', tσ]
      simp only [Q.mk_mul, map_mul]
      ring
    have e₂ := natEq (eq_add_of_le (nat_sqrt_mono hs))
    simp only [Q.mk_add, map_add] at e₂
    refine zle_of_toZ (monus A (monus x.pos x.neg)) ?_
    rw [tσ, ZT.toZ_ofNat]
    linear_combination -e₂

/-- The square of an integer value as the value of a natural term. -/
theorem sq_val (x : ZT n) : ZT.toZ Γ x ^ 2 = 𝔟 (ad x.pos x.neg) * 𝔟 (ad x.pos x.neg) := by
  rw [← ZT.toZ_sq, sq_nat, Q.mk_mul, map_mul]

/-- `|m z| ≤ m A` with `m ≥ 1` gives `|z| ≤ A`. -/
theorem nle_cancel {x y : ZT n} {A m : PTm n}
    (h : Γ ⊢[PRAAx] nle (ZT.ofNat (succ m) * x) (ZT.ofNat (succ m) * y) (succ m * A)) :
    Γ ⊢[PRAAx] nle x y A := by
  have hx := sq_val (Γ := Γ) x
  have hy := sq_val (Γ := Γ) y
  simp only [Q.mk_add, map_add] at hx hy
  have h₁ : Γ ⊢[PRAAx] le
      (succ m * (succ m * (ad x.pos x.neg * ad x.pos x.neg + ad y.pos y.neg * ad y.pos y.neg)))
      (succ m * (succ m * (A * A))) := by
    refine le_of_comb (zsl h) ?_ (nn_zsl h)
    rw [nle_sl h]
    simp only [ZT.toZ_mul, ZT.toZ_ofNat, Q.mk_add, Q.mk_mul, map_add, map_mul]
    linear_combination 𝔟 (succ m) * 𝔟 (succ m) * hx + 𝔟 (succ m) * 𝔟 (succ m) * hy
  have h₂ := mul_le_cancel (mul_le_cancel h₁)
  refine nle_of_comb (sl h₂) ?_ (nn_sl _)
  rw [sl_def]
  simp only [Q.mk_add, Q.mk_mul, map_add, map_mul]
  linear_combination -hx - hy

/-! ## Substitution -/

@[simp] theorem subst_zle {m : ℕ} (σ : Fin n → PTm m) (u v : ZT n) :
    (zle u v).subst σ = zle (u.subst σ) (v.subst σ) := by
  simp [zle, ZT.subst]

@[simp] theorem subst_mk {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    (⟨a, b⟩ : ZT n).subst σ = ⟨Syn.subst σ a, Syn.subst σ b⟩ := rfl

/-! ## Powers of a complex integer -/

/-- Step of the powers. Variables: `0 = j`, `1 = ⟨x⁺, x⁻⟩`, `2 = ⟨y⁺, y⁻⟩`, `3, 4 = p⁺, p⁻`, `5, 6 = q⁺, q⁻`;
`x' = p x − q y`. -/
abbrev sU : PTm 7 :=
  pairT (var 3 * fstT (var 1) + var 4 * sndT (var 1) + var 5 * sndT (var 2) + var 6 * fstT (var 2))
    (var 3 * sndT (var 1) + var 4 * fstT (var 1) + var 5 * fstT (var 2) + var 6 * sndT (var 2))

/-- `y' = q x + p y`. -/
abbrev sV : PTm 7 :=
  pairT (var 5 * fstT (var 1) + var 6 * sndT (var 1) + var 3 * fstT (var 2) + var 4 * sndT (var 2))
    (var 5 * sndT (var 1) + var 6 * fstT (var 1) + var 3 * sndT (var 2) + var 4 * fstT (var 2))

/-- The initial values `1 = ⟨1, 0⟩` and `0 = ⟨0, 0⟩`. -/
abbrev bU : PTm 4 := pairT one zero
abbrev bV : PTm 4 := pairT zero zero

/-- The coded real part `⟨x⁺, x⁻⟩` of `(p + i q)^j`, `p = p₁ − p₂`, `q = q₁ − q₂`. -/
def cU (p₁ p₂ q₁ q₂ j : PTm n) : PTm n := sim₁ bU bV sU sV j ![p₁, p₂, q₁, q₂]

/-- The coded imaginary part `⟨y⁺, y⁻⟩` of `(p + i q)^j`. -/
def cV (p₁ p₂ q₁ q₂ j : PTm n) : PTm n := sim₂ bU bV sU sV j ![p₁, p₂, q₁, q₂]

/-- `Re (re + i im)^j`. -/
def cRe (re im : ZT n) (j : PTm n) : ZT n :=
  ⟨fstT (cU re.pos re.neg im.pos im.neg j), sndT (cU re.pos re.neg im.pos im.neg j)⟩

/-- `Im (re + i im)^j`. -/
def cIm (re im : ZT n) (j : PTm n) : ZT n :=
  ⟨fstT (cV re.pos re.neg im.pos im.neg j), sndT (cV re.pos re.neg im.pos im.neg j)⟩

theorem cps_subst {m : ℕ} (σ : Fin n → PTm m) (a b c d : PTm n) :
    (fun i => Syn.subst σ ((![a, b, c, d] : Fin 4 → PTm n) i)) =
      ![Syn.subst σ a, Syn.subst σ b, Syn.subst σ c, Syn.subst σ d] := by
  funext i; fin_cases i <;> rfl

@[simp] theorem subst_cU {m : ℕ} (σ : Fin n → PTm m) (p₁ p₂ q₁ q₂ j : PTm n) :
    Syn.subst σ (cU p₁ p₂ q₁ q₂ j) =
      cU (Syn.subst σ p₁) (Syn.subst σ p₂) (Syn.subst σ q₁) (Syn.subst σ q₂) (Syn.subst σ j) := by
  unfold cU
  rw [subst_sim₁]
  exact congrArg (sim₁ bU bV sU sV (Syn.subst σ j)) (cps_subst σ p₁ p₂ q₁ q₂)

@[simp] theorem subst_cV {m : ℕ} (σ : Fin n → PTm m) (p₁ p₂ q₁ q₂ j : PTm n) :
    Syn.subst σ (cV p₁ p₂ q₁ q₂ j) =
      cV (Syn.subst σ p₁) (Syn.subst σ p₂) (Syn.subst σ q₁) (Syn.subst σ q₂) (Syn.subst σ j) := by
  unfold cV
  rw [subst_sim₂]
  exact congrArg (sim₂ bU bV sU sV (Syn.subst σ j)) (cps_subst σ p₁ p₂ q₁ q₂)

@[simp] theorem subst_cRe {m : ℕ} (σ : Fin n → PTm m) (re im : ZT n) (j : PTm n) :
    (cRe re im j).subst σ = cRe (re.subst σ) (im.subst σ) (Syn.subst σ j) := by
  show (⟨Syn.subst σ (fstT (cU re.pos re.neg im.pos im.neg j)),
    Syn.subst σ (sndT (cU re.pos re.neg im.pos im.neg j))⟩ : ZT m) = _
  simp only [subst_fstT, subst_sndT, subst_cU]
  rfl

@[simp] theorem subst_cIm {m : ℕ} (σ : Fin n → PTm m) (re im : ZT n) (j : PTm n) :
    (cIm re im j).subst σ = cIm (re.subst σ) (im.subst σ) (Syn.subst σ j) := by
  show (⟨Syn.subst σ (fstT (cV re.pos re.neg im.pos im.neg j)),
    Syn.subst σ (sndT (cV re.pos re.neg im.pos im.neg j))⟩ : ZT m) = _
  simp only [subst_fstT, subst_sndT, subst_cV]
  rfl

/-! ## The defining equations -/

theorem cU_zero (p₁ p₂ q₁ q₂ : PTm n) : Γ ⊢[PRAAx] cU p₁ p₂ q₁ q₂ zero ≐ pairT one zero := by
  have h := sim₁_zero (Γ := Γ) bU bV sU sV ![p₁, p₂, q₁, q₂]
  simp only [subst_pairT, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at h
  exact h

theorem cV_zero (p₁ p₂ q₁ q₂ : PTm n) : Γ ⊢[PRAAx] cV p₁ p₂ q₁ q₂ zero ≐ pairT zero zero := by
  have h := sim₂_zero (Γ := Γ) bU bV sU sV ![p₁, p₂, q₁, q₂]
  simp only [subst_pairT, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at h
  exact h

theorem cU_succ (p₁ p₂ q₁ q₂ j : PTm n) :
    Γ ⊢[PRAAx] cU p₁ p₂ q₁ q₂ (succ j) ≐
      pairT
        (p₁ * fstT (cU p₁ p₂ q₁ q₂ j) + p₂ * sndT (cU p₁ p₂ q₁ q₂ j) + q₁ * sndT (cV p₁ p₂ q₁ q₂ j) +
          q₂ * fstT (cV p₁ p₂ q₁ q₂ j))
        (p₁ * sndT (cU p₁ p₂ q₁ q₂ j) + p₂ * fstT (cU p₁ p₂ q₁ q₂ j) + q₁ * fstT (cV p₁ p₂ q₁ q₂ j) +
          q₂ * sndT (cV p₁ p₂ q₁ q₂ j)) := by
  have h := sim₁_succ (Γ := Γ) bU bV sU sV ![p₁, p₂, q₁, q₂] j
  simp only [subst_pairT, subst_fstT, subst_sndT, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Fin.cases_zero,
    finCases_one, finCases_two, finCases_three, finCases_four, finCases_five] at h
  exact h

theorem cV_succ (p₁ p₂ q₁ q₂ j : PTm n) :
    Γ ⊢[PRAAx] cV p₁ p₂ q₁ q₂ (succ j) ≐
      pairT
        (q₁ * fstT (cU p₁ p₂ q₁ q₂ j) + q₂ * sndT (cU p₁ p₂ q₁ q₂ j) + p₁ * fstT (cV p₁ p₂ q₁ q₂ j) +
          p₂ * sndT (cV p₁ p₂ q₁ q₂ j))
        (q₁ * sndT (cU p₁ p₂ q₁ q₂ j) + q₂ * fstT (cU p₁ p₂ q₁ q₂ j) + p₁ * sndT (cV p₁ p₂ q₁ q₂ j) +
          p₂ * fstT (cV p₁ p₂ q₁ q₂ j)) := by
  have h := sim₂_succ (Γ := Γ) bU bV sU sV ![p₁, p₂, q₁, q₂] j
  simp only [subst_pairT, subst_fstT, subst_sndT, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Fin.cases_zero,
    finCases_one, finCases_two, finCases_three, finCases_four, finCases_five] at h
  exact h

/-- `(p + i q)^0 = 1`. -/
theorem cRe_zero (re im : ZT n) : ZT.toZ Γ (cRe re im zero) = 1 := by
  have h := cU_zero (Γ := Γ) re.pos re.neg im.pos im.neg
  have e₁ := natEq h.fstE
  have e₂ := natEq h.sndE
  simp only [Q.mk_one, Q.mk_zero, map_one, map_zero] at e₁ e₂
  show (𝔟 (fstT (cU re.pos re.neg im.pos im.neg zero)) - 𝔟 (sndT (cU re.pos re.neg im.pos im.neg zero)) :
    Groth (Q Γ)) = 1
  linear_combination e₁ - e₂

theorem cIm_zero (re im : ZT n) : ZT.toZ Γ (cIm re im zero) = 0 := by
  have h := cV_zero (Γ := Γ) re.pos re.neg im.pos im.neg
  have e₁ := natEq h.fstE
  have e₂ := natEq h.sndE
  simp only [Q.mk_zero, map_zero] at e₁ e₂
  show (𝔟 (fstT (cV re.pos re.neg im.pos im.neg zero)) - 𝔟 (sndT (cV re.pos re.neg im.pos im.neg zero)) :
    Groth (Q Γ)) = 0
  linear_combination e₁ - e₂

/-- `Re z^{j+1} = p Re z^j − q Im z^j`. -/
theorem cRe_succ (re im : ZT n) (j : PTm n) :
    ZT.toZ Γ (cRe re im (succ j)) =
      ZT.toZ Γ re * ZT.toZ Γ (cRe re im j) - ZT.toZ Γ im * ZT.toZ Γ (cIm re im j) := by
  have h := cU_succ (Γ := Γ) re.pos re.neg im.pos im.neg j
  have e₁ := natEq h.fstE
  have e₂ := natEq h.sndE
  simp only [Q.mk_add, Q.mk_mul, map_add, map_mul] at e₁ e₂
  show (𝔟 (fstT (cU re.pos re.neg im.pos im.neg (succ j))) -
        𝔟 (sndT (cU re.pos re.neg im.pos im.neg (succ j))) : Groth (Q Γ)) =
      (𝔟 re.pos - 𝔟 re.neg) *
          (𝔟 (fstT (cU re.pos re.neg im.pos im.neg j)) - 𝔟 (sndT (cU re.pos re.neg im.pos im.neg j))) -
        (𝔟 im.pos - 𝔟 im.neg) *
          (𝔟 (fstT (cV re.pos re.neg im.pos im.neg j)) - 𝔟 (sndT (cV re.pos re.neg im.pos im.neg j)))
  linear_combination e₁ - e₂

/-- `Im z^{j+1} = q Re z^j + p Im z^j`. -/
theorem cIm_succ (re im : ZT n) (j : PTm n) :
    ZT.toZ Γ (cIm re im (succ j)) =
      ZT.toZ Γ im * ZT.toZ Γ (cRe re im j) + ZT.toZ Γ re * ZT.toZ Γ (cIm re im j) := by
  have h := cV_succ (Γ := Γ) re.pos re.neg im.pos im.neg j
  have e₁ := natEq h.fstE
  have e₂ := natEq h.sndE
  simp only [Q.mk_add, Q.mk_mul, map_add, map_mul] at e₁ e₂
  show (𝔟 (fstT (cV re.pos re.neg im.pos im.neg (succ j))) -
        𝔟 (sndT (cV re.pos re.neg im.pos im.neg (succ j))) : Groth (Q Γ)) =
      (𝔟 im.pos - 𝔟 im.neg) *
          (𝔟 (fstT (cU re.pos re.neg im.pos im.neg j)) - 𝔟 (sndT (cU re.pos re.neg im.pos im.neg j))) +
        (𝔟 re.pos - 𝔟 re.neg) *
          (𝔟 (fstT (cV re.pos re.neg im.pos im.neg j)) - 𝔟 (sndT (cV re.pos re.neg im.pos im.neg j)))
  linear_combination e₁ - e₂

/-! ## The modulus of a power -/

/-- `|z^0|² = (M^0)²`. -/
theorem cnorm_zero (re im : ZT n) (M : PTm n) :
    ZT.toZ Γ (cRe re im zero) ^ 2 + ZT.toZ Γ (cIm re im zero) ^ 2 = 𝔟 (pw M zero) * 𝔟 (pw M zero) := by
  have e := natEq (pw_zero (Γ := Γ) M)
  simp only [Q.mk_one, map_one] at e
  rw [cRe_zero, cIm_zero, e]
  ring

/-- `|z|² = M²` and `|z^j|² = (M^j)²` give `|z^{j+1}|² = (M^{j+1})²`. -/
theorem cnorm_step {re im : ZT n} {M j : PTm n}
    (hM : ZT.toZ Γ re ^ 2 + ZT.toZ Γ im ^ 2 = 𝔟 M * 𝔟 M)
    (ih : ZT.toZ Γ (cRe re im j) ^ 2 + ZT.toZ Γ (cIm re im j) ^ 2 = 𝔟 (pw M j) * 𝔟 (pw M j)) :
    ZT.toZ Γ (cRe re im (succ j)) ^ 2 + ZT.toZ Γ (cIm re im (succ j)) ^ 2 =
      𝔟 (pw M (succ j)) * 𝔟 (pw M (succ j)) := by
  have e := natEq (pw_succ (Γ := Γ) M j)
  simp only [Q.mk_mul, map_mul] at e
  rw [cRe_succ, cIm_succ, e]
  linear_combination (ZT.toZ Γ (cRe re im j) ^ 2 + ZT.toZ Γ (cIm re im j) ^ 2) * hM + 𝔟 M * 𝔟 M * ih

end LeanProofs.IPRA.Analysis.ComplexPowers
