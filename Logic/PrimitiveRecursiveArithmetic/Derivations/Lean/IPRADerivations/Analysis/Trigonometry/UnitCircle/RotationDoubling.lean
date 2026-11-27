import IPRADerivations.Analysis.Trigonometry.UnitCircle.RotationRemainder

/-!
# The Cauchy rate of the unit-circle names: doubling the stage

Packet: `probability/expected_value_ipra_2026-11-16`, `paper/sections/13_fourier_applications.tex`: "The sine and
cosine names are obtained from finite ... sums with explicit remainders", i.e. the names of `φ_X` are regular,
with a primitive recursive modulus. For the unit-circle names of
`Analysis/Trigonometry/UnitCircle/RotationRemainder`, `z_n(u) = w^n` with `w = g/ḡ`, `g = a + i b`, the stage
`2n` is `z_{2n}(u) = (w'²)^n` with `w' = g'/ḡ'`, `g' = 2a + i b`, and

  `g'² = 4a g − b²`,  hence  `g'⁴ N − g² N'² = 2i b³ g'² g`  (`N = |g|²`, `N' = |g'|²`),

so `|w'² − w| = 2b³/(N' √N) ≤ b³/(2a³)` and, both sides being of modulus one, `|z_{2n} − z_n| ≤ n |w'² − w|`.

* `cU_congr`, `cV_congr`, `cRe_congr`, `cIm_congr`, `rotRe_congr`, `rotIm_congr`: the powers respect provable
  equality of the exponent and of the natural data;
* `cpow_sq` (the power law): `(z²)^k = z^{2k}` for the complex-integer powers, by induction on `k`;
* `del_nle`: `|a (g'⁴ N − g² N'²)| ≤ 2b³ N' N`, from `|g'²| ≤ N'` and `|a g| ≤ N`;
* `doubling` (induction on `k`): with `α = g'⁴`, `A = N'²`, `β = g²`, `B = N`,
  `|a A B (α^k B^k − β^k A^k)| ≤ k A^k B^k · 2b³ N' N`, from
  `α^{k+1} B^{k+1} − β^{k+1} A^{k+1} = α B (α^k B^k − β^k A^k) + β^k A^k (α B − β A)`;
* `rot_doubling`: the same with `α^k = g'^{4k}` written as the rotation power of exponent `k + k` (`cpow_sq`):
  dividing by `a A^{k+1} B^{k+1}`, `|g'^{4k}/N'^{2k} − g^{2k}/N^k| ≤ 2k b³/(a N') ≤ k b³/(2a³)`;
* `cayley_doubling`: for the names at `u = p/q` (`a = 2jq`, `b = p`, `k = j`), with `C_m = cosNum q p m`,
  `S_m = sinNum q p m`, `D_j = trigDen q p j = B^j` and `A^j` the denominator `N'^{2j}` of the stage `2j`:
  `|a A B ((C_{2j} + i S_{2j}) D_j − (C_j + i S_j) A^j)| ≤ j A^j B^j · 2p³ N' N`, i.e.
  `|z_{2j}(u) − z_j(u)| ≤ u³/(16 j²)`.

The dyadic stages `j = 2^m j₀` therefore form a Cauchy sequence with a geometric rate
(`∑_m u³/(16 · 4^m j₀²)`); the summation of the rate and the identification of the limit with the Taylor names
are not derived here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.RotationDoubling

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.ComplexPowers
open LeanProofs.IPRA.Analysis.Rotation
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Congruence of the powers -/

theorem cU_congr {p₁ p₂ q₁ q₂ j p₁' p₂' q₁' q₂' j' : PTm n} (h₁ : Γ ⊢[PRAAx] p₁ ≐ p₁')
    (h₂ : Γ ⊢[PRAAx] p₂ ≐ p₂') (h₃ : Γ ⊢[PRAAx] q₁ ≐ q₁') (h₄ : Γ ⊢[PRAAx] q₂ ≐ q₂')
    (h₅ : Γ ⊢[PRAAx] j ≐ j') : Γ ⊢[PRAAx] cU p₁ p₂ q₁ q₂ j ≐ cU p₁' p₂' q₁' q₂' j' := by
  have h : Γ ⊢[PRAAx] Syn.subst ![p₁, p₂, q₁, q₂, j] (cU (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ≐
      Syn.subst ![p₁', p₂', q₁', q₂', j'] (cU (var 0) (var 1) (var 2) (var 3) (var 4)) :=
    Prf.eqCongr _ fun i => by fin_cases i <;> assumption
  simp only [subst_cU, Syn.subst_var] at h
  exact h

theorem cV_congr {p₁ p₂ q₁ q₂ j p₁' p₂' q₁' q₂' j' : PTm n} (h₁ : Γ ⊢[PRAAx] p₁ ≐ p₁')
    (h₂ : Γ ⊢[PRAAx] p₂ ≐ p₂') (h₃ : Γ ⊢[PRAAx] q₁ ≐ q₁') (h₄ : Γ ⊢[PRAAx] q₂ ≐ q₂')
    (h₅ : Γ ⊢[PRAAx] j ≐ j') : Γ ⊢[PRAAx] cV p₁ p₂ q₁ q₂ j ≐ cV p₁' p₂' q₁' q₂' j' := by
  have h : Γ ⊢[PRAAx] Syn.subst ![p₁, p₂, q₁, q₂, j] (cV (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ≐
      Syn.subst ![p₁', p₂', q₁', q₂', j'] (cV (var 0) (var 1) (var 2) (var 3) (var 4)) :=
    Prf.eqCongr _ fun i => by fin_cases i <;> assumption
  simp only [subst_cV, Syn.subst_var] at h
  exact h

/-- The value of a coded pair. -/
theorem pair_val {u v : PTm n} (h : Γ ⊢[PRAAx] u ≐ v) :
    (𝔟 (fstT u) - 𝔟 (sndT u) : Groth (Q Γ)) = 𝔟 (fstT v) - 𝔟 (sndT v) := by
  rw [natEq (congrFst h), natEq (congrSnd h)]

theorem cRe_congr {re im : ZT n} {j j' : PTm n} (h : Γ ⊢[PRAAx] j ≐ j') :
    ZT.toZ Γ (cRe re im j) = ZT.toZ Γ (cRe re im j') :=
  pair_val (cU_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) h)

theorem cIm_congr {re im : ZT n} {j j' : PTm n} (h : Γ ⊢[PRAAx] j ≐ j') :
    ZT.toZ Γ (cIm re im j) = ZT.toZ Γ (cIm re im j') :=
  pair_val (cV_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) h)

theorem rotRe_congr {a a' b k k' : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a') (hk : Γ ⊢[PRAAx] k ≐ k') :
    ZT.toZ Γ (rotRe a b k) = ZT.toZ Γ (rotRe a' b k') :=
  pair_val (cU_congr (p₁ := a * a) (p₂ := b * b) (q₁ := a * b + a * b) (q₂ := zero) (congrMul ha ha)
    (.eqRefl _) (congrAdd (congrMul ha (.eqRefl b)) (congrMul ha (.eqRefl b))) (.eqRefl _) hk)

theorem rotIm_congr {a a' b k k' : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a') (hk : Γ ⊢[PRAAx] k ≐ k') :
    ZT.toZ Γ (rotIm a b k) = ZT.toZ Γ (rotIm a' b k') :=
  pair_val (cV_congr (p₁ := a * a) (p₂ := b * b) (q₁ := a * b + a * b) (q₂ := zero) (congrMul ha ha)
    (.eqRefl _) (congrAdd (congrMul ha (.eqRefl b)) (congrMul ha (.eqRefl b))) (.eqRefl _) hk)

/-! ## The power law `(z²)^k = z^{2k}` -/

/-- `Re z²`, `Im z²`. -/
abbrev sqRe (re im : ZT n) : ZT n := re * re - im * im
abbrev sqIm (re im : ZT n) : ZT n := re * im + im * re

/-- `(z²)^k = z^{k+k}`. -/
abbrev SqP (re im : ZT n) (k : PTm n) : Fm PTm n :=
  ZT.eq (cRe (sqRe re im) (sqIm re im) k) (cRe re im (k + k)) ⋏
    ZT.eq (cIm (sqRe re im) (sqIm re im) k) (cIm re im (k + k))

theorem sq_zero (re im : ZT n) : Γ ⊢[PRAAx] SqP re im zero := by
  have c : Γ ⊢[PRAAx] (zero : PTm n) + zero ≐ zero := zero_add zero
  refine .andI (ZT.derive ?_) (ZT.derive ?_)
  · rw [cRe_congr c, cRe_zero, cRe_zero]
  · rw [cIm_congr c, cIm_zero, cIm_zero]

theorem sq_succ {re im : ZT n} {k : PTm n} (ih : Γ ⊢[PRAAx] SqP re im k) :
    Γ ⊢[PRAAx] SqP re im (succ k) := by
  have i₁ := ZT.toZ_eq (Prf.andE₁ ih)
  have i₂ := ZT.toZ_eq (Prf.andE₂ ih)
  have c : Γ ⊢[PRAAx] succ k + succ k ≐ succ (succ (k + k)) :=
    deriveNat (by simp only [Q.mk_add, Q.mk_succ, map_add, map_one]; ring)
  have a₁ := cRe_congr (re := re) (im := im) c
  have a₂ := cIm_congr (re := re) (im := im) c
  have s₁ := cRe_succ (Γ := Γ) re im (succ (k + k))
  have s₂ := cIm_succ (Γ := Γ) re im (succ (k + k))
  have t₁ := cRe_succ (Γ := Γ) re im (k + k)
  have t₂ := cIm_succ (Γ := Γ) re im (k + k)
  have u₁ := cRe_succ (Γ := Γ) (sqRe re im) (sqIm re im) k
  have u₂ := cIm_succ (Γ := Γ) (sqRe re im) (sqIm re im) k
  have er : ZT.toZ Γ (sqRe re im) = ZT.toZ Γ re * ZT.toZ Γ re - ZT.toZ Γ im * ZT.toZ Γ im := by
    simp only [sqRe, ZT.toZ_sub, ZT.toZ_mul]
  have ei : ZT.toZ Γ (sqIm re im) = ZT.toZ Γ re * ZT.toZ Γ im + ZT.toZ Γ im * ZT.toZ Γ re := by
    simp only [sqIm, ZT.toZ_add, ZT.toZ_mul]
  rw [er, ei] at u₁ u₂
  refine .andI (ZT.derive ?_) (ZT.derive ?_)
  · linear_combination u₁ - a₁ - s₁ - ZT.toZ Γ re * t₁ + ZT.toZ Γ im * t₂ +
      (ZT.toZ Γ re * ZT.toZ Γ re - ZT.toZ Γ im * ZT.toZ Γ im) * i₁ -
      (ZT.toZ Γ re * ZT.toZ Γ im + ZT.toZ Γ im * ZT.toZ Γ re) * i₂
  · linear_combination u₂ - a₂ - s₂ - ZT.toZ Γ im * t₁ - ZT.toZ Γ re * t₂ +
      (ZT.toZ Γ re * ZT.toZ Γ im + ZT.toZ Γ im * ZT.toZ Γ re) * i₁ +
      (ZT.toZ Γ re * ZT.toZ Γ re - ZT.toZ Γ im * ZT.toZ Γ im) * i₂

/-- Variables: `0 = k` (induction), `1, 2 = re⁺, re⁻`, `3, 4 = im⁺, im⁻`. -/
private theorem sq₀ :
    ([] : List (Fm PTm 5)) ⊢[PRAAx] SqP (⟨var 1, var 2⟩ : ZT 5) (⟨var 3, var 4⟩ : ZT 5) (var 0) := by
  ipra_ind (⟨trivial, trivial⟩) [SqP, sqRe, sqIm, ZT.subst_eq, subst_cRe, subst_cIm, ZT.subst_sub, ZT.subst_mul, ZT.subst_add, subst_mk]
  · exact sq_zero _ _
  · exact sq_succ Prf.hyp0

/-- The power law: `(z²)^k = z^{k+k}`. -/
theorem cpow_sq (re im : ZT n) (k : PTm n) : Γ ⊢[PRAAx] SqP re im k := by
  have h := inst (Γ := Γ) sq₀ (![k, re.pos, re.neg, im.pos, im.neg] : Fin 5 → PTm n)
  simp only [SqP, sqRe, sqIm, Fm.subst_and, ZT.subst_eq, subst_cRe, subst_cIm, ZT.subst_sub, ZT.subst_mul,
    ZT.subst_add, subst_mk, PTm.subst_add, Syn.subst_var] at h
  exact h

/-! ## The data of the two stages -/

/-- `α = g'⁴`, `g' = 2a + i b`. -/
def aRe (a b : PTm n) : ZT n := sqRe (rRe (a + a) b) (rIm (a + a) b)
def aIm (a b : PTm n) : ZT n := sqIm (rRe (a + a) b) (rIm (a + a) b)

/-- `A = |g'⁴| = N'²`. -/
def dA (a b : PTm n) : PTm n := nrm (a + a) b * nrm (a + a) b

/-- `a (α N − g² A) = 2i b³ g'² (a g)`. -/
def dEx (a b : PTm n) : ZT n :=
  -(ZT.ofNat (b * b * b + b * b * b) *
    (rRe (a + a) b * ZT.ofNat (a * b) + rIm (a + a) b * ZT.ofNat (a * a)))
def dEy (a b : PTm n) : ZT n :=
  ZT.ofNat (b * b * b + b * b * b) * (rRe (a + a) b * ZT.ofNat (a * a) - rIm (a + a) b * ZT.ofNat (a * b))

/-- The bound `2b³ N' N`. -/
def dDel (a b : PTm n) : PTm n := (b * b * b + b * b * b) * (nrm (a + a) b * nrm a b)

@[simp] theorem subst_aRe {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    (aRe a b).subst σ = aRe (Syn.subst σ a) (Syn.subst σ b) := by
  simp only [aRe, sqRe, ZT.subst_sub, ZT.subst_mul, subst_rRe, subst_rIm, PTm.subst_add]

@[simp] theorem subst_aIm {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    (aIm a b).subst σ = aIm (Syn.subst σ a) (Syn.subst σ b) := by
  simp only [aIm, sqIm, ZT.subst_add, ZT.subst_mul, subst_rRe, subst_rIm, PTm.subst_add]

@[simp] theorem subst_dA {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (dA a b) = dA (Syn.subst σ a) (Syn.subst σ b) := by
  simp only [dA, PTm.subst_mul, subst_nrm, PTm.subst_add]

@[simp] theorem subst_dDel {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (dDel a b) = dDel (Syn.subst σ a) (Syn.subst σ b) := by
  simp only [dDel, PTm.subst_mul, subst_nrm, PTm.subst_add]

/-- `|g'⁴| ≤ N'²`. -/
theorem alpha_nle (a b : PTm n) : Γ ⊢[PRAAx] nle (aRe a b) (aIm a b) (dA a b) :=
  nle_mul (g_nle (a + a) b) (g_nle (a + a) b)

/-- `|a (g'⁴ N − g² N'²)| ≤ 2b³ N' N`. -/
theorem del_nle (a b : PTm n) : Γ ⊢[PRAAx] nle (dEx a b) (dEy a b) (dDel a b) := by
  have h₀ := nle_scale (b * b * b + b * b * b) (nle_mul (g_nle (Γ := Γ) (a + a) b) (ag_nle a b))
  refine nle_of_comb (zsl h₀) ?_ (nn_zsl _)
  rw [nle_sl h₀]
  simp only [dEx, dEy, dDel, ZT.toZ_neg]
  ring

/-- Expansion of the values to the atoms `a`, `b`. -/
local macro "dexpand" : tactic =>
  `(tactic| simp only [dEx, dEy, aRe, aIm, sqRe, sqIm, dA, toZ_rRe, toZ_rIm, nrm_val, ZT.toZ_mul, ZT.toZ_sub,
    ZT.toZ_neg, ZT.toZ_add, ZT.toZ_ofNat, Q.mk_add, Q.mk_mul, map_add, map_mul])

/-- `a (α N − g² A)`, real part. -/
theorem dEx_val (a b : PTm n) :
    ZT.toZ Γ (dEx a b) =
      𝔟 a * (ZT.toZ Γ (aRe a b) * 𝔟 (nrm a b) - ZT.toZ Γ (rRe a b) * 𝔟 (dA a b)) := by
  dexpand
  ring

/-- `a (α N − g² A)`, imaginary part. -/
theorem dEy_val (a b : PTm n) :
    ZT.toZ Γ (dEy a b) =
      𝔟 a * (ZT.toZ Γ (aIm a b) * 𝔟 (nrm a b) - ZT.toZ Γ (rIm a b) * 𝔟 (dA a b)) := by
  dexpand
  ring

/-! ## The telescoping estimate -/

/-- `Z_k = a A B (α^k B^k − β^k A^k)`. -/
abbrev Zx (a b k : PTm n) : ZT n :=
  ZT.ofNat (a * (dA a b * nrm a b)) *
    (cRe (aRe a b) (aIm a b) k * ZT.ofNat (pw (nrm a b) k) - rotRe a b k * ZT.ofNat (pw (dA a b) k))
abbrev Zy (a b k : PTm n) : ZT n :=
  ZT.ofNat (a * (dA a b * nrm a b)) *
    (cIm (aRe a b) (aIm a b) k * ZT.ofNat (pw (nrm a b) k) - rotIm a b k * ZT.ofNat (pw (dA a b) k))

/-- The bound `k A^k B^k · 2b³ N' N`. -/
abbrev Td (a b k : PTm n) : PTm n := k * (pw (dA a b) k * pw (nrm a b) k) * dDel a b

/-- Expansion with `A`, `B`, the bases and the powers as atoms. -/
local macro "zexpand" : tactic =>
  `(tactic| simp only [Zx, Zy, Td, ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_add, ZT.toZ_ofNat, Q.mk_add, Q.mk_mul,
    Q.mk_succ, Q.mk_zero, map_add, map_mul, map_one, map_zero])

theorem pwA_step (a b k : PTm n) :
    (𝔟 (pw (dA a b) (succ k)) : Groth (Q Γ)) = 𝔟 (pw (dA a b) k) * 𝔟 (dA a b) := by
  have e := natEq (pw_succ (Γ := Γ) (dA a b) k)
  simp only [Q.mk_mul, map_mul] at e
  exact e

theorem pwB_step (a b k : PTm n) :
    (𝔟 (pw (nrm a b) (succ k)) : Groth (Q Γ)) = 𝔟 (pw (nrm a b) k) * 𝔟 (nrm a b) := by
  have e := natEq (pw_succ (Γ := Γ) (nrm a b) k)
  simp only [Q.mk_mul, map_mul] at e
  exact e

theorem pw_one_val (c : PTm n) : (𝔟 (pw c zero) : Groth (Q Γ)) = 1 := by
  have e := natEq (pw_zero (Γ := Γ) c)
  simp only [Q.mk_one, map_one] at e
  exact e

theorem d_zero (a b : PTm n) : Γ ⊢[PRAAx] nle (Zx a b zero) (Zy a b zero) (Td a b zero) := by
  refine nle_of_comb 0 ?_ nn_zero
  zexpand
  rw [cRe_zero, cIm_zero, rot_re_zero, rot_im_zero, pw_one_val, pw_one_val]
  ring

theorem d_succ {a b k : PTm n} (ih : Γ ⊢[PRAAx] nle (Zx a b k) (Zy a b k) (Td a b k)) :
    Γ ⊢[PRAAx] nle (Zx a b (succ k)) (Zy a b (succ k)) (Td a b (succ k)) := by
  have hβ : Γ ⊢[PRAAx] nle (rotRe a b k) (rotIm a b k) (pw (nrm a b) k) := nle_of_eq (un_val (rot_unit a b k))
  have ra := cRe_succ (Γ := Γ) (aRe a b) (aIm a b) k
  have ra' := cIm_succ (Γ := Γ) (aRe a b) (aIm a b) k
  have rb : ZT.toZ Γ (rotRe a b (succ k)) =
      ZT.toZ Γ (rRe a b) * ZT.toZ Γ (rotRe a b k) - ZT.toZ Γ (rIm a b) * ZT.toZ Γ (rotIm a b k) :=
    cRe_succ _ _ _
  have rb' : ZT.toZ Γ (rotIm a b (succ k)) =
      ZT.toZ Γ (rIm a b) * ZT.toZ Γ (rotRe a b k) + ZT.toZ Γ (rRe a b) * ZT.toZ Γ (rotIm a b k) :=
    cIm_succ _ _ _
  have eA := pwA_step (Γ := Γ) a b k
  have eB := pwB_step (Γ := Γ) a b k
  have hx := dEx_val (Γ := Γ) a b
  have hy := dEy_val (Γ := Γ) a b
  refine nle_of (nle_add (nle_mul (nle_scale (nrm a b) (alpha_nle a b)) ih)
    (nle_scale (pw (dA a b) k * (dA a b * nrm a b)) (nle_mul hβ (del_nle a b)))) ?_ ?_ ?_
  · zexpand
    linear_combination
      𝔟 a * 𝔟 (dA a b) * 𝔟 (nrm a b) *
          (𝔟 (pw (nrm a b) (succ k)) * ra +
            (ZT.toZ Γ (aRe a b) * ZT.toZ Γ (cRe (aRe a b) (aIm a b) k) -
              ZT.toZ Γ (aIm a b) * ZT.toZ Γ (cIm (aRe a b) (aIm a b) k)) * eB -
            𝔟 (pw (dA a b) (succ k)) * rb -
            (ZT.toZ Γ (rRe a b) * ZT.toZ Γ (rotRe a b k) - ZT.toZ Γ (rIm a b) * ZT.toZ Γ (rotIm a b k)) * eA) -
        𝔟 (pw (dA a b) k) * 𝔟 (dA a b) * 𝔟 (nrm a b) * ZT.toZ Γ (rotRe a b k) * hx +
        𝔟 (pw (dA a b) k) * 𝔟 (dA a b) * 𝔟 (nrm a b) * ZT.toZ Γ (rotIm a b k) * hy
  · zexpand
    linear_combination
      𝔟 a * 𝔟 (dA a b) * 𝔟 (nrm a b) *
          (𝔟 (pw (nrm a b) (succ k)) * ra' +
            (ZT.toZ Γ (aIm a b) * ZT.toZ Γ (cRe (aRe a b) (aIm a b) k) +
              ZT.toZ Γ (aRe a b) * ZT.toZ Γ (cIm (aRe a b) (aIm a b) k)) * eB -
            𝔟 (pw (dA a b) (succ k)) * rb' -
            (ZT.toZ Γ (rIm a b) * ZT.toZ Γ (rotRe a b k) + ZT.toZ Γ (rRe a b) * ZT.toZ Γ (rotIm a b k)) * eA) -
        𝔟 (pw (dA a b) k) * 𝔟 (dA a b) * 𝔟 (nrm a b) * ZT.toZ Γ (rotRe a b k) * hy -
        𝔟 (pw (dA a b) k) * 𝔟 (dA a b) * 𝔟 (nrm a b) * ZT.toZ Γ (rotIm a b k) * hx
  · refine le_of_comb 0 ?_ nn_zero
    zexpand
    linear_combination 𝔟 (dDel a b) * (𝔟 k + 1) * 𝔟 (pw (nrm a b) (succ k)) * eA +
      𝔟 (dDel a b) * (𝔟 k + 1) * 𝔟 (pw (dA a b) k) * 𝔟 (dA a b) * eB

/-- Variables: `0 = k` (induction), `1 = a`, `2 = b`. -/
private theorem d₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx]
    nle (Zx (var 1) (var 2) (var 0)) (Zy (var 1) (var 2) (var 0)) (Td (var 1) (var 2) (var 0)) := by
  ipra_ind [Zx, Zy, Td, subst_zle, ZT.subst_add, ZT.subst_sub, ZT.subst_mul, ZT.subst_sq, ZT.subst_ofNat, subst_cRe, subst_cIm, subst_aRe, subst_aIm, subst_rotRe, subst_rotIm, subst_nrm, subst_dA, subst_dDel, subst_ap2]
  · exact d_zero _ _
  · exact d_succ Prf.hyp0

/-- `|a A B (α^k B^k − β^k A^k)| ≤ k A^k B^k · 2b³ N' N` for `α = g'⁴`, `β = g²`. -/
theorem doubling (a b k : PTm n) : Γ ⊢[PRAAx] nle (Zx a b k) (Zy a b k) (Td a b k) := by
  have h := inst (Γ := Γ) d₀ (![k, a, b] : Fin 3 → PTm n)
  simpa using h

/-- The stage `2a`, exponent `k + k`, against the stage `a`, exponent `k`:
`|a A B (g'^{4k} N^k − g^{2k} N'^{2k})| ≤ k A^k B^k · 2b³ N' N`, i.e.
`|g'^{4k}/N'^{2k} − g^{2k}/N^k| ≤ 2k b³/(a N') ≤ k b³/(2a³)`. -/
theorem rot_doubling (a b k : PTm n) :
    Γ ⊢[PRAAx] nle
      (ZT.ofNat (a * (dA a b * nrm a b)) *
        (rotRe (a + a) b (k + k) * ZT.ofNat (pw (nrm a b) k) - rotRe a b k * ZT.ofNat (pw (dA a b) k)))
      (ZT.ofNat (a * (dA a b * nrm a b)) *
        (rotIm (a + a) b (k + k) * ZT.ofNat (pw (nrm a b) k) - rotIm a b k * ZT.ofNat (pw (dA a b) k)))
      (Td a b k) := by
  have p := cpow_sq (Γ := Γ) (rRe (a + a) b) (rIm (a + a) b) k
  have p₁ : ZT.toZ Γ (cRe (aRe a b) (aIm a b) k) = ZT.toZ Γ (rotRe (a + a) b (k + k)) :=
    ZT.toZ_eq (Prf.andE₁ p)
  have p₂ : ZT.toZ Γ (cIm (aRe a b) (aIm a b) k) = ZT.toZ Γ (rotIm (a + a) b (k + k)) :=
    ZT.toZ_eq (Prf.andE₂ p)
  refine nle_of (doubling a b k) ?_ ?_ (le_refl _)
  · simp only [Zx, ZT.toZ_mul, ZT.toZ_sub]
    rw [p₁]
  · simp only [Zy, ZT.toZ_mul, ZT.toZ_sub]
    rw [p₂]

/-- The Cauchy step of the names of `cos (p/q)`, `sin (p/q)`: with `a = 2jq`, `B = N = a² + p²`, `A = N'²`,
`N' = (2a)² + p²`, `|a A B ((C_{2j} + i S_{2j}) B^j − (C_j + i S_j) A^j)| ≤ j A^j B^j · 2p³ N' N`, i.e.
`|z_{2j}(u) − z_j(u)| ≤ u³/(16 j²)` for `u = p/q`. -/
theorem cayley_doubling (q p j : PTm n) :
    Γ ⊢[PRAAx] nle
      (ZT.ofNat ((j + j) * q * (dA ((j + j) * q) p * nrm ((j + j) * q) p)) *
        (cosNum q p (j + j) * ZT.ofNat (trigDen q p j) -
          cosNum q p j * ZT.ofNat (pw (dA ((j + j) * q) p) j)))
      (ZT.ofNat ((j + j) * q * (dA ((j + j) * q) p * nrm ((j + j) * q) p)) *
        (sinNum q p (j + j) * ZT.ofNat (trigDen q p j) -
          sinNum q p j * ZT.ofNat (pw (dA ((j + j) * q) p) j)))
      (Td ((j + j) * q) p j) := by
  have ha : Γ ⊢[PRAAx] (j + j + (j + j)) * q ≐ (j + j) * q + (j + j) * q :=
    deriveNat (by simp only [Q.mk_add, Q.mk_mul, map_add, map_mul]; ring)
  have c₁ := rotRe_congr (b := p) ha (.eqRefl (j + j))
  have c₂ := rotIm_congr (b := p) ha (.eqRefl (j + j))
  refine nle_of (rot_doubling ((j + j) * q) p j) ?_ ?_ (le_refl _)
  · simp only [cosNum, trigDen, ZT.toZ_mul, ZT.toZ_sub]
    rw [c₁]
  · simp only [sinNum, trigDen, ZT.toZ_mul, ZT.toZ_sub]
    rw [c₂]

end LeanProofs.IPRA.Analysis.RotationDoubling
