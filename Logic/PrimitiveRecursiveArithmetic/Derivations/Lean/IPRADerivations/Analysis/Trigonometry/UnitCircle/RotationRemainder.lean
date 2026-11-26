import IPRADerivations.Analysis.Trigonometry.UnitCircle.ComplexPowers

/-!
# Cosine and sine names on the unit circle, and their exact first-order remainder

Packet: `probability/expected_value_ipra_2026-11-16`, `paper/sections/13_fourier_applications.tex`, the names of
`φ_X(t) = E[cos(tX)] + i E[sin(tX)]` and the estimate `|e^{iu} − 1 − iu| ≤ u²/2` in the proof of Theorem
`thm:char-derivative` ("at rational precision it is a finite polynomial inequality").

The names used here are the Cayley (midpoint) approximants of `e^{iu}`, `u = p/q ≥ 0`:

  `z_n(u) = ((2n + iu)/(2n − iu))^n = g^{2n}/N^n`,  `g = a + i b`, `a = 2nq`, `b = p`, `N = a² + b²`,

so `cos_n u = Re g^{2n}/N^n` and `sin_n u = Im g^{2n}/N^n`, with `g^{2k}` the complex-integer powers of
`Analysis/Trigonometry/UnitCircle/ComplexPowers` (base `g² = (a² − b²) + i 2ab`, exponent a term). Every
approximant is a rational point of the unit circle, which the Taylor partial sums are not, and this makes the
first-order remainder exact at every stage: no tail term is needed.

For natural terms `a`, `b`, `k` (`rotRe a b k + i rotIm a b k = g^{2k}`, `nrm a b = N`):

* `rot_unit`: `(Re g^{2k})² + (Im g^{2k})² = (N^k)²`: the unit modulus `cos_n² + sin_n² = 1`, cleared;
* `e_bound`: `|a (g^{2k} − N^k)| ≤ 2k b N^k`, i.e. `|w^k − 1| ≤ k |w − 1|` for `w = g²/N` (`|w − 1| ≤ 2b/a`);
* `f_bound`: `|a² (g^{2k+2} − N^{k+1} − (k+1) N^k (g² − N))| ≤ 2b² k(k+1) N^{k+1}`, the second difference
  `|w^n − 1 − n(w − 1)| ≤ (n(n−1)/2) |w − 1|²`: the discrete form of the integral remainder;
* `rotation_remainder`: `|a² (g^{2n} − N^n) − i 2n a b N^n| ≤ 2 n² b² N^n` for `n = k + 1`, i.e.
  `|w^n − 1 − i u| ≤ u²/2` with `u = 2n b/a`; the three statements above are one induction on `k` (`inv`);
* `cayley_remainder` (the estimate of `thm:char-derivative` for the names): for `u = p/q` and the stage
  `n = k + 1`, with `C = cosNum`, `S = sinNum`, `D = trigDen`,
  `|2q² (C − D) + i 2q (q S − p D)| ≤ p² D`, i.e. `|cos_n u − 1 + i (sin_n u − u)| ≤ u²/2`;
* `cayley_unit`: `C² + S² = D²`; `cos_le_one`: `C ≤ D`; `one_sub_cos_le`: `2q² (D − C) ≤ p² D`, i.e.
  `1 − cos_n u ≤ u²/2`; `sin_sub_le`, `sub_sin_le`: `|sin_n u − u| ≤ u²/2`, cleared by `2q D`.

The moduli are bounded without square roots (`nle`), the bounds are natural terms, and the exponent and the
stage are terms, so the statements hold with the stage a variable. The convergence rate of the names and their
identification with the Taylor names of the packet are not derived here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.Rotation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.ComplexPowers
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The base `g² = (a² − b²) + i 2ab` and its powers -/

/-- `Re g² = a² − b²`. -/
def rRe (a b : PTm n) : ZT n := ⟨a * a, b * b⟩

/-- `Im g² = 2ab`. -/
def rIm (a b : PTm n) : ZT n := ZT.ofNat (a * b + a * b)

/-- `N = |g|² = a² + b²`. -/
def nrm (a b : PTm n) : PTm n := a * a + b * b

/-- `Re g^{2k}`. -/
def rotRe (a b k : PTm n) : ZT n := cRe (rRe a b) (rIm a b) k

/-- `Im g^{2k}`. -/
def rotIm (a b k : PTm n) : ZT n := cIm (rRe a b) (rIm a b) k

theorem toZ_rRe (a b : PTm n) : ZT.toZ Γ (rRe a b) = 𝔟 a * 𝔟 a - 𝔟 b * 𝔟 b := by
  show (𝔟 (a * a) - 𝔟 (b * b) : Groth (Q Γ)) = _
  simp only [Q.mk_mul, map_mul]

theorem toZ_rIm (a b : PTm n) : ZT.toZ Γ (rIm a b) = 𝔟 a * 𝔟 b + 𝔟 a * 𝔟 b := by
  simp only [rIm, ZT.toZ_ofNat, Q.mk_add, Q.mk_mul, map_add, map_mul]

theorem nrm_val (a b : PTm n) : (𝔟 (nrm a b) : Groth (Q Γ)) = 𝔟 a * 𝔟 a + 𝔟 b * 𝔟 b := by
  simp only [nrm, Q.mk_add, Q.mk_mul, map_add, map_mul]

@[simp] theorem subst_nrm {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (nrm a b) = nrm (Syn.subst σ a) (Syn.subst σ b) := by
  simp only [nrm, PTm.subst_add, PTm.subst_mul]

@[simp] theorem subst_rRe {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    (rRe a b).subst σ = rRe (Syn.subst σ a) (Syn.subst σ b) := by
  show (⟨Syn.subst σ (a * a), Syn.subst σ (b * b)⟩ : ZT m) = _
  simp only [PTm.subst_mul]
  rfl

@[simp] theorem subst_rIm {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    (rIm a b).subst σ = rIm (Syn.subst σ a) (Syn.subst σ b) := by
  simp only [rIm, ZT.subst_ofNat, PTm.subst_add, PTm.subst_mul]

@[simp] theorem subst_rotRe {m : ℕ} (σ : Fin n → PTm m) (a b k : PTm n) :
    (rotRe a b k).subst σ = rotRe (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ k) := by
  simp only [rotRe, subst_cRe, subst_rRe, subst_rIm]

@[simp] theorem subst_rotIm {m : ℕ} (σ : Fin n → PTm m) (a b k : PTm n) :
    (rotIm a b k).subst σ = rotIm (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ k) := by
  simp only [rotIm, subst_cIm, subst_rRe, subst_rIm]

theorem rot_re_zero (a b : PTm n) : ZT.toZ Γ (rotRe a b zero) = 1 := cRe_zero _ _

theorem rot_im_zero (a b : PTm n) : ZT.toZ Γ (rotIm a b zero) = 0 := cIm_zero _ _

theorem rot_re_succ (a b k : PTm n) :
    ZT.toZ Γ (rotRe a b (succ k)) =
      (𝔟 a * 𝔟 a - 𝔟 b * 𝔟 b) * ZT.toZ Γ (rotRe a b k) - (𝔟 a * 𝔟 b + 𝔟 a * 𝔟 b) * ZT.toZ Γ (rotIm a b k) := by
  have h := cRe_succ (Γ := Γ) (rRe a b) (rIm a b) k
  rw [toZ_rRe, toZ_rIm] at h
  exact h

theorem rot_im_succ (a b k : PTm n) :
    ZT.toZ Γ (rotIm a b (succ k)) =
      (𝔟 a * 𝔟 b + 𝔟 a * 𝔟 b) * ZT.toZ Γ (rotRe a b k) + (𝔟 a * 𝔟 a - 𝔟 b * 𝔟 b) * ZT.toZ Γ (rotIm a b k) := by
  have h := cIm_succ (Γ := Γ) (rRe a b) (rIm a b) k
  rw [toZ_rRe, toZ_rIm] at h
  exact h

/-! ## The differences `a (g^{2k} − N^k)` and the second differences -/

/-- `c = a (g² − N) = −2ab² + i 2a²b`. -/
abbrev cx (a b : PTm n) : ZT n := -ZT.ofNat (a * (b * b) + a * (b * b))
abbrev cy (a b : PTm n) : ZT n := ZT.ofNat (a * a * b + a * a * b)

/-- The bound `2bN` of `|c|`. -/
abbrev cB (a b : PTm n) : PTm n := (b + b) * nrm a b

/-- `E_k = a (g^{2k} − N^k)`. -/
abbrev Ex (a b k : PTm n) : ZT n := ZT.ofNat a * (rotRe a b k - ZT.ofNat (pw (nrm a b) k))
abbrev Ey (a b k : PTm n) : ZT n := ZT.ofNat a * rotIm a b k

/-- The bound `2k b N^k` of `|E_k|`. -/
abbrev Bd (a b k : PTm n) : PTm n := (k + k) * b * pw (nrm a b) k

/-- `F_k = a E_{k+1} − (k + 1) N^k a c`. -/
abbrev Fx (a b k : PTm n) : ZT n :=
  ZT.ofNat a * Ex a b (succ k) - ZT.ofNat (succ k * pw (nrm a b) k * a) * cx a b
abbrev Fy (a b k : PTm n) : ZT n :=
  ZT.ofNat a * Ey a b (succ k) - ZT.ofNat (succ k * pw (nrm a b) k * a) * cy a b

/-- The bound `2b² k(k+1) N^{k+1}` of `|F_k|`. -/
abbrev Cd (a b k : PTm n) : PTm n := (b * b + b * b) * (k * succ k) * pw (nrm a b) (succ k)

/-- Expansion of the values of the terms of this module. -/
local macro "rsimp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [cx, cy, cB, Ex, Ey, Bd, Fx, Fy, Cd, toZ_rRe, toZ_rIm, nrm_val, ZT.toZ_mul, ZT.toZ_sub,
    ZT.toZ_neg, ZT.toZ_add, ZT.toZ_ofNat, Q.mk_add, Q.mk_mul, Q.mk_succ, Q.mk_zero, Q.mk_one, map_add, map_mul,
    map_one, map_zero] $[$loc]?)

/-- `|g²|² = N²`. -/
theorem base_norm (a b : PTm n) :
    ZT.toZ Γ (rRe a b) ^ 2 + ZT.toZ Γ (rIm a b) ^ 2 = 𝔟 (nrm a b) * 𝔟 (nrm a b) := by
  rsimp
  ring

/-- `|g²| ≤ N`. -/
theorem g_nle (a b : PTm n) : Γ ⊢[PRAAx] nle (rRe a b) (rIm a b) (nrm a b) :=
  nle_of_eq (base_norm a b)

/-- `N^{k+1} = N^k N`. -/
theorem pw_step (a b k : PTm n) :
    (𝔟 (pw (nrm a b) (succ k)) : Groth (Q Γ)) = 𝔟 (pw (nrm a b) k) * (𝔟 a * 𝔟 a + 𝔟 b * 𝔟 b) := by
  have e := natEq (pw_succ (Γ := Γ) (nrm a b) k)
  simp only [Q.mk_mul, map_mul, nrm_val] at e
  exact e

theorem pw_base (a b : PTm n) : (𝔟 (pw (nrm a b) zero) : Groth (Q Γ)) = 1 := by
  have e := natEq (pw_zero (Γ := Γ) (nrm a b))
  simp only [Q.mk_one, map_one] at e
  exact e

/-- `|c| ≤ 2bN`: `(2bN)² − |c|² = 4b⁴N`. -/
theorem c_nle (a b : PTm n) : Γ ⊢[PRAAx] nle (cx a b) (cy a b) (cB a b) := by
  refine nle_of_comb ((𝔟 b * 𝔟 b + 𝔟 b * 𝔟 b) * (𝔟 b * 𝔟 b + 𝔟 b * 𝔟 b) * (𝔟 a * 𝔟 a + 𝔟 b * 𝔟 b)) ?_ (by znn)
  rsimp
  ring

/-- `|a g| ≤ N`: `N² − a²N = b²N`. -/
theorem ag_nle (a b : PTm n) : Γ ⊢[PRAAx] nle (ZT.ofNat (a * a)) (ZT.ofNat (a * b)) (nrm a b) := by
  refine nle_of_comb ((𝔟 a * 𝔟 a + 𝔟 b * 𝔟 b) * (𝔟 b * 𝔟 b)) ?_ (by znn)
  rsimp
  ring

/-- The unit modulus at the exponent `k`. -/
abbrev Un (a b k : PTm n) : Fm PTm n :=
  ZT.eq (ZT.sq (rotRe a b k) + ZT.sq (rotIm a b k)) (ZT.ofNat (pw (nrm a b) k * pw (nrm a b) k))

/-- The invariant: unit modulus, `|E_k| ≤ 2k b N^k` and `|F_k| ≤ 2b² k(k+1) N^{k+1}`. -/
abbrev Inv (a b k : PTm n) : Fm PTm n :=
  (Un a b k ⋏ nle (Ex a b k) (Ey a b k) (Bd a b k)) ⋏ nle (Fx a b k) (Fy a b k) (Cd a b k)

theorem un_val {a b k : PTm n} (h : Γ ⊢[PRAAx] Un a b k) :
    ZT.toZ Γ (rotRe a b k) ^ 2 + ZT.toZ Γ (rotIm a b k) ^ 2 =
      𝔟 (pw (nrm a b) k) * 𝔟 (pw (nrm a b) k) := by
  have e := ZT.toZ_eq h
  simp only [ZT.toZ_add, ZT.toZ_sq, ZT.toZ_ofNat, Q.mk_mul, map_mul] at e
  exact e

theorem un_of {a b k : PTm n}
    (h : ZT.toZ Γ (rotRe a b k) ^ 2 + ZT.toZ Γ (rotIm a b k) ^ 2 = 𝔟 (pw (nrm a b) k) * 𝔟 (pw (nrm a b) k)) :
    Γ ⊢[PRAAx] Un a b k := by
  apply ZT.derive
  simp only [ZT.toZ_add, ZT.toZ_sq, ZT.toZ_ofNat, Q.mk_mul, map_mul]
  exact h

theorem un_zero (a b : PTm n) : Γ ⊢[PRAAx] Un a b zero :=
  un_of (cnorm_zero (rRe a b) (rIm a b) (nrm a b))

theorem un_succ {a b k : PTm n} (ih : Γ ⊢[PRAAx] Un a b k) : Γ ⊢[PRAAx] Un a b (succ k) :=
  un_of (cnorm_step (base_norm a b) (un_val ih))

/-- `E_0 = 0`. -/
theorem e_zero (a b : PTm n) : Γ ⊢[PRAAx] nle (Ex a b zero) (Ey a b zero) (Bd a b zero) := by
  have x0 := rot_re_zero (Γ := Γ) a b
  have y0 := rot_im_zero (Γ := Γ) a b
  have w0 := pw_base (Γ := Γ) a b
  refine nle_of_comb 0 ?_ nn_zero
  rsimp
  rw [x0, y0, w0]
  ring

/-- `E_{k+1} = g² E_k + N^k c`. -/
theorem e_succ {a b k : PTm n} (ih : Γ ⊢[PRAAx] nle (Ex a b k) (Ey a b k) (Bd a b k)) :
    Γ ⊢[PRAAx] nle (Ex a b (succ k)) (Ey a b (succ k)) (Bd a b (succ k)) := by
  have r₁ := rot_re_succ (Γ := Γ) a b k
  have r₂ := rot_im_succ (Γ := Γ) a b k
  have ew := pw_step (Γ := Γ) a b k
  refine nle_of (nle_add (nle_mul (g_nle a b) ih) (nle_scale (pw (nrm a b) k) (c_nle a b))) ?_ ?_ ?_
  · rsimp
    linear_combination 𝔟 a * r₁ - 𝔟 a * ew
  · rsimp
    linear_combination 𝔟 a * r₂
  · refine le_of_comb 0 ?_ nn_zero
    rsimp
    linear_combination ((𝔟 k + 1) + (𝔟 k + 1)) * 𝔟 b * ew

/-- `F_0 = 0`. -/
theorem f_zero (a b : PTm n) : Γ ⊢[PRAAx] nle (Fx a b zero) (Fy a b zero) (Cd a b zero) := by
  have x1 := rot_re_succ (Γ := Γ) a b zero
  have y1 := rot_im_succ (Γ := Γ) a b zero
  rw [rot_re_zero, rot_im_zero] at x1 y1
  have w1 := pw_step (Γ := Γ) a b zero
  have w0 := pw_base (Γ := Γ) a b
  rw [w0] at w1
  refine nle_of_comb 0 ?_ nn_zero
  rsimp
  rw [x1, y1, w1, w0]
  ring

/-- `F_{k+1} = N F_k + c E_{k+1}`. -/
theorem f_succ {a b k : PTm n} (ihF : Γ ⊢[PRAAx] nle (Fx a b k) (Fy a b k) (Cd a b k))
    (hE : Γ ⊢[PRAAx] nle (Ex a b (succ k)) (Ey a b (succ k)) (Bd a b (succ k))) :
    Γ ⊢[PRAAx] nle (Fx a b (succ k)) (Fy a b (succ k)) (Cd a b (succ k)) := by
  have r₁ := rot_re_succ (Γ := Γ) a b (succ k)
  have r₂ := rot_im_succ (Γ := Γ) a b (succ k)
  have ew := pw_step (Γ := Γ) a b k
  have ew' := pw_step (Γ := Γ) a b (succ k)
  refine nle_of (nle_add (nle_scale (nrm a b) ihF) (nle_mul (c_nle a b) hE)) ?_ ?_ ?_
  · rsimp
    linear_combination 𝔟 a * 𝔟 a * r₁ - 𝔟 a * 𝔟 a * ew' +
      (𝔟 k + 1) * 𝔟 a * (𝔟 a * (𝔟 b * 𝔟 b) + 𝔟 a * (𝔟 b * 𝔟 b)) * ew
  · rsimp
    linear_combination 𝔟 a * 𝔟 a * r₂ - (𝔟 k + 1) * 𝔟 a * (𝔟 a * 𝔟 a * 𝔟 b + 𝔟 a * 𝔟 a * 𝔟 b) * ew
  · refine le_of_comb 0 ?_ nn_zero
    rsimp
    linear_combination (𝔟 b * 𝔟 b + 𝔟 b * 𝔟 b) * ((𝔟 k + 1) * (𝔟 k + 1 + 1)) * ew'

theorem inv_zero (a b : PTm n) : Γ ⊢[PRAAx] Inv a b zero :=
  .andI (.andI (un_zero a b) (e_zero a b)) (f_zero a b)

theorem inv_succ {a b k : PTm n} (ih : Γ ⊢[PRAAx] Inv a b k) : Γ ⊢[PRAAx] Inv a b (succ k) := by
  have hE := e_succ (Prf.andE₂ (Prf.andE₁ ih))
  exact .andI (.andI (un_succ (Prf.andE₁ (Prf.andE₁ ih))) hE) (f_succ (Prf.andE₂ ih) hE)

/-- Variables: `0 = k` (induction), `1 = a`, `2 = b`. -/
private theorem inv₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] Inv (var 1) (var 2) (var 0) := by
  refine ind _ ⟨⟨trivial, trivial⟩, trivial⟩ ?_ ?_
  · simp only [Inv, Un, cx, cy, cB, Ex, Ey, Bd, Fx, Fy, Cd, Fm.subst_and, ZT.subst_eq, subst_zle, ZT.subst_add,
      ZT.subst_sub, ZT.subst_mul, ZT.subst_neg, ZT.subst_sq, ZT.subst_ofNat, subst_rotRe, subst_rotIm, subst_nrm,
      subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.inst_zero, Syn.inst_one, inst_two, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    exact inv_zero _ _
  · simp only [Inv, Un, cx, cy, cB, Ex, Ey, Bd, Fx, Fy, Cd, Fm.subst_and, ZT.subst_eq, subst_zle, ZT.subst_add,
      ZT.subst_sub, ZT.subst_mul, ZT.subst_neg, ZT.subst_sq, ZT.subst_ofNat, subst_rotRe, subst_rotIm, subst_nrm,
      subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.repl_zero, repl_one, repl_two, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    exact inv_succ Prf.hyp0

/-- The invariant at every exponent. -/
theorem inv (a b k : PTm n) : Γ ⊢[PRAAx] Inv a b k := by
  have h := inst (Γ := Γ) inv₀ (![k, a, b] : Fin 3 → PTm n)
  simpa using h

/-- The unit modulus: `(Re g^{2k})² + (Im g^{2k})² = (N^k)²`. -/
theorem rot_unit (a b k : PTm n) : Γ ⊢[PRAAx] Un a b k :=
  Prf.andE₁ (Prf.andE₁ (inv a b k))

/-- `|a (g^{2k} − N^k)| ≤ 2k b N^k`. -/
theorem e_bound (a b k : PTm n) : Γ ⊢[PRAAx] nle (Ex a b k) (Ey a b k) (Bd a b k) :=
  Prf.andE₂ (Prf.andE₁ (inv a b k))

/-- `|a² (g^{2k+2} − N^{k+1} − (k+1) N^k (g² − N))| ≤ 2b² k(k+1) N^{k+1}`. -/
theorem f_bound (a b k : PTm n) : Γ ⊢[PRAAx] nle (Fx a b k) (Fy a b k) (Cd a b k) :=
  Prf.andE₂ (inv a b k)

/-! ## The first-order remainder -/

/-- `|a² (g^{2n} − N^n) − i 2n a b N^n| ≤ 2 n² b² N^n` for `n = k + 1`: with `w = g²/N` and `u = 2n b/a`,
`|w^n − 1 − i u| ≤ u²/2`. -/
theorem rotation_remainder (a b k : PTm n) :
    Γ ⊢[PRAAx] nle (ZT.ofNat (a * a) * (rotRe a b (succ k) - ZT.ofNat (pw (nrm a b) (succ k))))
      (ZT.ofNat (a * a) * rotIm a b (succ k) -
        ZT.ofNat ((succ k + succ k) * (a * b) * pw (nrm a b) (succ k)))
      ((b * b + b * b) * (succ k * succ k) * pw (nrm a b) (succ k)) := by
  have ew := pw_step (Γ := Γ) a b k
  have h₁ := nle_neg (nle_scale (succ k * pw (nrm a b) k * (b * b + b * b)) (ag_nle (Γ := Γ) a b))
  refine nle_of (nle_add (f_bound a b k) h₁) ?_ ?_ ?_
  · rsimp
    ring
  · rsimp
    linear_combination (-((𝔟 k + 1 + (𝔟 k + 1)) * (𝔟 a * 𝔟 b))) * ew
  · refine le_of_comb 0 ?_ nn_zero
    rsimp
    linear_combination (𝔟 b * 𝔟 b + 𝔟 b * 𝔟 b) * (𝔟 k + 1) * ew

/-! ## The names of `cos (p/q)` and `sin (p/q)` -/

/-- The numerator of `cos_n (p/q)` at the stage `n`: `Re g^{2n}`, `g = 2nq + i p`. -/
def cosNum (q p j : PTm n) : ZT n := rotRe ((j + j) * q) p j

/-- The numerator of `sin_n (p/q)`: `Im g^{2n}`. -/
def sinNum (q p j : PTm n) : ZT n := rotIm ((j + j) * q) p j

/-- The common denominator `N^n`, `N = (2nq)² + p²`. -/
def trigDen (q p j : PTm n) : PTm n := pw (nrm ((j + j) * q) p) j

@[simp] theorem subst_cosNum {m : ℕ} (σ : Fin n → PTm m) (q p j : PTm n) :
    (cosNum q p j).subst σ = cosNum (Syn.subst σ q) (Syn.subst σ p) (Syn.subst σ j) := by
  simp only [cosNum, subst_rotRe, PTm.subst_add, PTm.subst_mul]

@[simp] theorem subst_sinNum {m : ℕ} (σ : Fin n → PTm m) (q p j : PTm n) :
    (sinNum q p j).subst σ = sinNum (Syn.subst σ q) (Syn.subst σ p) (Syn.subst σ j) := by
  simp only [sinNum, subst_rotIm, PTm.subst_add, PTm.subst_mul]

@[simp] theorem subst_trigDen {m : ℕ} (σ : Fin n → PTm m) (q p j : PTm n) :
    Syn.subst σ (trigDen q p j) = trigDen (Syn.subst σ q) (Syn.subst σ p) (Syn.subst σ j) := by
  simp only [trigDen, subst_ap2, subst_nrm, PTm.subst_add, PTm.subst_mul]

/-- The unit modulus of the names: `C² + S² = D²`. -/
theorem cayley_unit (q p j : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sq (cosNum q p j) + ZT.sq (sinNum q p j))
      (ZT.ofNat (trigDen q p j * trigDen q p j)) :=
  rot_unit ((j + j) * q) p j

/-- The first-order remainder of the names at the stage `n = k + 1`:
`|2q² (C − D) + i 2q (q S − p D)| ≤ p² D`, i.e. `|cos_n u − 1 + i (sin_n u − u)| ≤ u²/2` for `u = p/q`. -/
theorem cayley_remainder (q p k : PTm n) :
    Γ ⊢[PRAAx] nle
      (ZT.ofNat (q * q + q * q) * (cosNum q p (succ k) - ZT.ofNat (trigDen q p (succ k))))
      (ZT.ofNat (q + q) * (ZT.ofNat q * sinNum q p (succ k) - ZT.ofNat (p * trigDen q p (succ k))))
      (p * p * trigDen q p (succ k)) := by
  have h := rotation_remainder (Γ := Γ) ((succ k + succ k) * q) p k
  refine nle_cancel (m := k * k + k * k + (k + k + (k + k)) + one) (nle_of h ?_ ?_ ?_)
  · simp only [cosNum, trigDen]
    rsimp
    ring
  · simp only [sinNum, trigDen]
    rsimp
    ring
  · refine le_of_comb 0 ?_ nn_zero
    simp only [trigDen]
    rsimp
    ring

/-! ## Real and imaginary parts -/

/-- `cos_n u ≤ 1`: `C ≤ D`. -/
theorem cos_le_one (q p j : PTm n) : Γ ⊢[PRAAx] zle (cosNum q p j) (ZT.ofNat (trigDen q p j)) :=
  zle_of_nle (nle_of_eq (un_val (a := (j + j) * q) (b := p) (k := j) (cayley_unit q p j)))

/-- `1 − cos_n u ≤ u²/2`: `2q² (D − C) ≤ p² D`, at the stage `n = k + 1`. -/
theorem one_sub_cos_le (q p k : PTm n) :
    Γ ⊢[PRAAx] zle (ZT.ofNat (q * q + q * q) * (ZT.ofNat (trigDen q p (succ k)) - cosNum q p (succ k)))
      (ZT.ofNat (p * p * trigDen q p (succ k))) := by
  have h := zle_of_nle (nle_neg (cayley_remainder (Γ := Γ) q p k))
  refine zle_of_comb (zsl h) ?_ (nn_zsl h)
  simp only [zsl_def, ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_neg]
  ring

/-- `sin_n u − u ≤ u²/2`: `2q (q S − p D) ≤ p² D`. -/
theorem sin_sub_le (q p k : PTm n) :
    Γ ⊢[PRAAx] zle
      (ZT.ofNat (q + q) * (ZT.ofNat q * sinNum q p (succ k) - ZT.ofNat (p * trigDen q p (succ k))))
      (ZT.ofNat (p * p * trigDen q p (succ k))) :=
  zle_of_nle (nle_swap (cayley_remainder q p k))

/-- `u − sin_n u ≤ u²/2`: `2q (p D − q S) ≤ p² D`. -/
theorem sub_sin_le (q p k : PTm n) :
    Γ ⊢[PRAAx] zle
      (ZT.ofNat (q + q) * (ZT.ofNat (p * trigDen q p (succ k)) - ZT.ofNat q * sinNum q p (succ k)))
      (ZT.ofNat (p * p * trigDen q p (succ k))) := by
  have h := zle_of_nle (nle_swap (nle_neg (cayley_remainder (Γ := Γ) q p k)))
  refine zle_of_comb (zsl h) ?_ (nn_zsl h)
  simp only [zsl_def, ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_neg]
  ring

end LeanProofs.IPRA.Analysis.Rotation
