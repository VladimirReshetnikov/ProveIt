import IPRADerivations.Core.SumReflect
import IPRADerivations.Core.SumSplit
import IPRADerivations.Core.Powers
import IPRADerivations.Core.Tactic

/-!
# Global sections of `O(d)` on the projective line

Packet: `geometry/ipra_algebraic_geometry_framework_2026-11-15` (`thm:p1-h0`, the correspondence
between the two chart polynomials). A global section of `O(d)`, `d ≥ 0`, is a coefficient vector
`(c_0, …, c_d)`; on the two charts it is

  `a(t) = ∑_{e ≤ d} c_e t^e`,   `b(u) = ∑_{j ≤ d} c_{d−j} u^j`,

and the cocycle condition is `a(t) = t^d b(t⁻¹)`. With `t = T/U` and denominators cleared this is
the identity of binary forms

  `∑_{e ≤ d} c_e T^e U^(d−e) = ∑_{j ≤ d} c_{d−j} U^j T^(d−j)`.

The data are read from one parameter code `y = ⟨d, ⟨T, ⟨U, x⟩⟩⟩`, with `c_e = c(e, x)` an
arbitrary body.

* `p1_sections`: the identity above, for every `d`, by reflecting the sum.
* `h1_decomposition` (`eq:p1-normal-form`): a degree-one cochain, as a list of terms by increasing
  exponent, is the sum of the block of exponents `≤ d`, the residual block `d < e < 0` and the
  block of exponents `≥ 0`; the outer blocks are the two chart contributions of a coboundary.
* `h1_unique`, `h1_residual_zero`, `h1_dimension`: a coboundary has zero coefficient at every
  exponent `d < e < 0`, so residuals that differ by a coboundary are equal there, and the range has
  `−d − 1` elements.

Coefficients are natural numbers; an integer vector is a difference of two such. The statements
that the kernel is exactly these vectors, and the case `d < 0` are not formalized.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.ProjectiveLine

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `m ∸ (m ∸ i) = i` for `i ≤ m`. -/
theorem monus_monus {i m : PTm n} (h : Γ ⊢[PRAAx] le i m) : Γ ⊢[PRAAx] monus m (monus m i) ≐ i :=
  (congrMonus (eq_add_of_le h) (zero_add _).eqSymm).eqTrans
    ((monus_add_add i zero (monus m i)).eqTrans (monus_zero i))

/-! ## Reading the parameter code `y = ⟨d, ⟨T, ⟨U, x⟩⟩⟩` -/

abbrev dOf {n : ℕ} (y : PTm n) : PTm n := fstT y
abbrev tOf {n : ℕ} (y : PTm n) : PTm n := fstT (sndT y)
abbrev uOf {n : ℕ} (y : PTm n) : PTm n := fstT (sndT (sndT y))
abbrev xOf {n : ℕ} (y : PTm n) : PTm n := sndT (sndT (sndT y))

/-- `c_e T^e U^(d−e)`; variables `0 = e`, `1 = y`. -/
abbrev aB (c : PTm 2) : PTm 2 :=
  Syn.subst ![var 0, xOf (var 1)] c * pw (tOf (var 1)) (var 0) * pw (uOf (var 1)) (monus (dOf (var 1)) (var 0))

/-- `c_{d−j} U^j T^(d−j)`; variables `0 = j`, `1 = y`. -/
abbrev bB (c : PTm 2) : PTm 2 :=
  Syn.subst ![monus (dOf (var 1)) (var 0), xOf (var 1)] c * pw (uOf (var 1)) (var 0) *
    pw (tOf (var 1)) (monus (dOf (var 1)) (var 0))

theorem inst2_a (c : PTm 2) (e y : PTm n) :
    inst2 (aB c) e y = inst2 c e (xOf y) * pw (tOf y) e * pw (uOf y) (monus (dOf y) e) := by
  have h : Syn.subst ![e, y] (Syn.subst ![var 0, xOf (var 1)] c) = inst2 c e (xOf y) := by
    simp only [inst2, Syn.subst_subst]
    congr 1; funext j; fin_cases j <;> simp
  simp only [inst2, PTm.subst_mul, h]
  simp [inst2]

theorem inst2_b (c : PTm 2) (j y : PTm n) :
    inst2 (bB c) j y =
      inst2 c (monus (dOf y) j) (xOf y) * pw (uOf y) j * pw (tOf y) (monus (dOf y) j) := by
  have h : Syn.subst ![j, y] (Syn.subst ![monus (dOf (var 1)) (var 0), xOf (var 1)] c) =
      inst2 c (monus (dOf y) j) (xOf y) := by
    simp only [inst2, Syn.subst_subst]
    congr 1; funext i; fin_cases i <;> simp
  simp only [inst2, PTm.subst_mul, h]
  simp [inst2]

/-! ## The correspondence -/

theorem refl_pt (c : PTm 2) {i y : PTm n} (h : Γ ⊢[PRAAx] le i (dOf y)) :
    Γ ⊢[PRAAx] inst2 (rflBody (aB c)) i (pairT (succ (dOf y)) y) ≐ inst2 (bB c) i y := by
  rw [inst2_rflBody]
  have hk : Γ ⊢[PRAAx] monus (fstT (pairT (succ (dOf y)) y)) (succ i) ≐ monus (dOf y) i :=
    (congrMonus (fst_pair _ _) (.eqRefl _)).eqTrans (succ_monus_succ _ _)
  refine (congrInst2 (aB c) hk (snd_pair _ _)).eqTrans ?_
  rw [inst2_a, inst2_b]
  have e := natEq (congrAp2 powF (monus_monus h) (.eqRefl (uOf y)))
  apply deriveNat; ipra_simps
  linear_combination 𝔞(inst2 c (monus (dOf y) i) (xOf y)) * 𝔞(pw (tOf y) (monus (dOf y) i)) * e

/-- `thm:p1-h0`, the correspondence: `∑_{e ≤ d} c_e T^e U^(d−e) = ∑_{j ≤ d} c_{d−j} U^j T^(d−j)`. -/
theorem p1_sections (c : PTm 2) (y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (aB c)) (succ (dOf y)) y ≐ ap2 (sumF (bB c)) (succ (dOf y)) y := by
  refine (sum_reflect (aB c) (succ (dOf y)) y).eqTrans ?_
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  have e : Syn.shift (pairT (succ (dOf y)) y) = pairT (succ (dOf (Syn.shift y))) (Syn.shift y) := by
    simp [Syn.shift]
  have e' : Syn.shift (succ (dOf y)) = succ (dOf (Syn.shift y)) := by simp [Syn.shift]
  rw [e]
  rw [e'] at *
  exact refl_pt c ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0)

/-! ## The `H¹` normal form -/

/-- `eq:p1-normal-form`. A degree-one cochain of `O(d)`, `d ≤ −2`, is a Laurent polynomial; list
its terms `g(i)` by increasing exponent, with `A` terms of exponent `≤ d`, then the `R = −d − 1`
terms of exponent `d < e < 0`, then `H` terms of exponent `≥ 0`. The first block is the
contribution `−t^d b(t⁻¹)` of the second chart and the last block is the contribution `a(t)` of
the first chart, so the cochain is a coboundary plus the residual block. -/
theorem h1_decomposition (g : PTm 2) (A R H x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF g) (A + R + H) x ≐
      ap2 (sumF g) A x + ap2 (sumF (offB g)) R (pairT A x) + ap2 (sumF (offB g)) H (pairT (A + R) x) :=
  sum_split₃ g A R H x

/-! ## Uniqueness of the residual -/

section Residual

/-- `[k ≤ N]`. -/
abbrev gle' {n : ℕ} (k N : PTm n) : PTm n := monus one (monus k N)

theorem gle'_above {k N : PTm n} (h : Γ ⊢[PRAAx] le (succ N) k) : Γ ⊢[PRAAx] gle' k N ≐ zero := by
  have e : Γ ⊢[PRAAx] k ≐ succ (monus k (succ N)) + N := by
    have a := natEq (eq_add_of_le h)
    apply deriveNat; ipra_simps; linear_combination a
  have m : Γ ⊢[PRAAx] monus k N ≐ succ (monus k (succ N)) := (congrMonus e (.eqRefl _)).eqTrans (add_monus _ _)
  exact (congrMonus (.eqRefl _) m).eqTrans ((succ_monus_succ _ _).eqTrans (zero_monus _))

/-- The coefficient of a coboundary `δ(a, b) = a(t) − t^d b(t⁻¹)` at the shifted exponent `e`
(exponent `e − A`, with `d = −D`, so that the `b` part sits at `e ≤ A ∸ D`): the positive part
`[A ≤ e] a_{e−A}` and the negative part `[e ≤ A ∸ D] b_{(A ∸ D) − e}`. -/
abbrev cobPos {n : ℕ} (A e pa : PTm n) : PTm n := gle' A e * pa
abbrev cobNeg {n : ℕ} (A D e pb : PTm n) : PTm n := gle' e (monus A D) * pb

theorem cob_zero_pos {A e : PTm n} (pa : PTm n) (h₂ : Γ ⊢[PRAAx] lt e A) : Γ ⊢[PRAAx] cobPos A e pa ≐ zero :=
  (congrMul (gle'_above h₂) (.eqRefl _)).eqTrans (zero_mul _)

theorem cob_zero_neg {A D e : PTm n} (pb : PTm n) (h₁ : Γ ⊢[PRAAx] lt (monus A D) e) :
    Γ ⊢[PRAAx] cobNeg A D e pb ≐ zero :=
  (congrMul (gle'_above h₁) (.eqRefl _)).eqTrans (zero_mul _)

/-- `thm:p1-h1`, uniqueness: at an exponent `d < e − A < 0` a coboundary has zero coefficient, so
residuals `R₁, R₂` with `R₁ − R₂ = δ(a, b)` there are equal. -/
theorem h1_unique {A D e R₁ R₂ pa pb : PTm n} (h₁ : Γ ⊢[PRAAx] lt (monus A D) e) (h₂ : Γ ⊢[PRAAx] lt e A)
    (h : Γ ⊢[PRAAx] R₁ + cobNeg A D e pb ≐ R₂ + cobPos A e pa) : Γ ⊢[PRAAx] R₁ ≐ R₂ := by
  have a := natEq (cob_zero_neg (D := D) pb h₁); have b := natEq (cob_zero_pos pa h₂)
  have c := natEq h
  apply deriveNat; ipra_simps
  linear_combination c - a + b

/-- In particular a residual that is a coboundary is zero. -/
theorem h1_residual_zero {A D e R pa pb : PTm n} (h₁ : Γ ⊢[PRAAx] lt (monus A D) e) (h₂ : Γ ⊢[PRAAx] lt e A)
    (h : Γ ⊢[PRAAx] R + cobNeg A D e pb ≐ cobPos A e pa) : Γ ⊢[PRAAx] R ≐ zero :=
  h1_unique h₁ h₂ (h.eqTrans (zero_add _).eqSymm)

/-- The residual range `A ∸ D < e < A` has `D − 1` elements for `1 ≤ D ≤ A`: the dimension
`−d − 1` of `Ȟ¹(P¹, O(d))`. -/
theorem h1_dimension {A D : PTm n} (h : Γ ⊢[PRAAx] le D A) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] monus A (succ (monus A D)) ≐ monus D one := by
  have e₁ := natEq (eq_add_of_le h); have e₂ := natEq (eq_add_of_le hD)
  have m₁ : Γ ⊢[PRAAx] A ≐ monus D one + succ (monus A D) := by
    apply deriveNat; ipra_simps; linear_combination e₁ + e₂
  exact (congrMonus m₁ (.eqRefl _)).eqTrans (add_monus _ _)

end Residual

end LeanProofs.IPRA.Geometry.ProjectiveLine
