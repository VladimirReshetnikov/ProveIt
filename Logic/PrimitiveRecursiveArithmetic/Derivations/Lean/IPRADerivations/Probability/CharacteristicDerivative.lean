import IPRADerivations.Analysis.Trigonometry.UnitCircle.RotationRemainder
import IPRADerivations.Probability.Expectation

/-!
# The derivative of a characteristic function at zero

Packet: `probability/expected_value_ipra_2026-11-16`, `paper/sections/13_fourier_applications.tex`, Theorem
`thm:char-derivative` ("Derivative of the characteristic function at zero"): for a finite rational law and a
rational `h ≠ 0`, `|(φ_X(h) − 1)/h − i E[X]| ≤ (|h|/2) E[X²]`, with `φ_X(t) = E[cos(tX)] + i E[sin(tX)]`. The
proof "puts `u = h X_i`, divides by `|h|`, and takes expectations" of `|e^{iu} − 1 − iu| ≤ u²/2`.

The law is a weight body `w(i, x) ≥ 0` on the outcomes `i < N` with natural values `X(i, x)`
(`Probability/Expectation`), and `h = p/q > 0` (the statement is even in `h`). The cosine and sine names are the
unit-circle approximants of `Analysis/Trigonometry/UnitCircle/RotationRemainder`: at the stage `n = k + 1` and the
outcome `i`, `cos_n(h X_i) = C_i/D_i`, `sin_n(h X_i) = S_i/D_i` with `C_i = cosNum q (p X_i) n`,
`S_i = sinNum q (p X_i) n`, `D_i = trigDen q (p X_i) n`. The denominators depend on the outcome, so a common
denominator `D = cof_i D_i` with a cofactor body `cof` is part of the data, and `φ_n(h) = (SC + i SS)/(D W)` for
`SC = Σ_i w_i cof_i C_i`, `SS = Σ_i w_i cof_i S_i`, `W = Σ_i w_i`.

* `zsumw`, `zsumw_zero`, `zsumw_succ`: weighted sums `Σ_{i<N} w_i t_i` of an integer-valued body;
* `complex_triangle`: `|Σ_i w_i z_i| ≤ Σ_i w_i r_i` when `|z_i| ≤ r_i` on the outcomes, for complex-integer
  valued bodies (the triangle inequality `|E[Z]| ≤ E|Z|`, without square roots);
* `char_derivative_of`: if on every outcome `|2q² (c_i − d_i) + i 2q (q s_i − p X_i d_i)| ≤ (p X_i)² d_i` (the
  first-order remainder `|e^{iu} − 1 − iu| ≤ u²/2` at `u = p X_i/q`, cleared by `2q² d_i`) and `cof_i d_i = D`,
  then `|2q² (SC − D W) + i 2q (q SS − p D E_w[X])| ≤ p² D E_w[X²]`;
* `char_derivative` (`thm:char-derivative`): the same conclusion for the names, i.e. for bodies that are
  `cosNum`, `sinNum`, `trigDen` on the outcomes; divided by `2q² D W` it reads
  `|φ_n(h) − 1 − i h E[X]| ≤ (h²/2) E[X²]`, at every stage `n = k + 1` of the names, with no error term.

The statement for the limit `φ_X(h)` of the stages, and the passage to infinite laws by truncation, are not
derived here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.CharacteristicDerivative

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.ComplexPowers
open LeanProofs.IPRA.Analysis.Rotation (cosNum sinNum trigDen cayley_remainder)
open LeanProofs.IPRA.Probability.Expectation (Ew Wt inst2_mul')
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Weighted sums of an integer-valued body -/

/-- `Σ_{i<N} w_i t_i` for an integer-valued body `t`. -/
def zsumw (w : PTm 2) (t : ZT 2) (N x : PTm n) : ZT n := ⟨Ew w t.pos N x, Ew w t.neg N x⟩

/-- The value `t(i, x)` of an integer-valued body. -/
abbrev zinst (t : ZT 2) (i x : PTm n) : ZT n := ⟨inst2 t.pos i x, inst2 t.neg i x⟩

@[simp] theorem subst_zsumw {m : ℕ} (σ : Fin n → PTm m) (w : PTm 2) (t : ZT 2) (N x : PTm n) :
    (zsumw w t N x).subst σ = zsumw w t (Syn.subst σ N) (Syn.subst σ x) := by
  show (⟨Syn.subst σ (Ew w t.pos N x), Syn.subst σ (Ew w t.neg N x)⟩ : ZT m) = _
  simp only [subst_ap2]
  rfl

theorem zsumw_zero (w : PTm 2) (t : ZT 2) (x : PTm n) : ZT.toZ Γ (zsumw w t zero x) = 0 := by
  have e₁ := natEq (sum_zero (Γ := Γ) (w * t.pos) x)
  have e₂ := natEq (sum_zero (Γ := Γ) (w * t.neg) x)
  show (𝔟 (Ew w t.pos zero x) - 𝔟 (Ew w t.neg zero x) : Groth (Q Γ)) = 0
  linear_combination e₁ - e₂

theorem zsumw_succ (w : PTm 2) (t : ZT 2) (J x : PTm n) :
    ZT.toZ Γ (zsumw w t (succ J) x) =
      ZT.toZ Γ (zsumw w t J x) + 𝔟 (inst2 w J x) * ZT.toZ Γ (zinst t J x) := by
  have s₁ := sum_succ' (Γ := Γ) (w * t.pos) J x
  rw [inst2_mul'] at s₁
  have s₂ := sum_succ' (Γ := Γ) (w * t.neg) J x
  rw [inst2_mul'] at s₂
  have e₁ := natEq s₁
  have e₂ := natEq s₂
  simp only [Q.mk_add, Q.mk_mul, map_add, map_mul] at e₁ e₂
  show (𝔟 (Ew w t.pos (succ J) x) - 𝔟 (Ew w t.neg (succ J) x) : Groth (Q Γ)) =
    (𝔟 (Ew w t.pos J x) - 𝔟 (Ew w t.neg J x)) +
      𝔟 (inst2 w J x) * (𝔟 (inst2 t.pos J x) - 𝔟 (inst2 t.neg J x))
  linear_combination e₁ - e₂

/-! ## The triangle inequality for expectations of complex-integer values -/

section Triangle

variable (w : PTm 2) (tx ty : ZT 2) (r : PTm 2)

/-- `|Σ_{i<J} w_i z_i| ≤ Σ_{i<J} w_i r_i`. -/
abbrev CInv (J x : PTm n) : Fm PTm n := nle (zsumw w tx J x) (zsumw w ty J x) (Ew w r J x)

theorem ctri_base (x : PTm n) : Γ ⊢[PRAAx] CInv w tx ty r zero x := by
  have z := natEq (sum_zero (Γ := Γ) (w * r) x)
  simp only [Q.mk_zero, map_zero] at z
  refine nle_of_comb 0 ?_ nn_zero
  rw [zsumw_zero, zsumw_zero, z]
  ring

theorem ctri_step {J x : PTm n} (hpt : Γ ⊢[PRAAx] nle (zinst tx J x) (zinst ty J x) (inst2 r J x))
    (ih : Γ ⊢[PRAAx] CInv w tx ty r J x) : Γ ⊢[PRAAx] CInv w tx ty r (succ J) x := by
  have s₀ := sum_succ' (Γ := Γ) (w * r) J x
  rw [inst2_mul'] at s₀
  have s := natEq s₀
  simp only [Q.mk_add, Q.mk_mul, map_add, map_mul] at s
  refine nle_of (nle_add ih (nle_scale (inst2 w J x) hpt)) ?_ ?_ ?_
  · rw [zsumw_succ]
    simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_ofNat]
  · rw [zsumw_succ]
    simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_ofNat]
  · refine le_of_comb 0 ?_ nn_zero
    simp only [Q.mk_add, Q.mk_mul, map_add, map_mul]
    linear_combination s

theorem ctri_all {N x : PTm n}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      nle (zinst tx (var 0) (Syn.shift x)) (zinst ty (var 0) (Syn.shift x)) (inst2 r (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶ CInv w tx ty r (var 0) (Syn.shift x)) := by
  refine qfIndAllUpTo N (P := CInv w tx ty r (var 0) (Syn.shift x)) (le_QF _ _) ?_ ?_
  · simpa using ctri_base (Γ := Γ) w tx ty r x
  · simp
    exact .impI (ctri_step w tx ty r (.impE h.allOpen.wk.wk Prf.hyp0) Prf.hyp1)

/-- `|E[Z]| ≤ E|Z|` for a finite law: `|z_i| ≤ r_i` on the outcomes gives
`|Σ_{i<N} w_i z_i| ≤ Σ_{i<N} w_i r_i`. -/
theorem complex_triangle {N x : PTm n}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      nle (zinst tx (var 0) (Syn.shift x)) (zinst ty (var 0) (Syn.shift x)) (inst2 r (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] CInv w tx ty r N x := by
  have hh := Prf.allE N (ctri_all w tx ty r h)
  have e : (le (var 0) (Syn.shift N) ⟶ CInv w tx ty r (var 0) (Syn.shift x)).subst (Syn.inst N) =
      (le N N ⟶ CInv w tx ty r N x) := by
    simp
  rw [e] at hh
  exact Prf.impE hh (le_refl N)

end Triangle

/-! ## The first-order remainder of a characteristic function -/

/-- The first-order remainder at one outcome with the value `Xv`, for the cosine and sine numerators `c`, `s`
over the denominator `d` and `h = p/q`: `|2q² (c − d) + i 2q (q s − p Xv d)| ≤ (p Xv)² d`, i.e.
`|c/d − 1 + i (s/d − u)| ≤ u²/2` with `u = p Xv/q`. -/
abbrev remF (q p : PTm n) (c s : ZT n) (d Xv : PTm n) : Fm PTm n :=
  nle (ZT.ofNat (q * q + q * q) * (c - ZT.ofNat d))
    (ZT.ofNat (q + q) * (ZT.ofNat q * s - ZT.ofNat (p * Xv * d))) (p * Xv * (p * Xv) * d)

section Remainder

variable (w X cof : PTm 2) (cs sn : ZT 2) (dn : PTm 2)

/-- The summed remainder at the length `J`:
`|2q² (SC − D W) + i 2q (q SS − p D E_w[X])| ≤ p² D E_w[X²]`. -/
abbrev DInv (q p D J x : PTm n) : Fm PTm n :=
  nle (ZT.ofNat (q * q + q * q) * (zsumw (w * cof) cs J x - ZT.ofNat (D * Wt w J x)))
    (ZT.ofNat (q + q) * (ZT.ofNat q * zsumw (w * cof) sn J x - ZT.ofNat (p * D * Ew w X J x)))
    (p * p * D * Ew w (X * X) J x)

theorem dinv_base (q p D x : PTm n) : Γ ⊢[PRAAx] DInv w X cof cs sn q p D zero x := by
  have zW := natEq (sum_zero (Γ := Γ) w x)
  have zX := natEq (sum_zero (Γ := Γ) (w * X) x)
  have zXX := natEq (sum_zero (Γ := Γ) (w * (X * X)) x)
  simp only [Q.mk_zero, map_zero] at zW zX zXX
  refine nle_of_comb 0 ?_ nn_zero
  simp only [ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_ofNat, Q.mk_mul, map_mul, zsumw_zero]
  rw [zW, zX, zXX]
  ring

theorem dinv_step {q p D J x : PTm n} (hD : Γ ⊢[PRAAx] inst2 cof J x * inst2 dn J x ≐ D)
    (hR : Γ ⊢[PRAAx] remF q p (zinst cs J x) (zinst sn J x) (inst2 dn J x) (inst2 X J x))
    (ih : Γ ⊢[PRAAx] DInv w X cof cs sn q p D J x) :
    Γ ⊢[PRAAx] DInv w X cof cs sn q p D (succ J) x := by
  have eD := natEq hD
  have sW := natEq (sum_succ' (Γ := Γ) w J x)
  have sX₀ := sum_succ' (Γ := Γ) (w * X) J x
  rw [inst2_mul'] at sX₀
  have sX := natEq sX₀
  have sXX₀ := sum_succ' (Γ := Γ) (w * (X * X)) J x
  rw [inst2_mul', inst2_mul'] at sXX₀
  have sXX := natEq sXX₀
  have sC := zsumw_succ (Γ := Γ) (w * cof) cs J x
  have sS := zsumw_succ (Γ := Γ) (w * cof) sn J x
  rw [inst2_mul'] at sC sS
  simp only [Q.mk_add, Q.mk_mul, map_add, map_mul] at eD sW sX sXX sC sS
  refine nle_of (nle_add ih (nle_scale (inst2 w J x * inst2 cof J x) hR)) ?_ ?_ ?_
  · simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_ofNat, Q.mk_add, Q.mk_mul, map_add, map_mul]
    linear_combination (𝔟 q * 𝔟 q + 𝔟 q * 𝔟 q) * sC - (𝔟 q * 𝔟 q + 𝔟 q * 𝔟 q) * 𝔟 D * sW +
      (𝔟 q * 𝔟 q + 𝔟 q * 𝔟 q) * 𝔟 (inst2 w J x) * eD
  · simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_ofNat, Q.mk_add, Q.mk_mul, map_add, map_mul]
    linear_combination (𝔟 q + 𝔟 q) * 𝔟 q * sS - (𝔟 q + 𝔟 q) * 𝔟 p * 𝔟 D * sX +
      (𝔟 q + 𝔟 q) * 𝔟 p * 𝔟 (inst2 w J x) * 𝔟 (inst2 X J x) * eD
  · refine le_of_comb 0 ?_ nn_zero
    simp only [Q.mk_add, Q.mk_mul, map_add, map_mul]
    linear_combination 𝔟 p * 𝔟 p * 𝔟 D * sXX -
      𝔟 p * 𝔟 p * 𝔟 (inst2 w J x) * 𝔟 (inst2 X J x) * 𝔟 (inst2 X J x) * eD

theorem dinv_all {q p D N x : PTm n}
    (hD : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (inst2 cof (var 0) (Syn.shift x) * inst2 dn (var 0) (Syn.shift x) ≐ Syn.shift D)))
    (hR : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      remF (Syn.shift q) (Syn.shift p) (zinst cs (var 0) (Syn.shift x)) (zinst sn (var 0) (Syn.shift x))
        (inst2 dn (var 0) (Syn.shift x)) (inst2 X (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶
      DInv w X cof cs sn (Syn.shift q) (Syn.shift p) (Syn.shift D) (var 0) (Syn.shift x)) := by
  refine qfIndAllUpTo N (P := DInv w X cof cs sn
    (Syn.shift q) (Syn.shift p) (Syn.shift D) (var 0) (Syn.shift x)) (le_QF _ _) ?_ ?_
  · simpa using dinv_base (Γ := Γ) w X cof cs sn q p D x
  · simp
    exact .impI (dinv_step w X cof cs sn dn (.impE hD.allOpen.wk.wk Prf.hyp0)
      (.impE hR.allOpen.wk.wk Prf.hyp0) Prf.hyp1)

/-- The first-order remainder of the expectation from the remainders on the outcomes and a common denominator
`D = cof_i d_i`: `|2q² (SC − D W) + i 2q (q SS − p D E_w[X])| ≤ p² D E_w[X²]`. -/
theorem char_derivative_of {q p D N x : PTm n}
    (hD : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (inst2 cof (var 0) (Syn.shift x) * inst2 dn (var 0) (Syn.shift x) ≐ Syn.shift D)))
    (hR : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      remF (Syn.shift q) (Syn.shift p) (zinst cs (var 0) (Syn.shift x)) (zinst sn (var 0) (Syn.shift x))
        (inst2 dn (var 0) (Syn.shift x)) (inst2 X (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] DInv w X cof cs sn q p D N x := by
  have h := Prf.allE N (dinv_all w X cof cs sn dn hD hR)
  have e : (le (var 0) (Syn.shift N) ⟶
        DInv w X cof cs sn (Syn.shift q) (Syn.shift p) (Syn.shift D) (var 0) (Syn.shift x)).subst
        (Syn.inst N) = (le N N ⟶ DInv w X cof cs sn q p D N x) := by
    simp
  rw [e] at h
  exact Prf.impE h (le_refl N)

/-- `thm:char-derivative` for the unit-circle names at the stage `n = k + 1`: if on the outcomes `i < N` the
bodies `cs`, `sn`, `dn` are the numerators and the denominator of `cos_n (p X_i/q)`, `sin_n (p X_i/q)` and
`cof_i dn_i = D`, then `|2q² (SC − D W) + i 2q (q SS − p D E_w[X])| ≤ p² D E_w[X²]`: with
`φ_n(h) = (SC + i SS)/(D W)` and `h = p/q`, `|φ_n(h) − 1 − i h E[X]| ≤ (h²/2) E[X²]`. -/
theorem char_derivative {q p k D N x : PTm n}
    (hC : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      ZT.eq (zinst cs (var 0) (Syn.shift x))
        (cosNum (Syn.shift q) (Syn.shift p * inst2 X (var 0) (Syn.shift x)) (succ (Syn.shift k)))))
    (hS : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      ZT.eq (zinst sn (var 0) (Syn.shift x))
        (sinNum (Syn.shift q) (Syn.shift p * inst2 X (var 0) (Syn.shift x)) (succ (Syn.shift k)))))
    (hN : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (inst2 dn (var 0) (Syn.shift x) ≐
        trigDen (Syn.shift q) (Syn.shift p * inst2 X (var 0) (Syn.shift x)) (succ (Syn.shift k)))))
    (hD : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (inst2 cof (var 0) (Syn.shift x) * inst2 dn (var 0) (Syn.shift x) ≐ Syn.shift D))) :
    Γ ⊢[PRAAx] DInv w X cof cs sn q p D N x := by
  refine char_derivative_of w X cof cs sn dn hD (.allI (.impI ?_))
  have c := ZT.toZ_eq (Prf.impE hC.allOpen.wk Prf.hyp0)
  have s := ZT.toZ_eq (Prf.impE hS.allOpen.wk Prf.hyp0)
  have d := natEq (Prf.impE hN.allOpen.wk Prf.hyp0)
  have r := cayley_remainder (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) (Syn.shift q)
    (Syn.shift p * inst2 X (var 0) (Syn.shift x)) (Syn.shift k)
  refine nle_of r ?_ ?_ ?_
  · simp only [ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_ofNat]
    rw [c, d]
  · simp only [ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_ofNat, Q.mk_mul, map_mul]
    rw [s, d]
  · refine le_of_comb 0 ?_ nn_zero
    simp only [Q.mk_mul, map_mul]
    rw [d]
    ring

end Remainder

end LeanProofs.IPRA.Probability.CharacteristicDerivative
