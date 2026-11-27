import IPRADerivations.Foundations.BoundedFormulas

/-!
# Bounded-formula compilation with certificate checkers

Packet: `foundations/STRIVE-iPRA-framework-2026-11-16`, `paper/sections/06_compiler_proof.tex`, Theorem
"STRIVE bounded-formula compilation": for every fixed bounded formula `A` one can construct primitive
recursive terms `Val_A`, `P_A^±`, `C_A^±`, `κ_A^±` with iPRA derivations of

* (6.1) `Val_A = 0 ∨ Val_A = 1`;   (6.2) `Val_A = 1 ↔ A`;
* (6.3) `C_A^+(c) = 1 → A`;   (6.4) `C_A^-(c) = 1 → ¬A`;   (6.5) `C_A^±(c) = 1 → c < P_A^±`;
* (6.6) `Val_A = 1 → C_A^+(κ_A^+) = 1`;   (6.7) `Val_A = 0 → C_A^-(κ_A^-) = 1`,

uniformly in the free parameters, without an object-language evaluator for formula codes.

`Val_A` is the bit of the compiler `Foundations/BoundedFormulas` (`bitAt`; (6.1) and (6.2) are `bf_cases` and
`bf_reflect`). The checkers here are the canonical one-point certificates: `C_A^+(c) = Val_A · [c = 0]`,
`C_A^-(c) = [Val_A = 0] · [c = 0]`, `P_A^± = 1`, `κ_A^± = 0`. They satisfy (6.3)–(6.7) for every bounded
formula; the paper's informative certificates (witness lists for the quantifiers) refine this choice and are
not constructed here.

* `val_cases`, `val_iff`: (6.1), (6.2);
* `bits_one`: a product of two bits equal to `1` has both factors `1`;
* `cplus_sound`, `cminus_sound`, `cplus_bound`, `cminus_bound`: (6.3)–(6.5);
* `cplus_complete`, `cminus_complete`: (6.6), (6.7).
-/

namespace LeanProofs.IPRA.Foundations.StriveCompilation

open_ipra exports
open LeanProofs.IPRA.Foundations.BoundedFormulas (BF bitAt fmAt bf_reflect bf_cases)
open LeanProofs.IPRA.Foundations.BoundedReflection (eqb_cases eq_of_eqb one_ne_zero)

variable {m : ℕ} {Δ : List (Fm PTm m)}

/-- `Val_A`. -/
abbrev Val (A : BF) (y : PTm m) : PTm m := bitAt A m y
/-- `C_A^+(c) = Val_A · [c = 0]`. -/
abbrev Cplus (A : BF) (y c : PTm m) : PTm m := Val A y * eqb c zero
/-- `C_A^-(c) = [Val_A = 0] · [c = 0]`. -/
abbrev Cminus (A : BF) (y c : PTm m) : PTm m := eqb (Val A y) zero * eqb c zero

/-- (6.1). -/
theorem val_cases (A : BF) (y : PTm m) : Δ ⊢[PRAAx] (Val A y ≐ zero) ⋎ (Val A y ≐ one) := bf_cases A y

/-- (6.2). -/
theorem val_iff (A : BF) (y : PTm m) : Δ ⊢[PRAAx] Fm.iff (Val A y ≐ one) (fmAt A m y) :=
  Prf.iffSymm (bf_reflect A y)

/-- A product of two bits equal to `1` has both factors `1`. -/
theorem bits_one {a b : PTm m} (ha : Δ ⊢[PRAAx] (a ≐ zero) ⋎ (a ≐ one)) (hb : Δ ⊢[PRAAx] (b ≐ zero) ⋎ (b ≐ one))
    (h : Δ ⊢[PRAAx] a * b ≐ one) : Δ ⊢[PRAAx] (a ≐ one) ⋏ (b ≐ one) := by
  refine .orE ha ?_ ?_
  · exact one_ne_zero _ (h.wk.eqSymm.eqTrans ((congrMul Prf.hyp0 (.eqRefl b)).eqTrans (zero_mul b)))
  · refine .orE hb.wk ?_ ?_
    · exact one_ne_zero _ (h.wk.wk.eqSymm.eqTrans ((congrMul (.eqRefl a) Prf.hyp0).eqTrans (mul_zero a)))
    · exact .andI Prf.hyp1 Prf.hyp0

/-- (6.3): `C_A^+(c) = 1 → A`. -/
theorem cplus_sound (A : BF) {y c : PTm m} (h : Δ ⊢[PRAAx] Cplus A y c ≐ one) : Δ ⊢[PRAAx] fmAt A m y :=
  Prf.iffMp (val_iff A y) (Prf.andE₁ (bits_one (val_cases A y) (eqb_cases c zero) h))

/-- (6.4): `C_A^-(c) = 1 → ¬A`. -/
theorem cminus_sound (A : BF) {y c : PTm m} (h : Δ ⊢[PRAAx] Cminus A y c ≐ one) :
    Δ ⊢[PRAAx] neg (fmAt A m y) := by
  have b := bits_one (eqb_cases (Val A y) zero) (eqb_cases c zero) h
  have v0 := eq_of_eqb (Prf.andE₁ b)
  refine .impI ?_
  have v1 := Prf.iffMpr (val_iff (Δ := fmAt A m y :: Δ) A y) Prf.hyp0
  exact one_ne_zero _ (v1.eqSymm.eqTrans v0.wk)

/-- (6.5) for `C_A^+`: `C_A^+(c) = 1 → c < 1`. -/
theorem cplus_bound (A : BF) {y c : PTm m} (h : Δ ⊢[PRAAx] Cplus A y c ≐ one) : Δ ⊢[PRAAx] lt c one := by
  have e := eq_of_eqb (Prf.andE₂ (bits_one (val_cases A y) (eqb_cases c zero) h))
  exact lt_congr e.eqSymm (.eqRefl _) (show Δ ⊢[PRAAx] le (succ zero) one from le_refl _)

/-- (6.5) for `C_A^-`. -/
theorem cminus_bound (A : BF) {y c : PTm m} (h : Δ ⊢[PRAAx] Cminus A y c ≐ one) : Δ ⊢[PRAAx] lt c one := by
  have e := eq_of_eqb (Prf.andE₂ (bits_one (eqb_cases (Val A y) zero) (eqb_cases c zero) h))
  exact lt_congr e.eqSymm (.eqRefl _) (show Δ ⊢[PRAAx] le (succ zero) one from le_refl _)

/-- (6.6): `Val_A = 1 → C_A^+(0) = 1`. -/
theorem cplus_complete (A : BF) {y : PTm m} (h : Δ ⊢[PRAAx] Val A y ≐ one) :
    Δ ⊢[PRAAx] Cplus A y zero ≐ one :=
  (congrMul h (eqb_of_eq (.eqRefl zero))).eqTrans (one_mul _)

/-- (6.7): `Val_A = 0 → C_A^-(0) = 1`. -/
theorem cminus_complete (A : BF) {y : PTm m} (h : Δ ⊢[PRAAx] Val A y ≐ zero) :
    Δ ⊢[PRAAx] Cminus A y zero ≐ one :=
  (congrMul (eqb_of_eq h) (eqb_of_eq (.eqRefl zero))).eqTrans (one_mul _)

end LeanProofs.IPRA.Foundations.StriveCompilation
