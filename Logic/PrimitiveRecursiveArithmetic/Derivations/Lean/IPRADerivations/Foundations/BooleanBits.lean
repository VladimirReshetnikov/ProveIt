import IPRADerivations.Foundations.BoundedFormulas
import IPRADerivations.Core.Header

/-!
# Truth tables of the Boolean operations on proved bits

Packet: `foundations/scope_ipra_framework_2026-11-16`, `sections/05_bounded_reflection.tex`, Section "Boolean
terms" and the lemma "Boolean truth tables". A term `b` is a proved bit when iPRA derives `b = 0 ∨ b = 1`.
The operations of the packet are

`¬_b b = 1 ∸ b`, `b ∧_b c = b c`, `b ∨_b c = 1 ∸ (1 ∸ b)(1 ∸ c)`, `b ⇒_b c = (¬_b b) ∨_b c`.

For proved bits `b`, `c`:

* `bnot_bit`, `band_bit`, `bor_bit`, `bimp_bit`: the results are bits;
* `bnot_iff`: `¬_b b = 1 ↔ b = 0`;
* `band_iff`: `b ∧_b c = 1 ↔ b = 1 ∧ c = 1`;
* `bor_iff`: `b ∨_b c = 1 ↔ b = 1 ∨ c = 1`;
* `bimp_iff`: `b ⇒_b c = 1 ↔ (b = 0 ∨ c = 1)`.

The same tables with `sg(b + c)` for the disjunction (the FINER packet's choice, `eq:bit-normal`) are the
lemmas `or_left`, `or_right`, `or_none` of `Foundations/BoundedFormulas`.
-/

namespace LeanProofs.IPRA.Foundations.BooleanBits

open_ipra
open LeanProofs.IPRA.Foundations.BoundedFormulas (and_both and_zero_left and_zero_right not_of_zero not_of_one
  clash)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `¬_b b = 1 ∸ b`. -/
abbrev bnot (b : PTm n) : PTm n := monus one b
/-- `b ∧_b c = b c`. -/
abbrev band (b c : PTm n) : PTm n := b * c
/-- `b ∨_b c = 1 ∸ (1 ∸ b)(1 ∸ c)`. -/
abbrev bor (b c : PTm n) : PTm n := monus one (monus one b * monus one c)
/-- `b ⇒_b c = (¬_b b) ∨_b c`. -/
abbrev bimp (b c : PTm n) : PTm n := bor (bnot b) c

/-- `b` is a proved bit. -/
abbrev Bit (b : PTm n) : Fm PTm n := (b ≐ zero) ⋎ (b ≐ one)

section Tables

variable {b c : PTm n}

/-! ## Negation -/

theorem bnot_bit (hb : Γ ⊢[PRAAx] Bit b) : Γ ⊢[PRAAx] Bit (bnot b) :=
  .orE hb (.orI₂ (not_of_zero Prf.hyp0)) (.orI₁ (not_of_one Prf.hyp0))

theorem zero_of_bnot (hb : Γ ⊢[PRAAx] Bit b) (h : Γ ⊢[PRAAx] bnot b ≐ one) : Γ ⊢[PRAAx] b ≐ zero :=
  .orE hb Prf.hyp0 (clash _ (not_of_one Prf.hyp0) h.wk)

/-- `¬_b b = 1 ↔ b = 0`. -/
theorem bnot_iff (hb : Γ ⊢[PRAAx] Bit b) : Γ ⊢[PRAAx] Fm.iff (bnot b ≐ one) (b ≐ zero) :=
  Prf.iffI (.impI (zero_of_bnot hb.wk Prf.hyp0)) (.impI (not_of_zero Prf.hyp0))

/-! ## Conjunction -/

theorem band_bit (hb : Γ ⊢[PRAAx] Bit b) (hc : Γ ⊢[PRAAx] Bit c) : Γ ⊢[PRAAx] Bit (band b c) :=
  .orE hb (.orI₁ (and_zero_left Prf.hyp0))
    (.orE hc.wk (.orI₁ (and_zero_right Prf.hyp0)) (.orI₂ (and_both Prf.hyp1 Prf.hyp0)))

theorem left_of_band (hb : Γ ⊢[PRAAx] Bit b) (h : Γ ⊢[PRAAx] band b c ≐ one) : Γ ⊢[PRAAx] b ≐ one :=
  .orE hb (clash _ (and_zero_left Prf.hyp0) h.wk) Prf.hyp0

theorem right_of_band (hc : Γ ⊢[PRAAx] Bit c) (h : Γ ⊢[PRAAx] band b c ≐ one) : Γ ⊢[PRAAx] c ≐ one :=
  .orE hc (clash _ (and_zero_right Prf.hyp0) h.wk) Prf.hyp0

/-- `b ∧_b c = 1 ↔ b = 1 ∧ c = 1`. -/
theorem band_iff (hb : Γ ⊢[PRAAx] Bit b) (hc : Γ ⊢[PRAAx] Bit c) :
    Γ ⊢[PRAAx] Fm.iff (band b c ≐ one) ((b ≐ one) ⋏ (c ≐ one)) :=
  Prf.iffI (.impI (.andI (left_of_band hb.wk Prf.hyp0) (right_of_band hc.wk Prf.hyp0)))
    (.impI (and_both (Prf.andE₁ Prf.hyp0) (Prf.andE₂ Prf.hyp0)))

/-! ## Disjunction -/

theorem bor_left (h : Γ ⊢[PRAAx] b ≐ one) : Γ ⊢[PRAAx] bor b c ≐ one :=
  not_of_zero (and_zero_left (not_of_one h))

theorem bor_right (h : Γ ⊢[PRAAx] c ≐ one) : Γ ⊢[PRAAx] bor b c ≐ one :=
  not_of_zero (and_zero_right (not_of_one h))

theorem bor_none (hb : Γ ⊢[PRAAx] b ≐ zero) (hc : Γ ⊢[PRAAx] c ≐ zero) : Γ ⊢[PRAAx] bor b c ≐ zero :=
  not_of_one (and_both (not_of_zero hb) (not_of_zero hc))

theorem bor_bit (hb : Γ ⊢[PRAAx] Bit b) (hc : Γ ⊢[PRAAx] Bit c) : Γ ⊢[PRAAx] Bit (bor b c) :=
  .orE hb (.orE hc.wk (.orI₁ (bor_none Prf.hyp1 Prf.hyp0)) (.orI₂ (bor_right Prf.hyp0)))
    (.orI₂ (bor_left Prf.hyp0))

theorem cases_of_bor (hb : Γ ⊢[PRAAx] Bit b) (hc : Γ ⊢[PRAAx] Bit c) (h : Γ ⊢[PRAAx] bor b c ≐ one) :
    Γ ⊢[PRAAx] (b ≐ one) ⋎ (c ≐ one) :=
  .orE hb (.orE hc.wk (clash _ (bor_none Prf.hyp1 Prf.hyp0) h.wk.wk) (.orI₂ Prf.hyp0)) (.orI₁ Prf.hyp0)

/-- `b ∨_b c = 1 ↔ b = 1 ∨ c = 1`. -/
theorem bor_iff (hb : Γ ⊢[PRAAx] Bit b) (hc : Γ ⊢[PRAAx] Bit c) :
    Γ ⊢[PRAAx] Fm.iff (bor b c ≐ one) ((b ≐ one) ⋎ (c ≐ one)) :=
  Prf.iffI (.impI (cases_of_bor hb.wk hc.wk Prf.hyp0))
    (.impI (.orE Prf.hyp0 (bor_left Prf.hyp0) (bor_right Prf.hyp0)))

/-! ## Implication -/

theorem bimp_bit (hb : Γ ⊢[PRAAx] Bit b) (hc : Γ ⊢[PRAAx] Bit c) : Γ ⊢[PRAAx] Bit (bimp b c) :=
  bor_bit (bnot_bit hb) hc

theorem cases_of_bimp (hb : Γ ⊢[PRAAx] Bit b) (hc : Γ ⊢[PRAAx] Bit c) (h : Γ ⊢[PRAAx] bimp b c ≐ one) :
    Γ ⊢[PRAAx] (b ≐ zero) ⋎ (c ≐ one) :=
  .orE (cases_of_bor (bnot_bit hb) hc h) (.orI₁ (zero_of_bnot hb.wk Prf.hyp0)) (.orI₂ Prf.hyp0)

/-- `b ⇒_b c = 1 ↔ (b = 0 ∨ c = 1)`. -/
theorem bimp_iff (hb : Γ ⊢[PRAAx] Bit b) (hc : Γ ⊢[PRAAx] Bit c) :
    Γ ⊢[PRAAx] Fm.iff (bimp b c ≐ one) ((b ≐ zero) ⋎ (c ≐ one)) :=
  Prf.iffI (.impI (cases_of_bimp hb.wk hc.wk Prf.hyp0))
    (.impI (.orE Prf.hyp0 (bor_left (not_of_zero Prf.hyp0)) (bor_right Prf.hyp0)))

end Tables

end LeanProofs.IPRA.Foundations.BooleanBits
