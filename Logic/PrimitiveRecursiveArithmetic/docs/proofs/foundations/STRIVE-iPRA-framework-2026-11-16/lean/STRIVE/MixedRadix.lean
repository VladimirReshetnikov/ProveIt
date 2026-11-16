import IPRADerivations.Core.Division
import IPRADerivations.Core.MultiSums
import IPRADerivations.Core.Powers

/-!
# STRIVE-iPRA: heterogeneous mixed-radix strategy tables

This is a dependency-accurate Lean blueprint.  It is deliberately phrased in
ordinary `Prf PRAAx`; the `sorry` markers are public formalization milestones,
not hidden assumptions.  The intended implementation specializes `digitBody`
and `radixBody` to concrete table-entry functions generated for one fixed
bounded formula.
-/

namespace LeanProofs.IPRA.STRIVE

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Prefix product `Π_{j<i} B(j,p,q)`. -/
abbrev radixPrefix (radixBody : PTm 3) (i p q : PTm n) : PTm n :=
  ap3 (prod2F radixBody) i p q

/-- Weight a table digit by the product of earlier radices.  Variables are
`0=i`, `1=p`, `2=q`. -/
def weightedDigit (digitBody radixBody : PTm 3) : PTm 3 :=
  digitBody * ap3 (prod2F radixBody) (var 0) (var 1) (var 2)

/-- `Σ_{i<N} a_i Π_{j<i} B_j`. -/
abbrev pack (digitBody radixBody : PTm 3) (N p q : PTm n) : PTm n :=
  ap3 (sum2F (weightedDigit digitBody radixBody)) N p q

/-- The `i`th heterogeneous digit of `code`.  Positivity of the prefix and
current radix is supplied at theorem boundaries. -/
abbrev digitAt (code : PTm n) (radixBody : PTm 3) (i p q : PTm n) : PTm n :=
  rem (quo code (radixPrefix radixBody i p q)) (inst3 radixBody i p q)

/-- Empty prefix products are one. -/
theorem prefix_zero (radixBody : PTm 3) (p q : PTm n) :
    Γ ⊢[PRAAx] radixPrefix radixBody zero p q ≐ one := by
  simpa [radixPrefix] using prod2_zero (Γ := Γ) radixBody p q

/-- Prefix-product recurrence. -/
theorem prefix_succ (radixBody : PTm 3) (i p q : PTm n) :
    Γ ⊢[PRAAx] radixPrefix radixBody (succ i) p q ≐
      radixPrefix radixBody i p q * inst3 radixBody i p q := by
  simpa [radixPrefix] using prod2_succ (Γ := Γ) radixBody i p q

/-- Empty tables have code zero. -/
theorem pack_zero (digitBody radixBody : PTm 3) (p q : PTm n) :
    Γ ⊢[PRAAx] pack digitBody radixBody zero p q ≐ zero := by
  simpa [pack, weightedDigit] using
    sum2_zero (Γ := Γ) (weightedDigit digitBody radixBody) p q

/-- Appending one digit extends the weighted sum. -/
theorem pack_succ (digitBody radixBody : PTm 3) (N p q : PTm n) :
    Γ ⊢[PRAAx] pack digitBody radixBody (succ N) p q ≐
      pack digitBody radixBody N p q +
        inst3 digitBody N p q * radixPrefix radixBody N p q := by
  simpa [pack, weightedDigit, radixPrefix, inst3] using
    sum2_succ (Γ := Γ) (weightedDigit digitBody radixBody) N p q

/-- Every prefix product is positive when all preceding radices are positive. -/
theorem prefix_positive (radixBody : PTm 3) {i p q : PTm n}
    (hradix : Γ ⊢[PRAAx] Fm.all
      (lt (var 0) (Syn.shift i) ⟶
        lt zero (inst3 radixBody (var 0) (Syn.shift p) (Syn.shift q)))) :
    Γ ⊢[PRAAx] lt zero (radixPrefix radixBody i p q) := by
  -- Quantifier-free induction on `i`, using `prefix_zero`, `prefix_succ`, and
  -- positivity of a product of positive naturals.
  sorry

/-- A decoded digit is below its positive current radix. -/
theorem digitAt_lt (code radixBody : PTm 3) {i p q : PTm n}
    (hprefix : Γ ⊢[PRAAx] lt zero (radixPrefix radixBody i p q))
    (hradix : Γ ⊢[PRAAx] lt zero (inst3 radixBody i p q)) :
    Γ ⊢[PRAAx] lt (digitAt code radixBody i p q) (inst3 radixBody i p q) := by
  -- Express both positive divisors as successors, expand `digitAt`, and take
  -- the remainder bound from `div_mod`.
  sorry

/-- One-step decoding lemma.  It is the algebraic core of the table proof. -/
theorem digit_of_append {code d P B : PTm n}
    (hP : Γ ⊢[PRAAx] lt zero P)
    (hB : Γ ⊢[PRAAx] lt zero B)
    (hcode : Γ ⊢[PRAAx] lt code P)
    (hd : Γ ⊢[PRAAx] lt d B) :
    Γ ⊢[PRAAx] rem (quo (code + d * P) P) B ≐ d := by
  -- Use `div_mod_unique` for divisor P to prove quotient d and remainder
  -- code; then use `div_mod_unique` for divisor B on d = B*0+d.
  sorry

/-- A bounded mixed-radix table has code below the next prefix product. -/
theorem pack_lt_prefix (digitBody radixBody : PTm 3) {N p q : PTm n}
    (hradices : Γ ⊢[PRAAx] Fm.all
      (lt (var 0) (Syn.shift N) ⟶
        lt zero (inst3 radixBody (var 0) (Syn.shift p) (Syn.shift q))))
    (hdigits : Γ ⊢[PRAAx] Fm.all
      (lt (var 0) (Syn.shift N) ⟶
        lt (inst3 digitBody (var 0) (Syn.shift p) (Syn.shift q))
          (inst3 radixBody (var 0) (Syn.shift p) (Syn.shift q)))) :
    Γ ⊢[PRAAx]
      lt (pack digitBody radixBody N p q) (radixPrefix radixBody N p q) := by
  -- Quantifier-free induction on N.  Rewrite with `pack_succ` and
  -- `prefix_succ`; from c<P and d<B derive c+dP<PB.
  sorry

/-- Appending a higher digit leaves each earlier decoded digit unchanged. -/
theorem earlier_digit_append {code d P B Pi Bi : PTm n}
    (hPi : Γ ⊢[PRAAx] lt zero Pi)
    (hBi : Γ ⊢[PRAAx] lt zero Bi)
    (hprefixFactor : Γ ⊢[PRAAx] P ≐ Pi * Bi * B)
    (hcode : Γ ⊢[PRAAx] lt code P) :
    Γ ⊢[PRAAx]
      rem (quo (code + d * P) Pi) Bi ≐ rem (quo code Pi) Bi := by
  -- The appended term is divisible by `Pi*Bi`, so it changes the quotient by
  -- a multiple of Bi and leaves the outer remainder unchanged.
  sorry

/-- Decode every in-range digit of a packed table. -/
theorem digit_pack (digitBody radixBody : PTm 3) {N p q i : PTm n}
    (hi : Γ ⊢[PRAAx] lt i N)
    (hradices : Γ ⊢[PRAAx] Fm.all
      (lt (var 0) (Syn.shift N) ⟶
        lt zero (inst3 radixBody (var 0) (Syn.shift p) (Syn.shift q))))
    (hdigits : Γ ⊢[PRAAx] Fm.all
      (lt (var 0) (Syn.shift N) ⟶
        lt (inst3 digitBody (var 0) (Syn.shift p) (Syn.shift q))
          (inst3 radixBody (var 0) (Syn.shift p) (Syn.shift q)))) :
    Γ ⊢[PRAAx]
      digitAt (pack digitBody radixBody N p q) radixBody i p q ≐
        inst3 digitBody i p q := by
  -- Induct on N.  At the newest index use `digit_of_append`; at earlier
  -- indices use `earlier_digit_append` and the induction hypothesis.
  sorry

/-- Two bounded packed tables with equal digits below N have equal codes. -/
theorem pack_ext (f g radixBody : PTm 3) {N p q : PTm n}
    (hfg : Γ ⊢[PRAAx] Fm.all
      (lt (var 0) (Syn.shift N) ⟶
       (inst3 f (var 0) (Syn.shift p) (Syn.shift q) ≐
        inst3 g (var 0) (Syn.shift p) (Syn.shift q)))) :
    Γ ⊢[PRAAx]
      pack f radixBody N p q ≐ pack g radixBody N p q := by
  -- Apply `sum2_congr_bounded` and congruence under the common prefix factor.
  sorry

end LeanProofs.IPRA.STRIVE
