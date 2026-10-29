import ZFCinPA.ConstructibleInterpretation
import BoundedPAConsistency.InternalRelativizationBound
import BoundedPAConsistency.ShiftBound

/-!
# Choice transport with an explicit proof-size bound, up to the schemata

The constructible interpretation of `𝗭𝗙𝗖` in `𝗭𝗙`, run through the bounded
relativization engine (`InternalRelativizationBound`). In every model of `𝗜𝚺₁`:
if every internal separation or replacement axiom code `p` has a `𝗭𝗙`-derivation
of its relativization to `L` with code at most `2^(2^(2^(aL·(p+1))))` (and at
most `p + aL` side formulas), then a `𝗭𝗙𝗖`-refutation with code `n` yields a
`𝗭𝗙`-refutation with code at most `provB aL n`
(`provableLe_falsum_ZF_of_ZFC`).

Everything else the engine needs is discharged here, at one standard numeral
`aL`:

* the finitely many standard obligations (equality axioms, the seven fixed
  axioms, `𝗔𝗖`) and `𝗭𝗙 ⊢ ∃x (x ∈ L)` are fixed meta-level proofs; quoted by
  D1, their internal codes are the numerals `⌜b⌝`, bounded by `aL`;
* `⌜domL⌝`, its negation, and the side formulas at `&0` are numerals
  (Σ₁ absoluteness of `neg` and `substs1`), and `ShiftBound` grows the side
  formulas `¬δ(&i)` and `δ(&i)` double exponentially from there.

`aL` is a fixed natural number defined from these codes; it is not evaluated.
The schema obligations (`LSepBase.sep_obligation`, `LReplBase.repl_obligation`)
are the remaining, unbounded input.
-/
set_option autoImplicit false
noncomputable section

namespace LeanProofs.ZFCinPA.ConstructibleInterpretationBound

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory
open scoped LO.FirstOrder.Arithmetic
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.ConstructibleInterpretation
open LeanProofs.BoundedPAConsistency.InternalRelativization
open LeanProofs.BoundedPAConsistency.SizedDerivation
open LeanProofs.BoundedPAConsistency.InternalRelativizationBound
open LeanProofs.BoundedPAConsistency.ShiftBound

/-! ## The standard constants -/

/-- The finite, standard part of `𝗭𝗙𝗖`. -/
abbrev stdAx : SetTheory := 𝗘𝗤 ℒₛₑₜ ∪ zfFixed ∪ 𝗔𝗖

theorem stdAx_finite : Set.Finite stdAx := by
  refine Set.Finite.union (Set.Finite.union Theory.EqAxiom.finite ?_) ?_
  · simp [zfFixed]
  · simp [AxiomOfChoice]

open Classical in
/-- The code of the fixed meta-level `𝗭𝗙`-proof of `σ^L`. -/
def stdCode (σ : SetTheorySentence) : ℕ :=
  if h : σ ∈ stdAx then (⌜(zf_proves_relL σ h).get⌝ : ℕ) else 0

/-- A bound for all standard obligation codes. -/
def stdN : ℕ := Classical.choose (stdAx_finite.image stdCode).bddAbove

theorem stdCode_le {σ : SetTheorySentence} (h : σ ∈ stdAx) : stdCode σ ≤ stdN :=
  Classical.choose_spec (stdAx_finite.image stdCode).bddAbove ⟨σ, h, rfl⟩

/-- The code of the fixed meta-level proof of `𝗭𝗙 ⊢ ∃x (x ∈ L)`. -/
def neN : ℕ := (⌜zf_proves_exists_L.get⌝ : ℕ)

def dN : ℕ := (⌜domL⌝ : ℕ)

def ndN : ℕ := neg ℒₛₑₜ dN

def s0N : ℕ := substs1 ℒₛₑₜ (^&0) dN

def f0N : ℕ := neg ℒₛₑₜ s0N

/-- **The interpretation parameter** (a standard numeral). -/
def aN : ℕ := stdN + neN + dN + ndN + s0N + f0N + 1

/-! ## The constants inside a model -/

section Internal

variable {W : Type} [ORingStructure W] [W↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The interpretation parameter in `W`. -/
def aL : W := (aN : W)

theorem cast_le_aL {x : ℕ} (hx : x ≤ aN) : (x : W) ≤ aL := Nat.mono_cast hx

theorem one_le_aL : (1 : W) ≤ aL := by
  have := cast_le_aL (W := W) (x := 1) (by unfold aN; omega)
  simpa using this

theorem d_cast : (⌜domL⌝ : W) = (dN : W) := (Sentence.coe_quote_eq_quote domL).symm

theorem neg_cast (x : ℕ) : neg ℒₛₑₜ (x : W) = ((neg ℒₛₑₜ x : ℕ) : W) := by
  have h := LO.FirstOrder.Arithmetic.DefinedFunction.shigmaOne_absolute_func W
    (neg.defined (V := ℕ) (L := ℒₛₑₜ)) (neg.defined (V := W) (L := ℒₛₑₜ)) ![x]
  simpa [Function.comp_def] using h.symm

theorem fvar_cast (x : ℕ) : ((^&x : ℕ) : W) = ^&(x : W) := by
  simp [qqFvar, nat_cast_pair]

theorem substs1_cast (t x : ℕ) : substs1 ℒₛₑₜ (t : W) (x : W) = ((substs1 ℒₛₑₜ t x : ℕ) : W) := by
  have h := LO.FirstOrder.Arithmetic.DefinedFunction.shigmaOne_absolute_func W
    (substs1.defined (V := ℕ) (L := ℒₛₑₜ)) (substs1.defined (V := W) (L := ℒₛₑₜ)) ![t, x]
  simpa [Function.comp_def] using h.symm

theorem s0_cast : substs1 ℒₛₑₜ (^&0) (⌜domL⌝ : W) = (s0N : W) := by
  have := substs1_cast (W := W) (^&0) dN
  rw [fvar_cast] at this
  simpa [d_cast, s0N] using this

theorem f0_cast : domF ℒₛₑₜ (⌜domL⌝ : W) 0 = (f0N : W) := by
  simp only [domF]
  rw [s0_cast, neg_cast]
  rfl

theorem hda : (⌜domL⌝ : W) ≤ aL := by
  rw [d_cast]
  exact cast_le_aL (by unfold aN; omega)

theorem hna : neg ℒₛₑₜ (⌜domL⌝ : W) ≤ aL := by
  rw [d_cast, neg_cast]
  exact cast_le_aL (by unfold aN ndN; omega)

theorem hdom : ∀ i : W, domF ℒₛₑₜ (⌜domL⌝ : W) i ≤ Exp.exp (Exp.exp (aL * (i + 1))) :=
  domF_le isSemiformula_quote_domL shift_quote_domL one_le_aL (by
    rw [f0_cast]
    exact le_trans (cast_le_aL (by unfold aN; omega)) (self_le_exp_exp _))

theorem hsubd : ∀ i : W, substs1 ℒₛₑₜ ^&i (⌜domL⌝ : W) ≤ Exp.exp (Exp.exp (aL * (i + 1))) :=
  substs1_fvar_le isSemiformula_quote_domL shift_quote_domL one_le_aL (by
    rw [s0_cast]
    exact le_trans (cast_le_aL (by unfold aN; omega)) (self_le_exp_exp _))

theorem aL_le_tower (x : W) : aL ≤ Exp.exp (Exp.exp (Exp.exp (aL * (x + 1)))) :=
  le_trans (le_trans (le_mul_of_one_le_right (Arithmetic.zero_le _) le_add_self) (self_le_exp_exp _))
    (le_exp_self _)

/-- **`𝗭𝗙 ⊢ ∃x (x ∈ L)`, with its code bounded by `2^aL`.** -/
theorem hne : DerivableLe 𝗭𝗙 (insert (^∃ (⌜domL⌝ : W)) (∅ : W)) (Exp.exp aL) := by
  set b := zf_proves_exists_L.get
  have hp : Proof 𝗭𝗙 (⌜b⌝ : W) ⌜(∃⁰ domL : SetTheorySentence)⌝ := proof_of_quote_proof b
  have hq : (⌜(∃⁰ domL : SetTheorySentence)⌝ : W) = ^∃ (⌜domL⌝ : W) := by
    simp [LO.FirstOrder.Sentence.quote_def]
  rw [hq] at hp
  refine ⟨⌜b⌝, ?_, by rw [← singleton_eq_insert]; exact hp⟩
  rw [← coe_quote_proof_eq b]
  exact le_trans (cast_le_aL (x := neN) (by unfold aN; omega)) (le_exp_self _)

/-- **The standard obligations, bounded.** -/
theorem standard_obligationLe {p : W}
    (hp : p ∈ (𝗘𝗤 ℒₛₑₜ : SetTheory).Δ₁Class ∨ p ∈ zfFixed.Δ₁Class ∨
      p ∈ (𝗔𝗖 : SetTheory).Δ₁Class) :
    ∃ m, m ≤ p + aL ∧ DerivableLe 𝗭𝗙 (insert (relativize ℒₛₑₜ (⌜domL⌝ : W) p)
      (domSet ℒₛₑₜ (⌜domL⌝ : W) m)) (Exp.exp (Exp.exp (Exp.exp (aL * (p + 1))))) := by
  obtain ⟨σ, hσ, rfl⟩ := standard_of_mem_class hp
  refine ⟨0, Arithmetic.zero_le _, ?_⟩
  have hempty : domSet ℒₛₑₜ (⌜domL⌝ : W) 0 = ∅ := mem_ext fun y => by simp [mem_domSet_iff]
  rw [hempty, ← quote_relF_sentence]
  set b := (zf_proves_relL σ hσ).get
  have hpf : Proof 𝗭𝗙 (⌜b⌝ : W) ⌜relF domL σ⌝ := proof_of_quote_proof b
  refine ⟨⌜b⌝, ?_, by rw [← singleton_eq_insert]; exact hpf⟩
  rw [← coe_quote_proof_eq b]
  have hcode : (⌜b⌝ : ℕ) = stdCode σ := by
    rw [stdCode, dif_pos hσ]
  have hle : (⌜b⌝ : ℕ) ≤ aN := by
    rw [hcode]
    have := stdCode_le hσ
    unfold aN
    omega
  exact le_trans (cast_le_aL hle) (aL_le_tower _)

/-- **Choice transport with an explicit proof-size bound, up to the schemata.**
In every model of `𝗜𝚺₁`: given bounded schema obligations, a `𝗭𝗙𝗖`-refutation
with code `n` yields a `𝗭𝗙`-refutation with code at most `provB aL n`. -/
theorem provableLe_falsum_ZF_of_ZFC
    (hSchema : ∀ p : W, IsFormula ℒₛₑₜ p →
      p ∈ separationTheory.Δ₁Class ∨ p ∈ replacementTheory.Δ₁Class →
      ∃ m, m ≤ p + aL ∧ DerivableLe 𝗭𝗙 (insert (relativize ℒₛₑₜ (⌜domL⌝ : W) p)
        (domSet ℒₛₑₜ (⌜domL⌝ : W) m)) (Exp.exp (Exp.exp (Exp.exp (aL * (p + 1))))))
    {n : W} (h : Proof 𝗭𝗙𝗖 n (^⊥ : W)) : ProvableLe 𝗭𝗙 (^⊥ : W) (provB aL n) :=
  provableLe_falsum_of_relativize isSemiformula_quote_domL shift_quote_domL
    (fun _ ht => SetRelativization.isTerm_eq_fvar ht) hda hna hdom hsubd
    (fun p hp hmem => by
      rcases mem_ZFC_class hmem with h | h | h | h | h
      · exact standard_obligationLe (Or.inl h)
      · exact standard_obligationLe (Or.inr (Or.inl h))
      · exact standard_obligationLe (Or.inr (Or.inr h))
      · exact hSchema p hp (Or.inl h)
      · exact hSchema p hp (Or.inr h))
    hne h

end Internal

end LeanProofs.ZFCinPA.ConstructibleInterpretationBound
