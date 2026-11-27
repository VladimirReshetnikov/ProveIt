import IPRADerivations.Probability.ProductPower

/-!
# Finite uniqueness supplies coherence (`ipra_coherent_methods_2026-11-15`, `thm:coherence`)

Packet: `foundations/ipra_coherent_methods_2026-11-15`, Section "Coherent finite
presentations", Theorem `thm:coherence`.

A presentation of finite data at each precision (`Refinement`) is given by fixed formulas and
terms in the numerical parameter `x`: a specification `C(x, n, z)` (including validity at
precision `n`), an equivalence `z ≃_{x,n} z'`, restrictions `π_{m,n}(z)` and a producer
`a(x, n)`. The hypotheses (`Refinement.Laws`) are the three displayed implications of the
theorem, as rules derivable at arbitrary terms and hypotheses:

* `C(x, n, a(x, n))`;
* `n ≤ m`, `C(x, m, z)` give `C(x, n, π_{m,n}(z))`;
* `C(x, n, z)`, `C(x, n, z')` give `z ≃_{x,n} z'`.

Then `coherence`: `π_{m,n}(a(x, m)) ≃_{x,n} a(x, n)` for `n ≤ m`, with the closed form
`coherence_closed`. No induction and no choice principle is used: correctness at `m` and
restriction give the specification of the restricted value, and finite uniqueness compares it
with the value produced at `n`.

Instance with every law derived: residues modulo `2^n` (`binaryRes`), where restriction
reduces to the smaller modulus; the restriction law is `rem_rem`:
`(x mod 2^m) mod 2^n = x mod 2^n` for `n ≤ m`. The closed sentence is `binary_coherence`.
-/

namespace LeanProofs.IPRA.Foundations.CoherentPresentations

open_ipra exports
open LeanProofs.IPRA.Probability.ProductPower (rem_shift div_eq')
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-- A presentation of finite data at each precision, with a producer. -/
structure Refinement where
  /-- The specification `C(x, n, z)`; variables `0 = x`, `1 = n`, `2 = z`. -/
  C : Fm PTm 3
  /-- The equivalence `z ≃_{x,n} z'`; variables `0 = x`, `1 = n`, `2 = z`, `3 = z'`. -/
  Eqv : Fm PTm 4
  /-- The restriction `π_{m,n}(z)`; variables `0 = x`, `1 = m`, `2 = n`, `3 = z`. -/
  pi : PTm 4
  /-- The producer `a(x, n)`; variables `0 = x`, `1 = n`. -/
  a : PTm 2

namespace Refinement

variable (P : Refinement)

/-- `C(x, n, z)`. -/
def spec (x n z : PTm k) : Fm PTm k := P.C.subst ![x, n, z]
/-- `z ≃_{x,n} z'`. -/
def eqv (x n z z' : PTm k) : Fm PTm k := P.Eqv.subst ![x, n, z, z']
/-- `π_{m,n}(z)`. -/
def res (x m n z : PTm k) : PTm k := Syn.subst ![x, m, n, z] P.pi
/-- `a(x, n)`. -/
def out (x n : PTm k) : PTm k := Syn.subst ![x, n] P.a

/-- The hypotheses of `thm:coherence`. -/
structure Laws : Prop where
  sat : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {x n : PTm k}, Γ ⊢[PRAAx] P.spec x n (P.out x n)
  restr : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {x n m z : PTm k},
    (Γ ⊢[PRAAx] le n m) → (Γ ⊢[PRAAx] P.spec x m z) → (Γ ⊢[PRAAx] P.spec x n (P.res x m n z))
  uniq : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {x n z z' : PTm k},
    (Γ ⊢[PRAAx] P.spec x n z) → (Γ ⊢[PRAAx] P.spec x n z') → (Γ ⊢[PRAAx] P.eqv x n z z')

end Refinement

open Refinement

/-- `thm:coherence`: the producer is coherent, `π_{m,n}(a(x, m)) ≃_{x,n} a(x, n)` for
`n ≤ m`. -/
theorem coherence {P : Refinement} (L : P.Laws) {x n m : PTm k} (h : Γ ⊢[PRAAx] le n m) :
    Γ ⊢[PRAAx] P.eqv x n (P.res x m n (P.out x m)) (P.out x n) :=
  L.uniq (L.restr h L.sat) L.sat

/-- `thm:coherence` as a closed sentence. Variables: `0 = x`, `1 = n`, `2 = m`. -/
theorem coherence_closed {P : Refinement} (L : P.Laws) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (le (var 1) (var 2) ⟶
        P.eqv (var 0) (var 1) (P.res (var 0) (var 2) (var 1) (P.out (var 0) (var 2)))
          (P.out (var 0) (var 1))) :=
  closeUniv 3 (.impI (coherence L Prf.hyp0))

/-! ## An instance: residues modulo `2^n` -/

theorem two_pos : Γ ⊢[PRAAx] (two : PTm k) ≐ succ (pred two) :=
  pos_of_eq_succ (c := one) (.eqRefl _)

/-- `(x mod 2^m) mod 2^n = x mod 2^n` for `n ≤ m`. -/
theorem rem_rem {x n m : PTm k} (h : Γ ⊢[PRAAx] le n m) :
    Γ ⊢[PRAAx] rem (rem x (pw two m)) (pw two n) ≐ rem x (pw two n) := by
  have factor := (congrPw (.eqRefl _) (eq_add_of_le h)).eqTrans (pw_add two n (monus m n))
  exact Division.rem_rem_of_mul (pw_pos' two_pos n) (pw_pos' two_pos m) factor

/-- Residues modulo `2^n`: `C(x, n, z)` is `z = x mod 2^n`, the equivalence is equality, and
restriction reduces modulo the smaller power. -/
def binaryRes : Refinement where
  C := (var 2 : PTm 3) ≐ rem (var 0) (pw two (var 1))
  Eqv := (var 2 : PTm 4) ≐ var 3
  pi := rem (var 3) (pw two (var 2))
  a := rem (var 0) (pw two (var 1))

theorem binary_spec (x n z : PTm k) : binaryRes.spec x n z = (z ≐ rem x (pw two n)) := by
  simp [Refinement.spec, binaryRes]

theorem binary_eqv (x n z z' : PTm k) : binaryRes.eqv x n z z' = (z ≐ z') := by
  simp [Refinement.eqv, binaryRes]

theorem binary_res (x m n z : PTm k) : binaryRes.res x m n z = rem z (pw two n) := by
  simp [Refinement.res, binaryRes]

theorem binary_out (x n : PTm k) : binaryRes.out x n = rem x (pw two n) := by
  simp [Refinement.out, binaryRes]

/-- The residues modulo `2^n` satisfy the hypotheses of `thm:coherence`. -/
theorem binary_laws : binaryRes.Laws where
  sat := by
    intro k Γ x n
    rw [binary_spec, binary_out]
    exact .eqRefl _
  restr := fun h hz => by
    rw [binary_spec] at hz ⊢
    rw [binary_res]
    exact (congrAp2 remF hz (.eqRefl _)).eqTrans (rem_rem h)
  uniq := fun h₁ h₂ => by
    rw [binary_spec] at h₁ h₂
    rw [binary_eqv]
    exact h₁.eqTrans h₂.eqSymm

/-- Coherence of the binary residues, as a closed sentence with all hypotheses discharged. -/
theorem binary_coherence :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (le (var 1) (var 2) ⟶
        binaryRes.eqv (var 0) (var 1)
          (binaryRes.res (var 0) (var 2) (var 1) (binaryRes.out (var 0) (var 2)))
          (binaryRes.out (var 0) (var 1))) :=
  coherence_closed binary_laws

end LeanProofs.IPRA.Foundations.CoherentPresentations
