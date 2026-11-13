import DiophantineConsistency.Norm38MacroVarsOutput
import DiophantineConsistency.Norm38NamedFormula

/-! Candidate identification of symbolic macro variables with the named evaluator tuple. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroNamedEquality
open ExecutableJones NinePolynomial Norm38MacroLanguage Norm38MacroPrefixGroup01 Norm38MacroVarsBd
  Norm38MacroRankSymbolic

def namedVars {R : Type*} [CommRing R] (a : Fin 9 → R) : RingVars R :=
  let ν := 38
  let seed := SharingSeed38.seed CurrentWindowCarry2011.ports
  let z := indexZ seed 0
  let y := indexY seed 0
  let aa : Fin 10 → R := Fin.cons 1 a
  let b := aa 0 * (y : R) + 1 + aa 1
  let B := b ^ 5
  let q := B ^ codingL4 ν
  let n := q ^ 16
  let e := ∑ k ∈ codingStar ν 4,
    ((z : R) + (pCoefficient seed k : R)) * B ^ (codingLexp ν 4 - codingExpo ν 4 k)
  let l := ∑ i ∈ Finset.range ν, B ^ (5 ^ (i + 1))
  let lam := ∑ i ∈ Finset.range (4 * codingLexp ν 4), B ^ i
  let g := aa 2 + 1
  let θ := B - 2 * (z : R)
  ⟨rankCode (aa 0) (z : R) b e g l n q θ lam, n, b, g,
    32 * b * B ^ (5 ^ ν), aa 3 + 1, aa 4 + 1, aa 5 + 1, aa 6, aa 7 + 1, aa 8 + 1⟩

theorem vars_eq_named {R : Type*} [CommRing R] (a : Fin 9 → R) :
    vars a = namedVars a := by
  have h1 : Fin.cons (α := fun _ : Fin 10 => R) (1 : R) a (1 : Fin 10) = a (0 : Fin 9) := by
    have hi : (0 : Fin 9).succ = (1 : Fin 10) := by decide
    rw [← hi, Fin.cons_succ]
  have h2 : Fin.cons (α := fun _ : Fin 10 => R) (1 : R) a (2 : Fin 10) = a (1 : Fin 9) := by
    have hi : (1 : Fin 9).succ = (2 : Fin 10) := by decide
    rw [← hi, Fin.cons_succ]
  have h3 : Fin.cons (α := fun _ : Fin 10 => R) (1 : R) a (3 : Fin 10) = a (2 : Fin 9) := by
    have hi : (2 : Fin 9).succ = (3 : Fin 10) := by decide
    rw [← hi, Fin.cons_succ]
  have h4 : Fin.cons (α := fun _ : Fin 10 => R) (1 : R) a (4 : Fin 10) = a (3 : Fin 9) := by
    have hi : (3 : Fin 9).succ = (4 : Fin 10) := by decide
    rw [← hi, Fin.cons_succ]
  have h5 : Fin.cons (α := fun _ : Fin 10 => R) (1 : R) a (5 : Fin 10) = a (4 : Fin 9) := by
    have hi : (4 : Fin 9).succ = (5 : Fin 10) := by decide
    rw [← hi, Fin.cons_succ]
  have h6 : Fin.cons (α := fun _ : Fin 10 => R) (1 : R) a (6 : Fin 10) = a (5 : Fin 9) := by
    have hi : (5 : Fin 9).succ = (6 : Fin 10) := by decide
    rw [← hi, Fin.cons_succ]
  have h7 : Fin.cons (α := fun _ : Fin 10 => R) (1 : R) a (7 : Fin 10) = a (6 : Fin 9) := by
    have hi : (6 : Fin 9).succ = (7 : Fin 10) := by decide
    rw [← hi, Fin.cons_succ]
  have h8 : Fin.cons (α := fun _ : Fin 10 => R) (1 : R) a (8 : Fin 10) = a (7 : Fin 9) := by
    have hi : (7 : Fin 9).succ = (8 : Fin 10) := by decide
    rw [← hi, Fin.cons_succ]
  unfold vars namedVars
  rw [d11_rank_symbolic]
  simp only [Fin.cons_zero, h1, h2, h3, h4, h5, h6, h7, h8, one_mul,
    Int.cast_ofNat, Int.cast_one, codingL4, codingLexp, base, Nat.reduceAdd]

#print axioms vars_eq_named
end DiophantineConsistency.Norm38MacroNamedEquality
