import IPRADerivations.Combinatorics.LucasIdentities

/-!
# Catalan's Fibonacci identity

Packet `combinatorics/fibonacci_lucas_ipra`, equation (3). The parameters
range over arbitrary iPRA terms and the sign is represented by the parity
bit. The difference form uses the canonical witness `N ∸ r` for `r ≤ N`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.FibonacciCatalan

open_ipra
open LeanProofs.IPRA.Combinatorics.Fibonacci

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `F_(a+r)² − F_a F_(a+2r) = (−1)^a F_r²`, with signed
terms moved to the opposite sides of a natural-number equation. -/
theorem catalan_add (a r : PTm n) :
    Γ ⊢[PRAAx]
      fib (a + r) * fib (a + r) + par a * (fib r * fib r) ≐
        fib a * fib ((a + r) + r) + monus one (par a) * (fib r * fib r) := by
  ipra_lc (𝔞(fib (a + r)) + 𝔞(fibS a) * 𝔞(fib r)) * natEq (fib_add_sym (Γ := Γ) a r) -
    𝔞(fib a) * 𝔞(fib r) * natEq (fibS_add (Γ := Γ) a r) - 𝔞(fib a) * natEq (fib_add_sym (Γ := Γ) (a + r) r) -
    𝔞(fib r) ^ 2 * natEq (cassini (Γ := Γ) a) + 𝔞(fib a) * 𝔞(fib r) ^ 2 * natEq (fibS_succ (Γ := Γ) a)

/-- The conventional Catalan formula, with `r ≤ N` in the local context. -/
theorem catalan {N r : PTm n} (bound : Γ ⊢[PRAAx] le r N) :
    Γ ⊢[PRAAx]
      fib N * fib N + par (monus N r) * (fib r * fib r) ≐
        fib (monus N r) * fib (N + r) +
          monus one (par (monus N r)) * (fib r * fib r) := by
  have e : Γ ⊢[PRAAx] monus N r + r ≐ N :=
    (add_comm _ _).eqTrans (eq_add_of_le bound).eqSymm
  have left := congrAdd (congrMul (congrFib e) (congrFib e))
    (.eqRefl (par (monus N r) * (fib r * fib r)))
  have right := congrAdd
    (congrMul (.eqRefl (fib (monus N r)))
      (congrFib (congrAdd e (.eqRefl r))))
    (.eqRefl (monus one (par (monus N r)) * (fib r * fib r)))
  exact left.eqSymm.eqTrans ((catalan_add (monus N r) r).eqTrans right)

abbrev catalanAddFormula : Fm PTm 2 :=
  fib (var 0 + var 1) * fib (var 0 + var 1) + par (var 0) * (fib (var 1) * fib (var 1)) ≐
    fib (var 0) * fib ((var 0 + var 1) + var 1) +
      monus one (par (var 0)) * (fib (var 1) * fib (var 1))

/-- Universally closed additive-parameter form of Catalan's identity. -/
theorem catalan_add_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 catalanAddFormula :=
  closeUniv 2 (catalan_add _ _)

abbrev catalanFormula : Fm PTm 2 :=
  le (var 1) (var 0) ⟶
    (fib (var 0) * fib (var 0) + par (monus (var 0) (var 1)) * (fib (var 1) * fib (var 1)) ≐
      fib (monus (var 0) (var 1)) * fib (var 0 + var 1) +
        monus one (par (monus (var 0) (var 1))) * (fib (var 1) * fib (var 1)))

/-- The packet's `N ≥ r` theorem in the closed ordinary iPRA judgment. -/
theorem catalan_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 catalanFormula :=
  closeUniv 2 (.impI (catalan Prf.hyp0))

#print axioms catalan_add_closed
#print axioms catalan_closed

end LeanProofs.IPRA.Combinatorics.FibonacciCatalan
