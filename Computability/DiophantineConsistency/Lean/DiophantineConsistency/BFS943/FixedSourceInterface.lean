import DiophantineConsistency.BFS943.Trace75NaturalTransport
import DiophantineConsistency.BFS943.Trace75Rank
import DiophantineConsistency.ArithmeticRadixAlignment
import DiophantineConsistency.ArithmeticRepunit
import DiophantineConsistency.ArithmeticBinaryPopulation

/-! # A zero-free entry boundary for the direct-BFS943 word layer

The trace75 word layer (`Trace75BFS*`) reaches the algebra of a 75 zero only
through `Trace75FixedSlots.graph_fixed_slots`,
`Trace75FixedDigits.graph_fixed_digits` and
`Trace75FixedCongruence.graph_fixed_congruence`, and those need exactly four
facts about the coordinates `J = v 0`, `F = v 1`, `α = v 2`, `W = v 5` at the
ports `p`:

* `power`: `W q = 2^R` (`Trace75Factors.X p v = Exp.exp (rankNat p v)`);
* `mask`: `F + α < q`;
* `transport`: `(K0 + W) C = F + h t` for some `t`, with `C = q - F - α`;
* `population`: `q = 2^ℓ` and `3 ℓ + 2 ≤ population R` for some `ℓ`.

Here `h = β J`, `q = h + 1` and `R` is the rank polynomial
`[h (q - F) + α] (q² - 1) + (MC + q MF) J` (`Trace75Rank.rankNat`), all
functions of `p` and `v 0`, `v 1`, `v 2`, `v 5` only. No other coordinate of
`v` enters. `FixedSource p v` packages them; `FixedSourceHalt.source_halts`
proves machine 215 halts from it at the direct-BFS943 ports, and
`FixedSourceOfTrace75.source_of_zero` shows a positive 75 zero gives it.

This module also restates the radix alignment and repunit identification of
`Trace75RadixAlignment`/`Trace75Repunit` from `power` alone (same proofs). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace BFS943FixedSource
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticRadixAlignment ArithmeticRepunit ArithmeticBinaryPopulation
open Trace75Factors Trace75Rank Trace75NaturalTransport
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The four facts the direct-BFS943 word layer consumes. -/
structure FixedSource (p : Fin 4 → ℕ) (v : Fin 10 → V) : Prop where
  power : X p v = Exp.exp (rankNat p v)
  mask : v 1 + v 2 < q p v
  transport : ∃ t : V, ((p 1:V) + v 5) * Cnat p v = v 1 + b p v * t
  population : ∃ ℓ : V, q p v = Exp.exp ℓ ∧ 3 * ℓ + 2 ≤ population (rankNat p v)

theorem radix_alignment (p : Fin 4 → ℕ) (v : Fin 10 → V) (d : V)
    (hv : ∀j,0<v j) (hz : FixedSource p v) (hd : 2≤d)
    (hbeta : (p 0:V)+1=Exp.exp d) :
    ∃ N : V, 0<N ∧ q p v=Exp.exp (d*N) ∧ d*N≤rankNat p v ∧
      v 5=Exp.exp (rankNat p v-d*N) := by
  have hx := hz.power
  have hpred : Exp.exp d-1=(p 0:V) := by rw [←hbeta]; simp
  have he : Exp.exp (rankNat p v)=v 5*((Exp.exp d-1)*v 0+1) := by
    rw [hpred,←hx]
    rfl
  obtain ⟨_,N,hN,hq,hbound,hrest⟩ := factor_alignment d (v 0) (rankNat p v) (v 5) hd (hv 0) he
  have hqdef : q p v=(Exp.exp d-1)*v 0+1 := by rw [hpred]; rfl
  refine ⟨N,hN,?_,hbound,hrest⟩
  rw [hqdef]
  exact hq

theorem repunit (p : Fin 4 → ℕ) (v : Fin 10 → V) (d : V)
    (hv : ∀j,0<v j) (hz : FixedSource p v) (hd : 2≤d)
    (hbeta : (p 0:V)+1=Exp.exp d) :
    ∃ N : V, 0<N ∧ v 0=rep d N ∧ q p v=Exp.exp (d*N) ∧ d*N≤rankNat p v ∧
      v 5=Exp.exp (rankNat p v-d*N) := by
  obtain ⟨N,hN,hq,hbound,hrest⟩ := radix_alignment p v d hv hz hd hbeta
  have hpred : Exp.exp d-1=(p 0:V) := by rw [←hbeta]; simp
  have hidentity : (Exp.exp d-1)*v 0+1=Exp.exp (d*N) := by
    rw [hpred]
    exact hq
  have hj : v 0=rep d N := eq_rep_of_identity (lt_of_lt_of_le (by norm_num : (0:V)<2) hd) hidentity
  exact ⟨N,hN,hj,hq,hbound,hrest⟩

/-- The population field at the repunit length of `repunit`. -/
theorem population_at (p : Fin 4 → ℕ) (v : Fin 10 → V) (d : V)
    (hv : ∀j,0<v j) (hz : FixedSource p v) (hd : 2≤d)
    (hbeta : (p 0:V)+1=Exp.exp d) :
    ∃ N : V, 0<N ∧ v 0=rep d N ∧ 3*(d*N)+2≤population (rankNat p v) := by
  obtain ⟨N,hN,hj,hq,_,_⟩ := repunit p v d hv hz hd hbeta
  obtain ⟨ℓ,hℓ,hpop⟩ := hz.population
  have : ℓ=d*N := exp_inj (hℓ.symm.trans hq)
  subst this
  exact ⟨N,hN,hj,hpop⟩

#print axioms BFS943FixedSource.radix_alignment
#print axioms BFS943FixedSource.repunit
#print axioms BFS943FixedSource.population_at
end BFS943FixedSource
