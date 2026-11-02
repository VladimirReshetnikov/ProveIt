import DiophantineConsistency.CompactSymbolicGraphDigits
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactSymbolicPorts
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticBinaryPopulation ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def lowNat : ℕ := Nat.ofDigits (2^67) (CompactListMask.digits (2^67) 8807 1063 CompactConcreteMask.support)
def highNat : ℕ := Nat.ofDigits (2^67) CompactHighPopulation.highDigits
def ports (β K : ℕ) : Fin 4 → ℕ := ![β,K,lowNat,β+highNat]

/-- Symbolic-instance specialization only; K is an arbitrary natural input,
    and graph positivity, beta, radix and product bounds remain hypotheses. -/
theorem graph_digits (β K : ℕ) (v : Fin 12 → V) (N : V)
    (hb : 0<(ports β K 0:V)) (hl : (ports β K 2:V)<(ports β K 0:V))
    (hh : (ports β K 3:V)<2*(ports β K 0:V))
    (hv : ∀ j,0<v j) (hz : InternalZero (literal (fun j => (ports β K j:ℤ))) v)
    (hbeta : (46:V)≤(ports β K 0:V)) (hN : 0<N)
    (hq : 1+v 0*(ports β K 0:V)=Exp.exp ((67*8807)*N))
    (hJ : v 0=rep (67*8807) N) (hHPJ : 1≤(highNat:V)*v 0) :
    let q : V := 1+v 0*(ports β K 0:V)
    let C : V := q-v 1-v 2
    dig 67 C 0=1 ∧ ∀ k < 8807*N, dig 67 C k≤3 := by
  have hlow : (ports β K 2:V)=CompactConcreteIncrement.mask := by rfl
  have hhigh : (highNat:V)=((Nat.ofDigits (2^67) CompactHighPopulation.highDigits : ℕ):V) := by rfl
  have hport : (ports β K 3:V)=(highNat:V)+(ports β K 0:V) := by
    change ((β+highNat:ℕ):V)=(highNat:V)+(β:V)
    rw [Nat.cast_add,add_comm]
  exact CompactSymbolicGraphDigits.graph_digits (ports β K) v N (highNat:V)
    hb hl hh hv hz hbeta hN hq hJ hlow hhigh hport hHPJ
end CompactSymbolicPorts
#print axioms CompactSymbolicPorts.graph_digits
