import DiophantineConsistency.Compact44.CompactSymbolicGraphDigits
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
def ports (β K L H : ℕ) : Fin 4 → ℕ := ![β,K,L,β+H]

/-- Symbolic-instance specialization only; K is an arbitrary natural input,
    and graph positivity, beta, radix and product bounds remain hypotheses. -/
theorem graph_digits_of_symbols (β K L H : ℕ) (v : Fin 12 → V) (N : V)
    (hb : 0<(ports β K L H 0:V)) (hl : (ports β K L H 2:V)<(ports β K L H 0:V))
    (hh : (ports β K L H 3:V)<2*(ports β K L H 0:V))
    (hv : ∀ j,0<v j) (hz : InternalZero (literal (fun j => (ports β K L H j:ℤ))) v)
    (hbeta : (46:V)≤(ports β K L H 0:V)) (hN : 0<N)
    (hq : 1+v 0*(ports β K L H 0:V)=Exp.exp ((67*8807)*N))
    (hJ : v 0=rep (67*8807) N) (hL : L=lowNat) (hH : H=highNat) (hHPJ : 1≤(H:V)*v 0) :
    let q : V := 1+v 0*(ports β K L H 0:V)
    let C : V := q-v 1-v 2
    dig 67 C 0=1 ∧ ∀ k < 8807*N, dig 67 C k≤3 := by
  have hlow : (ports β K L H 2:V)=CompactConcreteIncrement.mask := by
    change (L:V)=CompactConcreteIncrement.mask
    rw [hL]
    rfl
  have hhigh : (H:V)=((Nat.ofDigits (2^67) CompactHighPopulation.highDigits : ℕ):V) := by
    rw [hH]
    rfl
  have hport : (ports β K L H 3:V)=(H:V)+(ports β K L H 0:V) := by
    change ((β+H:ℕ):V)=(H:V)+(β:V)
    rw [Nat.cast_add,add_comm]
  exact CompactSymbolicGraphDigits.graph_digits (ports β K L H) v N (H:V)
    hb hl hh hv hz hbeta hN hq hJ hlow hhigh hport hHPJ

/-- The fixed symbolic natural masks are supplied by construction. -/
theorem graph_digits (β K : ℕ) (v : Fin 12 → V) (N : V)
    (hb : 0<(ports β K lowNat highNat 0:V))
    (hl : (ports β K lowNat highNat 2:V)<(ports β K lowNat highNat 0:V))
    (hh : (ports β K lowNat highNat 3:V)<2*(ports β K lowNat highNat 0:V))
    (hv : ∀ j,0<v j) (hz : InternalZero (literal (fun j => (ports β K lowNat highNat j:ℤ))) v)
    (hbeta : (46:V)≤(ports β K lowNat highNat 0:V)) (hN : 0<N)
    (hq : 1+v 0*(ports β K lowNat highNat 0:V)=Exp.exp ((67*8807)*N))
    (hJ : v 0=rep (67*8807) N) (hHPJ : 1≤(highNat:V)*v 0) :
    let q : V := 1+v 0*(ports β K lowNat highNat 0:V)
    let C : V := q-v 1-v 2
    dig 67 C 0=1 ∧ ∀ k < 8807*N, dig 67 C k≤3 := by
  exact graph_digits_of_symbols β K lowNat highNat v N hb hl hh hv hz hbeta hN hq hJ rfl rfl hHPJ

end CompactSymbolicPorts
#print axioms CompactSymbolicPorts.graph_digits_of_symbols
#print axioms CompactSymbolicPorts.graph_digits
