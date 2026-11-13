import DiophantineConsistency.CompactFixedBeta
import DiophantineConsistency.CompactSymbolicPorts
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactFixedGraphDigits
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticBinaryPopulation ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits
open CompactSymbolicPorts CompactFixedBeta
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- For the explicitly symbolic fixed beta and masks, only graph zero,
    positive variables and radix/repunit constraints remain. K is arbitrary. -/
theorem graph_digits (K : ℕ) (v : Fin 12 → V) (N : V)
    (hv : ∀ j,0<v j)
    (hz : InternalZero (literal (fun j => (ports betaNat K lowNat highNat j:ℤ))) v)
    (hN : 0<N)
    (hq : 1+v 0*(ports betaNat K lowNat highNat 0:V)=Exp.exp ((67*8807)*N))
    (hJ : v 0=rep (67*8807) N) :
    let q : V := 1+v 0*(ports betaNat K lowNat highNat 0:V)
    let C : V := q-v 1-v 2
    dig 67 C 0=1 ∧ ∀ k < 8807*N, dig 67 C k≤3 := by
  obtain ⟨hb',hl',hh',hHPJ'⟩ := CompactFixedBeta.bounds (v 0) (hv 0)
  have hb : 0<(ports betaNat K lowNat highNat 0:V) := by
    change 0<(betaNat:V)
    exact hb'
  have hl : (ports betaNat K lowNat highNat 2:V)<(ports betaNat K lowNat highNat 0:V) := by
    change (lowNat:V)<(betaNat:V)
    exact hl'
  have hh : (ports betaNat K lowNat highNat 3:V)<2*(ports betaNat K lowNat highNat 0:V) := by
    change ((betaNat+highNat:ℕ):V)<2*(betaNat:V)
    rw [Nat.cast_add]
    exact hh'
  have hHPJ : 1≤(highNat:V)*v 0 := hHPJ'
  have h64 : (64:V)=Exp.exp (6:V) := by
    rw [ArithmeticStandardCasts.cast_exp]
    norm_num
  have hbig : (64:V)≤(betaNat:V)+1 := by
    rw [CompactFixedBeta.beta_identity, h64]
    exact exp_monotone_le.mpr (by norm_num)
  have hbeta : (46:V)≤(ports betaNat K lowNat highNat 0:V) := by
    change (46:V)≤(betaNat:V)
    apply le_iff_lt_succ.mpr
    exact lt_of_lt_of_le (by norm_num : (46:V)<64) hbig
  exact CompactSymbolicPorts.graph_digits betaNat K v N hb hl hh hv hz hbeta hN hq hJ hHPJ
end CompactFixedGraphDigits
#print axioms CompactFixedGraphDigits.graph_digits
